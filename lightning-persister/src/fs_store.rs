//! Objects related to [`FilesystemStore`] live here.
use crate::utils::{check_namespace_key_validity, is_valid_kvstore_str};

use lightning::types::string::PrintableString;
use lightning::util::persist::{KVStoreSync, MigratableKVStore};

use std::collections::HashMap;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock, Weak};

#[cfg(feature = "tokio")]
use core::future::Future;
#[cfg(feature = "tokio")]
use core::pin::Pin;
#[cfg(feature = "tokio")]
use lightning::util::persist::KVStore;

#[cfg(target_os = "windows")]
use {std::ffi::OsStr, std::os::windows::ffi::OsStrExt};

#[cfg(target_os = "windows")]
macro_rules! call {
	($e: expr) => {
		if $e != 0 {
			Ok(())
		} else {
			Err(std::io::Error::last_os_error())
		}
	};
}

#[cfg(target_os = "windows")]
fn path_to_windows_str<T: AsRef<OsStr>>(path: &T) -> Vec<u16> {
	path.as_ref().encode_wide().chain(Some(0)).collect()
}

// The number of times we retry listing keys in `FilesystemStore::list` before we give up reaching
// a consistent view and error out.
const LIST_DIR_CONSISTENCY_RETRIES: usize = 10;

struct FilesystemStoreInner {
	data_dir: PathBuf,
	tmp_file_counter: AtomicUsize,

	// Per-path lock ensuring that writes and removes to the same file don't execute concurrently.
	// The lock also encapsulates the latest operation state and outstanding durability work.
	locks: Mutex<HashMap<PathBuf, Arc<RwLock<FilesystemStoreOperationState>>>>,
}

#[derive(Default)]
struct FilesystemStoreOperationState {
	latest_operation: Option<FilesystemStoreOperationAttempt>,
	latest_applied_version: Option<u64>,
	#[cfg(not(target_os = "windows"))]
	pending_directory_sync_version: Option<u64>,
	#[cfg(target_os = "windows")]
	pending_file_sync: Option<PendingWindowsFileSync>,
}

impl FilesystemStoreOperationState {
	fn has_pending_durability_work(&self) -> bool {
		#[cfg(not(target_os = "windows"))]
		{
			self.pending_directory_sync_version.is_some()
		}
		#[cfg(target_os = "windows")]
		{
			self.pending_file_sync.is_some()
		}
	}
}

#[cfg(target_os = "windows")]
#[derive(Clone)]
struct PendingWindowsFileSync {
	version: u64,
	path: PathBuf,
	remove_after_sync: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FilesystemStoreOperationAttemptStatus {
	Started,
	Applied,
	Failed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FilesystemStoreOperationAttempt {
	version: u64,
	status: FilesystemStoreOperationAttemptStatus,
}

/// The outcome of executing a prepared filesystem store operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FilesystemStoreOperationStatus {
	/// The operation was applied to the filesystem.
	Applied,
	/// A newer operation for the same key was successfully applied, so this operation was skipped.
	Superseded,
}

struct PreparedFilesystemStoreOperation {
	inner: Arc<FilesystemStoreInner>,
	dest_file_path: PathBuf,
	inner_lock_ref: Option<Arc<RwLock<FilesystemStoreOperationState>>>,
	version: u64,
}

impl PreparedFilesystemStoreOperation {
	fn execute<
		F: FnOnce(
			&FilesystemStoreInner,
			&Path,
			&mut FilesystemStoreOperationState,
			u64,
		) -> Result<(), lightning::io::Error>,
	>(
		&mut self, callback: F,
	) -> Result<FilesystemStoreOperationStatus, lightning::io::Error> {
		let inner_lock_ref = self.inner_lock_ref.as_ref().expect("operation lock missing");
		let mut state = inner_lock_ref.write().unwrap();

		// If a previous operation changed the filesystem but failed to make that change durable,
		// finish its durability work first. This either proves that the previous operation was
		// applied or returns an I/O error; it never lets an older operation overwrite a possibly
		// applied newer mutation.
		self.inner.complete_pending_durability(&self.dest_file_path, &mut state)?;

		if let Some(latest_applied_version) = state.latest_applied_version {
			if self.version < latest_applied_version {
				return Ok(FilesystemStoreOperationStatus::Superseded);
			}
			if self.version == latest_applied_version {
				return Ok(FilesystemStoreOperationStatus::Applied);
			}
		}
		if let Some(latest_operation) = state.latest_operation {
			if self.version < latest_operation.version {
				match latest_operation.status {
					FilesystemStoreOperationAttemptStatus::Applied => {
						return Ok(FilesystemStoreOperationStatus::Superseded);
					},
					FilesystemStoreOperationAttemptStatus::Started => {
						// This is defensive: the per-key write lock normally prevents observing a
						// concurrently executing operation. Never expose it as a successful outcome.
						return Err(lightning::io::Error::new(
							lightning::io::ErrorKind::WouldBlock,
							"Filesystem store operation is blocked by a newer operation",
						));
					},
					FilesystemStoreOperationAttemptStatus::Failed => {
						// A failure without pending durability work happened before the filesystem
						// mutation. It is safe for this older operation to apply. The newer token
						// retains its reserved version and may still retry afterwards.
					},
				}
			}
			if self.version == latest_operation.version
				&& latest_operation.status == FilesystemStoreOperationAttemptStatus::Applied
			{
				return Ok(FilesystemStoreOperationStatus::Applied);
			}
		}

		// Claim the version before any I/O. Preparation reserves the version, but execution is what
		// establishes the ordering barrier. A failed operation can retry its same version. A
		// post-mutation failure leaves versioned durability work which is completed before any token
		// may proceed. A pre-mutation failure leaves no such work, so an older operation may safely
		// apply while the newer token retains its reserved version for a later retry.
		let is_latest_operation =
			state.latest_operation.map_or(true, |operation| self.version >= operation.version);
		if is_latest_operation {
			state.latest_operation = Some(FilesystemStoreOperationAttempt {
				version: self.version,
				status: FilesystemStoreOperationAttemptStatus::Started,
			});
		}
		let result = callback(&self.inner, &self.dest_file_path, &mut state, self.version);
		if result.is_ok() {
			state.latest_applied_version = Some(
				state
					.latest_applied_version
					.map_or(self.version, |version| version.max(self.version)),
			);
		}
		if is_latest_operation {
			state.latest_operation.as_mut().unwrap().status = if result.is_ok() {
				FilesystemStoreOperationAttemptStatus::Applied
			} else {
				FilesystemStoreOperationAttemptStatus::Failed
			};
		}
		result.map(|_| FilesystemStoreOperationStatus::Applied)
	}
}

impl Drop for PreparedFilesystemStoreOperation {
	fn drop(&mut self) {
		if let Some(inner_lock_ref) = self.inner_lock_ref.take() {
			self.inner.clean_lock(inner_lock_ref, &self.dest_file_path);
		}
	}
}

/// A prepared filesystem write that reserves its version when it is created.
///
/// The reserved version becomes the highest-started ordering barrier only when [`Self::execute`]
/// is first called. Calling it again after an I/O error retries the same version. Pending
/// durability work from any newer filesystem mutation is completed first. A newer applied or
/// recovered version supersedes this one without changing the file. If a newer attempt failed
/// before mutating the filesystem, this older write is instead executed because it is still safe
/// to apply.
pub struct FilesystemStoreWriteOperation {
	operation: PreparedFilesystemStoreOperation,
	buf: Vec<u8>,
}

impl FilesystemStoreWriteOperation {
	/// Executes this prepared write once.
	pub fn execute(&mut self) -> Result<FilesystemStoreOperationStatus, lightning::io::Error> {
		self.operation.execute(|inner, dest_file_path, state, version| {
			inner.write(dest_file_path, &self.buf, state, version)
		})
	}
}

/// A prepared filesystem remove that reserves its version when it is created.
///
/// The reserved version becomes the highest-started ordering barrier only when [`Self::execute`]
/// is first called. Calling it again after an I/O error retries the same version and the same lazy
/// or durable removal mode selected at preparation. Pending durability work from any newer
/// filesystem mutation is completed first. A newer applied or recovered version supersedes this
/// one without changing the file. If a newer attempt failed before mutating the filesystem, this
/// older remove is instead executed because it is still safe to apply.
pub struct FilesystemStoreRemoveOperation {
	operation: PreparedFilesystemStoreOperation,
	lazy: bool,
}

impl FilesystemStoreRemoveOperation {
	/// Executes this prepared remove once.
	///
	/// A durable operation repeats outstanding durability work on retry even if an earlier attempt
	/// already removed the destination file.
	pub fn execute(&mut self) -> Result<FilesystemStoreOperationStatus, lightning::io::Error> {
		let lazy = self.lazy;
		self.operation.execute(|inner, dest_file_path, state, version| {
			inner.remove(dest_file_path, lazy, state, version)
		})
	}
}

struct CleanupFile(PathBuf);

impl Drop for CleanupFile {
	fn drop(&mut self) {
		fs::remove_file(&self.0).ok();
	}
}

/// A [`KVStore`] and [`KVStoreSync`] implementation that writes to and reads from the file system.
///
/// [`KVStore`]: lightning::util::persist::KVStore
pub struct FilesystemStore {
	inner: Arc<FilesystemStoreInner>,

	// Version counter to ensure that writes are applied in the correct order. It is assumed that read and list
	// operations aren't sensitive to the order of execution.
	next_version: AtomicU64,
}

impl FilesystemStore {
	/// Constructs a new [`FilesystemStore`].
	pub fn new(data_dir: PathBuf) -> Self {
		let locks = Mutex::new(HashMap::new());
		let tmp_file_counter = AtomicUsize::new(0);
		Self {
			inner: Arc::new(FilesystemStoreInner { data_dir, tmp_file_counter, locks }),
			next_version: AtomicU64::new(1),
		}
	}

	/// Returns the data directory.
	pub fn get_data_dir(&self) -> PathBuf {
		self.inner.data_dir.clone()
	}

	fn prepare_operation(&self, dest_file_path: PathBuf) -> PreparedFilesystemStoreOperation {
		// Get a reference to the per-path state before allocating a version. This prevents another
		// operation from completing and removing the state between those two steps.
		let inner_lock_ref = self.inner.get_inner_lock_ref(dest_file_path.clone());
		let version =
			match self.next_version.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |version| {
				version.checked_add(1)
			}) {
				Ok(version) => version,
				Err(_) => {
					self.inner.clean_lock(inner_lock_ref, &dest_file_path);
					panic!("FilesystemStore version counter overflowed");
				},
			};

		PreparedFilesystemStoreOperation {
			inner: Arc::clone(&self.inner),
			dest_file_path,
			inner_lock_ref: Some(inner_lock_ref),
			version,
		}
	}

	/// Prepares a write, reserving its version before returning.
	///
	/// The returned operation can be executed repeatedly to retry transient I/O errors without
	/// allocating a new version. The version becomes the highest-started ordering barrier on the
	/// first call to [`FilesystemStoreWriteOperation::execute`]. The operation must be prepared when
	/// the logical write is issued, rather than when an asynchronous executor first polls it.
	pub fn prepare_write(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str, buf: Vec<u8>,
	) -> Result<FilesystemStoreWriteOperation, lightning::io::Error> {
		let dest_file_path = self.inner.get_checked_dest_file_path(
			primary_namespace,
			secondary_namespace,
			Some(key),
			"write",
		)?;
		Ok(FilesystemStoreWriteOperation { operation: self.prepare_operation(dest_file_path), buf })
	}

	/// Prepares a remove, reserving its version and removal mode before returning.
	///
	/// The returned operation can be executed repeatedly to retry transient I/O errors without
	/// allocating a new version or changing the lazy/durable mode. The version becomes the
	/// highest-started ordering barrier on the first call to
	/// [`FilesystemStoreRemoveOperation::execute`]. The operation must be prepared when the logical
	/// remove is issued, rather than when an asynchronous executor first polls it.
	pub fn prepare_remove(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str, lazy: bool,
	) -> Result<FilesystemStoreRemoveOperation, lightning::io::Error> {
		let dest_file_path = self.inner.get_checked_dest_file_path(
			primary_namespace,
			secondary_namespace,
			Some(key),
			"remove",
		)?;
		Ok(FilesystemStoreRemoveOperation {
			operation: self.prepare_operation(dest_file_path),
			lazy,
		})
	}

	#[cfg(any(all(feature = "tokio", test), fuzzing))]
	/// Returns the size of the async state.
	pub fn state_size(&self) -> usize {
		let outer_lock = self.inner.locks.lock().unwrap();
		outer_lock.len()
	}
}

impl KVStoreSync for FilesystemStore {
	fn read(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str,
	) -> Result<Vec<u8>, lightning::io::Error> {
		let path = self.inner.get_checked_dest_file_path(
			primary_namespace,
			secondary_namespace,
			Some(key),
			"read",
		)?;
		self.inner.read(path)
	}

	fn write(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str, buf: Vec<u8>,
	) -> Result<(), lightning::io::Error> {
		self.prepare_write(primary_namespace, secondary_namespace, key, buf)
			.and_then(|mut operation| operation.execute().map(|_| ()))
	}

	fn remove(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str, lazy: bool,
	) -> Result<(), lightning::io::Error> {
		self.prepare_remove(primary_namespace, secondary_namespace, key, lazy)
			.and_then(|mut operation| operation.execute().map(|_| ()))
	}

	fn list(
		&self, primary_namespace: &str, secondary_namespace: &str,
	) -> Result<Vec<String>, lightning::io::Error> {
		let path = self.inner.get_checked_dest_file_path(
			primary_namespace,
			secondary_namespace,
			None,
			"list",
		)?;
		self.inner.list(path)
	}
}

impl FilesystemStoreInner {
	fn get_inner_lock_ref(&self, path: PathBuf) -> Arc<RwLock<FilesystemStoreOperationState>> {
		let mut outer_lock = self.locks.lock().unwrap();
		Arc::clone(outer_lock.entry(path).or_default())
	}

	fn get_dest_dir_path(
		&self, primary_namespace: &str, secondary_namespace: &str,
	) -> std::io::Result<PathBuf> {
		let mut dest_dir_path = {
			#[cfg(target_os = "windows")]
			{
				let data_dir = self.data_dir.clone();
				fs::create_dir_all(data_dir.clone())?;
				fs::canonicalize(data_dir)?
			}
			#[cfg(not(target_os = "windows"))]
			{
				self.data_dir.clone()
			}
		};

		dest_dir_path.push(primary_namespace);
		if !secondary_namespace.is_empty() {
			dest_dir_path.push(secondary_namespace);
		}

		Ok(dest_dir_path)
	}

	fn get_checked_dest_file_path(
		&self, primary_namespace: &str, secondary_namespace: &str, key: Option<&str>,
		operation: &str,
	) -> lightning::io::Result<PathBuf> {
		check_namespace_key_validity(primary_namespace, secondary_namespace, key, operation)?;

		let mut dest_file_path = self.get_dest_dir_path(primary_namespace, secondary_namespace)?;
		if let Some(key) = key {
			dest_file_path.push(key);
		}

		Ok(dest_file_path)
	}

	fn read(&self, dest_file_path: PathBuf) -> lightning::io::Result<Vec<u8>> {
		let mut buf = Vec::new();

		self.execute_locked_read(dest_file_path.clone(), || {
			let mut f = fs::File::open(dest_file_path)?;
			f.read_to_end(&mut buf)?;
			Ok(())
		})?;

		Ok(buf)
	}

	fn execute_locked_read<F: FnOnce() -> Result<(), lightning::io::Error>>(
		&self, dest_file_path: PathBuf, callback: F,
	) -> Result<(), lightning::io::Error> {
		let inner_lock_ref = self.get_inner_lock_ref(dest_file_path.clone());
		let res = {
			let _guard = inner_lock_ref.read().unwrap();
			callback()
		};
		self.clean_lock(inner_lock_ref, &dest_file_path);
		res
	}

	fn clean_lock(
		&self, inner_lock_ref: Arc<RwLock<FilesystemStoreOperationState>>, dest_file_path: &Path,
	) {
		let inner_lock_weak = Arc::downgrade(&inner_lock_ref);
		// Drop this caller's reference before counting. Otherwise two concurrent cleanups can both
		// observe the other's about-to-be-dropped reference and leave the map entry behind.
		drop(inner_lock_ref);
		let mut outer_lock = self.locks.lock().unwrap();
		let should_remove = match outer_lock.get(dest_file_path) {
			Some(state) => {
				Weak::ptr_eq(&inner_lock_weak, &Arc::downgrade(state))
					&& Arc::strong_count(state) == 1
					&& !state.read().unwrap().has_pending_durability_work()
			},
			None => false,
		};
		if should_remove {
			outer_lock.remove(dest_file_path);
		}
	}

	fn mark_version_applied(state: &mut FilesystemStoreOperationState, version: u64) {
		state.latest_applied_version =
			Some(state.latest_applied_version.map_or(version, |applied| applied.max(version)));
		if let Some(latest_operation) = state.latest_operation.as_mut() {
			if latest_operation.version == version {
				latest_operation.status = FilesystemStoreOperationAttemptStatus::Applied;
			}
		}
	}

	fn complete_pending_durability(
		&self, dest_file_path: &Path, state: &mut FilesystemStoreOperationState,
	) -> lightning::io::Result<()> {
		#[cfg(not(target_os = "windows"))]
		if let Some(version) = state.pending_directory_sync_version {
			let parent_directory = dest_file_path.parent().ok_or_else(|| {
				let msg =
					format!("Could not retrieve parent directory of {}.", dest_file_path.display());
				std::io::Error::new(std::io::ErrorKind::InvalidInput, msg)
			})?;
			let dir_file = fs::OpenOptions::new().read(true).open(parent_directory)?;
			dir_file.sync_all()?;
			state.pending_directory_sync_version = None;
			Self::mark_version_applied(state, version);
		}

		#[cfg(target_os = "windows")]
		if let Some(pending_file_sync) = state.pending_file_sync.clone() {
			let file =
				fs::OpenOptions::new().read(true).write(true).open(&pending_file_sync.path)?;
			file.sync_all()?;
			if pending_file_sync.remove_after_sync {
				// The logical removal is already durable at this point. A leftover trash file is
				// harmless and will also be cleaned during listing.
				fs::remove_file(&pending_file_sync.path).ok();
			}
			state.pending_file_sync = None;
			Self::mark_version_applied(state, pending_file_sync.version);
		}

		Ok(())
	}

	fn write(
		&self, dest_file_path: &Path, buf: &[u8], state: &mut FilesystemStoreOperationState,
		version: u64,
	) -> lightning::io::Result<()> {
		let parent_directory = dest_file_path.parent().ok_or_else(|| {
			let msg =
				format!("Could not retrieve parent directory of {}.", dest_file_path.display());
			std::io::Error::new(std::io::ErrorKind::InvalidInput, msg)
		})?;
		fs::create_dir_all(parent_directory)?;

		// Do a crazy dance with lots of fsync()s to be overly cautious here...
		// We never want to end up in a state where we've lost the old data, or end up using the
		// old data on power loss after we've returned.
		// The way to atomically write a file on Unix platforms is:
		// open(tmpname), write(tmpfile), fsync(tmpfile), close(tmpfile), rename(), fsync(dir)
		let mut tmp_file_path = dest_file_path.to_path_buf();
		let tmp_file_ext = format!("{}.tmp", self.tmp_file_counter.fetch_add(1, Ordering::AcqRel));
		tmp_file_path.set_extension(tmp_file_ext);
		let _cleanup_file = CleanupFile(tmp_file_path.clone());

		{
			let mut tmp_file = fs::File::create(&tmp_file_path)?;
			tmp_file.write_all(buf)?;
			tmp_file.sync_all()?;
		}

		#[cfg(not(target_os = "windows"))]
		{
			fs::rename(&tmp_file_path, dest_file_path)?;
			state.pending_directory_sync_version = Some(version);
			self.complete_pending_durability(dest_file_path, state)
		}

		#[cfg(target_os = "windows")]
		{
			let res = if dest_file_path.exists() {
				call!(unsafe {
					windows_sys::Win32::Storage::FileSystem::ReplaceFileW(
						path_to_windows_str(&dest_file_path).as_ptr(),
						path_to_windows_str(&tmp_file_path).as_ptr(),
						std::ptr::null(),
						windows_sys::Win32::Storage::FileSystem::REPLACEFILE_IGNORE_MERGE_ERRORS,
						std::ptr::null_mut() as *const core::ffi::c_void,
						std::ptr::null_mut() as *const core::ffi::c_void,
					)
				})
			} else {
				call!(unsafe {
					windows_sys::Win32::Storage::FileSystem::MoveFileExW(
						path_to_windows_str(&tmp_file_path).as_ptr(),
						path_to_windows_str(&dest_file_path).as_ptr(),
						windows_sys::Win32::Storage::FileSystem::MOVEFILE_WRITE_THROUGH
							| windows_sys::Win32::Storage::FileSystem::MOVEFILE_REPLACE_EXISTING,
					)
				})
			};

			match res {
				Ok(()) => {
					// We fsync the destination in hopes this will also flush its metadata to disk.
					// Record this stage before opening the file so a failed attempt cannot be
					// mistaken for an applied write merely because the temp path was moved.
					state.pending_file_sync = Some(PendingWindowsFileSync {
						version,
						path: dest_file_path.to_path_buf(),
						remove_after_sync: false,
					});
					self.complete_pending_durability(dest_file_path, state)
				},
				Err(e) => Err(e.into()),
			}
		}
	}

	fn remove(
		&self, dest_file_path: &Path, lazy: bool, state: &mut FilesystemStoreOperationState,
		version: u64,
	) -> lightning::io::Result<()> {
		if lazy {
			if dest_file_path.is_file() {
				fs::remove_file(dest_file_path)?;
			}
			return Ok(());
		}

		#[cfg(not(target_os = "windows"))]
		{
			if dest_file_path.is_file() {
				fs::remove_file(dest_file_path)?;
				state.pending_directory_sync_version = Some(version);
			}
			// `remove_file` corresponds to POSIX `unlink`, whose changes might get cached and
			// lost on crash. Persist it by syncing the parent directory. If the sync fails, the
			// versioned pending action remains for this or any other token to retry.
			self.complete_pending_durability(dest_file_path, state)?;
		}

		#[cfg(target_os = "windows")]
		{
			if dest_file_path.is_file() {
				// Since Windows `DeleteFile` API is not persisted until the last open file handle
				// is dropped, and there seemingly is no reliable way to flush the directory
				// metadata, we here fall back to use a 'recycling bin' model, i.e., first move the
				// file to be deleted to a temporary trash file and remove the latter file
				// afterwards.
				//
				// This should be marginally better, as, according to the documentation,
				// `MoveFileExW` APIs should offer stronger persistence guarantees,
				// at least if `MOVEFILE_WRITE_THROUGH`/`MOVEFILE_REPLACE_EXISTING` is set.
				// However, all this is partially based on assumptions and local experiments, as
				// Windows API is horribly underdocumented.
				let mut trash_file_path = dest_file_path.to_path_buf();
				let trash_file_ext =
					format!("{}.trash", self.tmp_file_counter.fetch_add(1, Ordering::AcqRel));
				trash_file_path.set_extension(trash_file_ext);

				call!(unsafe {
					windows_sys::Win32::Storage::FileSystem::MoveFileExW(
						path_to_windows_str(&dest_file_path).as_ptr(),
						path_to_windows_str(&trash_file_path).as_ptr(),
						windows_sys::Win32::Storage::FileSystem::MOVEFILE_WRITE_THROUGH
							| windows_sys::Win32::Storage::FileSystem::MOVEFILE_REPLACE_EXISTING,
					)
				})?;
				state.pending_file_sync = Some(PendingWindowsFileSync {
					version,
					path: trash_file_path,
					remove_after_sync: true,
				});
				self.complete_pending_durability(dest_file_path, state)?;
			}
		}

		Ok(())
	}

	fn list(&self, prefixed_dest: PathBuf) -> lightning::io::Result<Vec<String>> {
		if !Path::new(&prefixed_dest).exists() {
			return Ok(Vec::new());
		}

		let mut keys;
		let mut retries = LIST_DIR_CONSISTENCY_RETRIES;

		'retry_list: loop {
			keys = Vec::new();
			'skip_entry: for entry in fs::read_dir(&prefixed_dest)? {
				let entry = entry?;
				let p = entry.path();
				if self.dir_entry_is_store_artifact(&p) {
					continue 'skip_entry;
				}

				let res = dir_entry_is_key(&entry);
				match res {
					Ok(true) => {
						let key = get_key_from_dir_entry_path(&p, &prefixed_dest)?;
						keys.push(key);
					},
					Ok(false) => {
						// We didn't error, but the entry is not a valid key (e.g., a directory,
						// or a temp file).
						continue 'skip_entry;
					},
					Err(e) => {
						if e.kind() == lightning::io::ErrorKind::NotFound && retries > 0 {
							// We had found the entry in `read_dir` above, so some race happend.
							// Retry the `read_dir` to get a consistent view.
							retries -= 1;
							continue 'retry_list;
						} else {
							// For all errors or if we exhausted retries, bubble up.
							return Err(e.into());
						}
					},
				}
			}
			break 'retry_list;
		}

		Ok(keys)
	}

	fn dir_entry_is_store_artifact(&self, path: &Path) -> bool {
		match path.extension().and_then(|ext| ext.to_str()) {
			Some("tmp") => true,
			Some("trash") => {
				#[cfg(target_os = "windows")]
				{
					// A remove operation holds its per-key write lock across MoveFileEx and
					// registering the trash path. Taking every state read lock while holding the
					// lock-map mutex closes the window where listing could otherwise delete the
					// live trash file before it is synced. Lock cleanup uses the same order.
					let outer_lock = self.locks.lock().unwrap();
					let is_pending = outer_lock.values().any(|state| {
						state
							.read()
							.unwrap()
							.pending_file_sync
							.as_ref()
							.map_or(false, |pending| pending.path == path)
					});
					if !is_pending {
						fs::remove_file(path).ok();
					}
				}
				true
			},
			_ => false,
		}
	}
}

#[cfg(feature = "tokio")]
impl KVStore for FilesystemStore {
	fn read(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str,
	) -> Pin<Box<dyn Future<Output = Result<Vec<u8>, lightning::io::Error>> + 'static + Send>> {
		let this = Arc::clone(&self.inner);
		let path = match this.get_checked_dest_file_path(
			primary_namespace,
			secondary_namespace,
			Some(key),
			"read",
		) {
			Ok(path) => path,
			Err(e) => return Box::pin(async move { Err(e) }),
		};

		Box::pin(async move {
			tokio::task::spawn_blocking(move || this.read(path)).await.unwrap_or_else(|e| {
				Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, e))
			})
		})
	}

	fn write(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str, buf: Vec<u8>,
	) -> Pin<Box<dyn Future<Output = Result<(), lightning::io::Error>> + 'static + Send>> {
		let mut operation =
			match self.prepare_write(primary_namespace, secondary_namespace, key, buf) {
				Ok(operation) => operation,
				Err(e) => return Box::pin(async move { Err(e) }),
			};

		Box::pin(async move {
			tokio::task::spawn_blocking(move || operation.execute().map(|_| ()))
				.await
				.unwrap_or_else(|e| {
					Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, e))
				})
		})
	}

	fn remove(
		&self, primary_namespace: &str, secondary_namespace: &str, key: &str, lazy: bool,
	) -> Pin<Box<dyn Future<Output = Result<(), lightning::io::Error>> + 'static + Send>> {
		let mut operation =
			match self.prepare_remove(primary_namespace, secondary_namespace, key, lazy) {
				Ok(operation) => operation,
				Err(e) => return Box::pin(async move { Err(e) }),
			};

		Box::pin(async move {
			tokio::task::spawn_blocking(move || operation.execute().map(|_| ()))
				.await
				.unwrap_or_else(|e| {
					Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, e))
				})
		})
	}

	fn list(
		&self, primary_namespace: &str, secondary_namespace: &str,
	) -> Pin<Box<dyn Future<Output = Result<Vec<String>, lightning::io::Error>> + 'static + Send>> {
		let this = Arc::clone(&self.inner);

		let path = match this.get_checked_dest_file_path(
			primary_namespace,
			secondary_namespace,
			None,
			"list",
		) {
			Ok(path) => path,
			Err(e) => return Box::pin(async move { Err(e) }),
		};

		Box::pin(async move {
			tokio::task::spawn_blocking(move || this.list(path)).await.unwrap_or_else(|e| {
				Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, e))
			})
		})
	}
}

fn dir_entry_is_key(dir_entry: &fs::DirEntry) -> Result<bool, lightning::io::Error> {
	let p = dir_entry.path();
	let metadata = dir_entry.metadata()?;

	// We allow the presence of directories in the empty primary namespace and just skip them.
	if metadata.is_dir() {
		return Ok(false);
	}

	// If we otherwise don't find a file at the given path something went wrong.
	if !metadata.is_file() {
		debug_assert!(
			false,
			"Failed to list keys at path {}: file couldn't be accessed.",
			PrintableString(p.to_str().unwrap_or_default())
		);
		let msg = format!(
			"Failed to list keys at path {}: file couldn't be accessed.",
			PrintableString(p.to_str().unwrap_or_default())
		);
		return Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, msg));
	}

	Ok(true)
}

fn get_key_from_dir_entry_path(p: &Path, base_path: &Path) -> Result<String, lightning::io::Error> {
	match p.strip_prefix(&base_path) {
		Ok(stripped_path) => {
			if let Some(relative_path) = stripped_path.to_str() {
				if is_valid_kvstore_str(relative_path) {
					return Ok(relative_path.to_string());
				} else {
					debug_assert!(
						false,
						"Failed to list keys of path {}: file path is not valid key",
						PrintableString(p.to_str().unwrap_or_default())
					);
					let msg = format!(
						"Failed to list keys of path {}: file path is not valid key",
						PrintableString(p.to_str().unwrap_or_default())
					);
					return Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, msg));
				}
			} else {
				debug_assert!(
					false,
					"Failed to list keys of path {}: file path is not valid UTF-8",
					PrintableString(p.to_str().unwrap_or_default())
				);
				let msg = format!(
					"Failed to list keys of path {}: file path is not valid UTF-8",
					PrintableString(p.to_str().unwrap_or_default())
				);
				return Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, msg));
			}
		},
		Err(e) => {
			debug_assert!(
				false,
				"Failed to list keys of path {}: {}",
				PrintableString(p.to_str().unwrap_or_default()),
				e
			);
			let msg = format!(
				"Failed to list keys of path {}: {}",
				PrintableString(p.to_str().unwrap_or_default()),
				e
			);
			return Err(lightning::io::Error::new(lightning::io::ErrorKind::Other, msg));
		},
	}
}

impl MigratableKVStore for FilesystemStore {
	fn list_all_keys(&self) -> Result<Vec<(String, String, String)>, lightning::io::Error> {
		let prefixed_dest = &self.inner.data_dir;
		if !prefixed_dest.exists() {
			return Ok(Vec::new());
		}

		let mut keys = Vec::new();

		'primary_loop: for primary_entry in fs::read_dir(prefixed_dest)? {
			let primary_entry = primary_entry?;
			let primary_path = primary_entry.path();
			if self.inner.dir_entry_is_store_artifact(&primary_path) {
				continue 'primary_loop;
			}

			if dir_entry_is_key(&primary_entry)? {
				let primary_namespace = String::new();
				let secondary_namespace = String::new();
				let key = get_key_from_dir_entry_path(&primary_path, prefixed_dest)?;
				keys.push((primary_namespace, secondary_namespace, key));
				continue 'primary_loop;
			}

			// The primary_entry is actually also a directory.
			'secondary_loop: for secondary_entry in fs::read_dir(&primary_path)? {
				let secondary_entry = secondary_entry?;
				let secondary_path = secondary_entry.path();
				if self.inner.dir_entry_is_store_artifact(&secondary_path) {
					continue 'secondary_loop;
				}

				if dir_entry_is_key(&secondary_entry)? {
					let primary_namespace =
						get_key_from_dir_entry_path(&primary_path, prefixed_dest)?;
					let secondary_namespace = String::new();
					let key = get_key_from_dir_entry_path(&secondary_path, &primary_path)?;
					keys.push((primary_namespace, secondary_namespace, key));
					continue 'secondary_loop;
				}

				// The secondary_entry is actually also a directory.
				for tertiary_entry in fs::read_dir(&secondary_path)? {
					let tertiary_entry = tertiary_entry?;
					let tertiary_path = tertiary_entry.path();
					if self.inner.dir_entry_is_store_artifact(&tertiary_path) {
						continue;
					}

					if dir_entry_is_key(&tertiary_entry)? {
						let primary_namespace =
							get_key_from_dir_entry_path(&primary_path, prefixed_dest)?;
						let secondary_namespace =
							get_key_from_dir_entry_path(&secondary_path, &primary_path)?;
						let key = get_key_from_dir_entry_path(&tertiary_path, &secondary_path)?;
						keys.push((primary_namespace, secondary_namespace, key));
					} else {
						debug_assert!(
							false,
							"Failed to list keys of path {}: only two levels of namespaces are supported",
							PrintableString(tertiary_path.to_str().unwrap_or_default())
						);
						let msg = format!(
							"Failed to list keys of path {}: only two levels of namespaces are supported",
							PrintableString(tertiary_path.to_str().unwrap_or_default())
						);
						return Err(lightning::io::Error::new(
							lightning::io::ErrorKind::Other,
							msg,
						));
					}
				}
			}
		}
		Ok(keys)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::test_utils::{
		do_read_write_remove_list_persist, do_test_data_migration, do_test_store,
	};

	use lightning::chain::chainmonitor::Persist;
	use lightning::chain::ChannelMonitorUpdateStatus;
	use lightning::check_closed_event;
	use lightning::events::ClosureReason;
	use lightning::ln::functional_test_utils::*;
	use lightning::ln::msgs::BaseMessageHandler;
	use lightning::util::persist::read_channel_monitors;
	use lightning::util::test_utils;
	use std::sync::Barrier;

	impl Drop for FilesystemStore {
		fn drop(&mut self) {
			// We test for invalid directory names, so it's OK if directory removal
			// fails.
			match fs::remove_dir_all(&self.inner.data_dir) {
				Err(e) => println!("Failed to remove test persister directory: {}", e),
				_ => {},
			}
		}
	}

	fn new_test_store(test_name: &str) -> FilesystemStore {
		let data_dir = std::env::temp_dir().join(test_name);
		fs::remove_dir_all(&data_dir).ok();
		fs::create_dir_all(&data_dir).unwrap();
		FilesystemStore::new(data_dir)
	}

	fn assert_no_temporary_files(directory: &Path) {
		let temporary_files = fs::read_dir(directory)
			.unwrap()
			.filter_map(Result::ok)
			.map(|entry| entry.path())
			.filter(|path| path.extension().map_or(false, |extension| extension == "tmp"))
			.collect::<Vec<_>>();
		assert!(temporary_files.is_empty(), "unexpected temporary files: {temporary_files:?}");
	}

	#[test]
	fn prepared_operations_preserve_order_and_allow_same_version_retry() {
		let fs_store = new_test_store("test_prepared_operations_preserve_order");
		let parent = fs_store.get_data_dir().join("primary").join("secondary");
		let dest_file_path = parent.join("key");
		fs::create_dir_all(&dest_file_path).unwrap();

		let mut retrying_write =
			fs_store.prepare_write("primary", "secondary", "key", b"older".to_vec()).unwrap();
		assert!(retrying_write.execute().is_err());
		assert_no_temporary_files(&parent);

		fs::remove_dir(&dest_file_path).unwrap();
		assert_eq!(retrying_write.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert_eq!(fs::read(&dest_file_path).unwrap(), b"older");

		let mut older =
			fs_store.prepare_write("primary", "secondary", "other_key", b"older".to_vec()).unwrap();
		let mut newer =
			fs_store.prepare_write("primary", "secondary", "other_key", b"newer".to_vec()).unwrap();
		let other_dest_file_path = parent.join("other_key");
		fs::create_dir(&other_dest_file_path).unwrap();
		assert!(newer.execute().is_err());
		assert_no_temporary_files(&parent);

		// The newer write failed before changing the destination, so the older write can still
		// apply safely. It must actually write the file rather than report a false success.
		fs::remove_dir(&other_dest_file_path).unwrap();
		assert_eq!(older.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert_eq!(fs::read(&other_dest_file_path).unwrap(), b"older");

		assert_eq!(newer.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert_eq!(fs::read(&other_dest_file_path).unwrap(), b"newer");
		assert_eq!(older.execute().unwrap(), FilesystemStoreOperationStatus::Superseded);

		let mut final_write =
			fs_store.prepare_write("primary", "secondary", "key", b"newer".to_vec()).unwrap();
		fs::remove_file(&dest_file_path).unwrap();
		fs::create_dir(&dest_file_path).unwrap();
		assert!(final_write.execute().is_err());
		assert_no_temporary_files(&parent);

		fs::remove_dir(&dest_file_path).unwrap();
		assert_eq!(final_write.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert_eq!(fs::read(&dest_file_path).unwrap(), b"newer");
	}

	#[test]
	fn prepared_operations_execute_in_reverse_invocation_order() {
		let fs_store = new_test_store("test_prepared_operations_reverse_order");
		let dest_file_path = fs_store.get_data_dir().join("primary").join("key");
		let mut older = fs_store.prepare_write("primary", "", "key", b"older".to_vec()).unwrap();
		let mut newer = fs_store.prepare_write("primary", "", "key", b"newer".to_vec()).unwrap();

		assert_eq!(newer.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert_eq!(older.execute().unwrap(), FilesystemStoreOperationStatus::Superseded);
		assert_eq!(fs::read(dest_file_path).unwrap(), b"newer");
		assert_no_temporary_files(&fs_store.get_data_dir().join("primary"));
	}

	#[test]
	fn concurrently_dropped_operations_clean_their_lock_state() {
		let fs_store = new_test_store("test_concurrent_operation_cleanup");
		let first = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let second = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let barrier = Arc::new(Barrier::new(3));

		std::thread::scope(|scope| {
			let first_barrier = Arc::clone(&barrier);
			scope.spawn(move || {
				first_barrier.wait();
				drop(first);
			});
			let second_barrier = Arc::clone(&barrier);
			scope.spawn(move || {
				second_barrier.wait();
				drop(second);
			});
			barrier.wait();
		});

		assert!(fs_store.inner.locks.lock().unwrap().is_empty());
	}

	#[test]
	fn version_overflow_does_not_wrap_or_leak_lock_state() {
		let fs_store = new_test_store("test_prepared_operation_version_overflow");
		fs_store.next_version.store(u64::MAX, Ordering::Relaxed);
		let result = std::panic::catch_unwind(|| {
			fs_store.prepare_remove("primary", "", "key", false).unwrap();
		});

		assert!(result.is_err());
		assert_eq!(fs_store.next_version.load(Ordering::Relaxed), u64::MAX);
		assert!(fs_store.inner.locks.lock().unwrap().is_empty());
	}

	#[cfg(not(target_os = "windows"))]
	#[test]
	fn same_remove_token_retries_pending_directory_sync_after_unlink() {
		let fs_store = new_test_store("test_durable_remove_retries_directory_sync");
		KVStoreSync::write(&fs_store, "primary", "", "key", b"value".to_vec()).unwrap();
		let mut remove = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let dest_file_path = fs_store.get_data_dir().join("primary").join("key");

		fs::remove_file(&dest_file_path).unwrap();
		{
			let mut state = remove.operation.inner_lock_ref.as_ref().unwrap().write().unwrap();
			state.latest_operation = Some(FilesystemStoreOperationAttempt {
				version: remove.operation.version,
				status: FilesystemStoreOperationAttemptStatus::Failed,
			});
			state.pending_directory_sync_version = Some(remove.operation.version);
		}

		assert_eq!(remove.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert!(!remove
			.operation
			.inner_lock_ref
			.as_ref()
			.unwrap()
			.read()
			.unwrap()
			.pending_directory_sync_version
			.is_some());
		drop(remove);
		assert!(fs_store.inner.locks.lock().unwrap().is_empty());
	}

	#[cfg(not(target_os = "windows"))]
	#[test]
	fn older_operation_waits_for_newer_pending_durability() {
		let fs_store = new_test_store("test_older_waits_for_newer_pending_durability");
		KVStoreSync::write(&fs_store, "primary", "", "key", b"initial".to_vec()).unwrap();
		let mut older = fs_store.prepare_write("primary", "", "key", b"older".to_vec()).unwrap();
		let newer = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let parent = fs_store.get_data_dir().join("primary");
		let unavailable_parent = fs_store.get_data_dir().join("primary-unavailable");
		let dest_file_path = parent.join("key");

		// Model a remove which unlinked the destination and then failed to sync its parent.
		fs::remove_file(&dest_file_path).unwrap();
		{
			let mut state = newer.operation.inner_lock_ref.as_ref().unwrap().write().unwrap();
			state.latest_operation = Some(FilesystemStoreOperationAttempt {
				version: newer.operation.version,
				status: FilesystemStoreOperationAttemptStatus::Failed,
			});
			state.pending_directory_sync_version = Some(newer.operation.version);
		}
		drop(newer);
		assert_eq!(fs_store.inner.locks.lock().unwrap().len(), 1);
		fs::rename(&parent, &unavailable_parent).unwrap();

		// The older write must surface the failed durability retry, not return success while the
		// destination is absent or overwrite the newer mutation.
		assert!(older.execute().is_err());
		assert!(!dest_file_path.exists());

		fs::rename(&unavailable_parent, &parent).unwrap();
		assert_eq!(older.execute().unwrap(), FilesystemStoreOperationStatus::Superseded);
		assert!(!dest_file_path.exists());
	}

	#[cfg(target_os = "windows")]
	#[test]
	fn durable_remove_retries_pending_trash_sync() {
		let fs_store = new_test_store("test_durable_remove_retries_pending_trash_sync");
		let mut remove = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let parent = fs_store.get_data_dir().join("primary");
		fs::create_dir_all(&parent).unwrap();
		let trash_file_path = parent.join("key.0.trash");

		// A directory cannot be opened as the read/write file whose metadata must be synced. This
		// models MoveFileEx succeeding before the trash open or sync fails.
		fs::create_dir(&trash_file_path).unwrap();
		{
			let mut state = remove.operation.inner_lock_ref.as_ref().unwrap().write().unwrap();
			state.latest_operation = Some(FilesystemStoreOperationAttempt {
				version: remove.operation.version,
				status: FilesystemStoreOperationAttemptStatus::Failed,
			});
			state.pending_file_sync = Some(PendingWindowsFileSync {
				version: remove.operation.version,
				path: trash_file_path.clone(),
				remove_after_sync: true,
			});
		}
		assert!(remove.execute().is_err());

		fs::remove_dir(&trash_file_path).unwrap();
		fs::write(&trash_file_path, b"removed data").unwrap();
		assert_eq!(remove.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert!(!trash_file_path.exists());
	}

	#[cfg(target_os = "windows")]
	#[test]
	fn listing_does_not_delete_pending_trash_file() {
		let fs_store = new_test_store("test_listing_preserves_pending_trash");
		let remove = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let parent = fs_store.get_data_dir().join("primary");
		fs::create_dir_all(&parent).unwrap();
		let trash_file_path = parent.join("key.0.trash");
		fs::write(&trash_file_path, b"removed data").unwrap();
		{
			let mut state = remove.operation.inner_lock_ref.as_ref().unwrap().write().unwrap();
			state.pending_file_sync = Some(PendingWindowsFileSync {
				version: remove.operation.version,
				path: trash_file_path.clone(),
				remove_after_sync: true,
			});
		}

		assert!(fs_store.inner.list(parent).unwrap().is_empty());
		assert!(trash_file_path.exists());
		remove.operation.inner_lock_ref.as_ref().unwrap().write().unwrap().pending_file_sync = None;
		assert!(fs_store.inner.list(fs_store.get_data_dir().join("primary")).unwrap().is_empty());
		assert!(!trash_file_path.exists());
	}

	#[cfg(feature = "tokio")]
	#[tokio::test]
	async fn async_write_does_not_report_false_success_after_newer_pre_mutation_failure() {
		let fs_store = Arc::new(new_test_store("test_async_write_after_newer_failure"));
		let async_fs_store: Arc<dyn KVStore> = fs_store.clone();
		let older = async_fs_store.write("primary", "", "key", b"older".to_vec());
		let mut newer = fs_store.prepare_write("primary", "", "key", b"newer".to_vec()).unwrap();
		let parent = fs_store.get_data_dir().join("primary");
		let dest_file_path = parent.join("key");
		fs::create_dir_all(&dest_file_path).unwrap();

		assert!(newer.execute().is_err());
		fs::remove_dir(&dest_file_path).unwrap();
		older.await.unwrap();
		assert_eq!(fs::read(&dest_file_path).unwrap(), b"older");

		assert_eq!(newer.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
		assert_eq!(fs::read(dest_file_path).unwrap(), b"newer");
	}

	#[cfg(all(feature = "tokio", not(target_os = "windows")))]
	#[tokio::test]
	async fn async_write_errors_while_newer_durability_is_pending() {
		let fs_store = Arc::new(new_test_store("test_async_write_while_durability_pending"));
		KVStoreSync::write(&*fs_store, "primary", "", "key", b"initial".to_vec()).unwrap();
		let async_fs_store: Arc<dyn KVStore> = fs_store.clone();
		let older = async_fs_store.write("primary", "", "key", b"older".to_vec());
		let newer = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		let parent = fs_store.get_data_dir().join("primary");
		let unavailable_parent = fs_store.get_data_dir().join("primary-unavailable");
		let dest_file_path = parent.join("key");

		fs::remove_file(&dest_file_path).unwrap();
		{
			let mut state = newer.operation.inner_lock_ref.as_ref().unwrap().write().unwrap();
			state.latest_operation = Some(FilesystemStoreOperationAttempt {
				version: newer.operation.version,
				status: FilesystemStoreOperationAttemptStatus::Failed,
			});
			state.pending_directory_sync_version = Some(newer.operation.version);
		}
		drop(newer);
		fs::rename(&parent, &unavailable_parent).unwrap();

		assert!(older.await.is_err());
		assert!(!dest_file_path.exists());

		fs::rename(&unavailable_parent, &parent).unwrap();
		let mut recovery = fs_store.prepare_remove("primary", "", "key", false).unwrap();
		assert_eq!(recovery.execute().unwrap(), FilesystemStoreOperationStatus::Applied);
	}

	#[test]
	fn read_write_remove_list_persist() {
		let mut temp_path = std::env::temp_dir();
		temp_path.push("test_read_write_remove_list_persist");
		let fs_store = FilesystemStore::new(temp_path);
		do_read_write_remove_list_persist(&fs_store);
	}

	#[cfg(feature = "tokio")]
	#[tokio::test]
	async fn read_write_remove_list_persist_async() {
		use crate::fs_store::FilesystemStore;
		use lightning::util::persist::KVStore;
		use std::sync::Arc;

		let mut temp_path = std::env::temp_dir();
		temp_path.push("test_read_write_remove_list_persist_async");
		let fs_store = Arc::new(FilesystemStore::new(temp_path));
		assert_eq!(fs_store.state_size(), 0);

		let async_fs_store: Arc<dyn KVStore> = fs_store.clone();

		let data1 = vec![42u8; 32];
		let data2 = vec![43u8; 32];

		let primary_namespace = "testspace";
		let secondary_namespace = "testsubspace";
		let key = "testkey";

		// Test writing the same key twice with different data. Execute the asynchronous part out of order to ensure
		// that eventual consistency works.
		let fut1 = async_fs_store.write(primary_namespace, secondary_namespace, key, data1);
		assert_eq!(fs_store.state_size(), 1);

		let fut2 = async_fs_store.remove(primary_namespace, secondary_namespace, key, false);
		assert_eq!(fs_store.state_size(), 1);

		let fut3 = async_fs_store.write(primary_namespace, secondary_namespace, key, data2.clone());
		assert_eq!(fs_store.state_size(), 1);

		fut3.await.unwrap();
		assert_eq!(fs_store.state_size(), 1);

		fut2.await.unwrap();
		assert_eq!(fs_store.state_size(), 1);

		fut1.await.unwrap();
		assert_eq!(fs_store.state_size(), 0);

		// Test list.
		let listed_keys =
			async_fs_store.list(primary_namespace, secondary_namespace).await.unwrap();
		assert_eq!(listed_keys.len(), 1);
		assert_eq!(listed_keys[0], key);

		// Test read. We expect to read data2, as the write call was initiated later.
		let read_data =
			async_fs_store.read(primary_namespace, secondary_namespace, key).await.unwrap();
		assert_eq!(data2, &*read_data);

		// Test remove.
		async_fs_store.remove(primary_namespace, secondary_namespace, key, false).await.unwrap();

		let listed_keys =
			async_fs_store.list(primary_namespace, secondary_namespace).await.unwrap();
		assert_eq!(listed_keys.len(), 0);
	}

	#[test]
	fn list_all_keys_skips_leftover_store_artifacts() {
		let mut temp_path = std::env::temp_dir();
		temp_path.push("test_list_all_keys_skips_leftover_store_artifacts");
		let fs_store = FilesystemStore::new(temp_path.clone());
		KVStoreSync::write(&fs_store, "primary", "secondary", "key", vec![1]).unwrap();

		fs::write(temp_path.join("top_level.0.tmp"), b"stale").unwrap();
		fs::write(temp_path.join("top_level.0.trash"), b"stale").unwrap();

		let primary_path = temp_path.join("primary");
		fs::write(primary_path.join("primary_level.0.tmp"), b"stale").unwrap();
		fs::write(primary_path.join("primary_level.0.trash"), b"stale").unwrap();

		let secondary_path = primary_path.join("secondary");
		fs::write(secondary_path.join("secondary_level.0.tmp"), b"stale").unwrap();
		fs::write(secondary_path.join("secondary_level.0.trash"), b"stale").unwrap();

		let keys = fs_store.list_all_keys().unwrap();
		assert_eq!(keys, vec![("primary".to_string(), "secondary".to_string(), "key".to_string())]);
	}

	#[test]
	fn test_data_migration() {
		let mut source_temp_path = std::env::temp_dir();
		source_temp_path.push("test_data_migration_source");
		let mut source_store = FilesystemStore::new(source_temp_path);

		let mut target_temp_path = std::env::temp_dir();
		target_temp_path.push("test_data_migration_target");
		let mut target_store = FilesystemStore::new(target_temp_path);

		do_test_data_migration(&mut source_store, &mut target_store);
	}

	#[test]
	fn test_if_monitors_is_not_dir() {
		let store = FilesystemStore::new("test_monitors_is_not_dir".into());

		fs::create_dir_all(&store.get_data_dir()).unwrap();
		let mut path = std::path::PathBuf::from(&store.get_data_dir());
		path.push("monitors");
		fs::File::create(path).unwrap();

		let chanmon_cfgs = create_chanmon_cfgs(1);
		let mut node_cfgs = create_node_cfgs(1, &chanmon_cfgs);
		let chain_mon_0 = test_utils::TestChainMonitor::new(
			Some(&chanmon_cfgs[0].chain_source),
			&chanmon_cfgs[0].tx_broadcaster,
			&chanmon_cfgs[0].logger,
			&chanmon_cfgs[0].fee_estimator,
			&store,
			node_cfgs[0].keys_manager,
		);
		node_cfgs[0].chain_monitor = chain_mon_0;
		let node_chanmgrs = create_node_chanmgrs(1, &node_cfgs, &[None]);
		let nodes = create_network(1, &node_cfgs, &node_chanmgrs);

		// Check that read_channel_monitors() returns error if monitors/ is not a
		// directory.
		assert!(
			read_channel_monitors(&store, nodes[0].keys_manager, nodes[0].keys_manager).is_err()
		);
	}

	#[test]
	fn test_filesystem_store() {
		// Create the nodes, giving them FilesystemStores for data stores.
		let store_0 = FilesystemStore::new("test_filesystem_store_0".into());
		let store_1 = FilesystemStore::new("test_filesystem_store_1".into());
		do_test_store(&store_0, &store_1)
	}

	// Test that if the store's path to channel data is read-only, writing a
	// monitor to it results in the store returning an UnrecoverableError.
	// Windows ignores the read-only flag for folders, so this test is Unix-only.
	#[cfg(not(target_os = "windows"))]
	#[test]
	fn test_readonly_dir_perm_failure() {
		let store = FilesystemStore::new("test_readonly_dir_perm_failure".into());
		fs::create_dir_all(&store.get_data_dir()).unwrap();

		// Set up a dummy channel and force close. This will produce a monitor
		// that we can then use to test persistence.
		let chanmon_cfgs = create_chanmon_cfgs(2);
		let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
		let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
		let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

		let node_a_id = nodes[0].node.get_our_node_id();

		let chan = create_announced_chan_between_nodes(&nodes, 0, 1);

		let message = "Channel force-closed".to_owned();
		nodes[1]
			.node
			.force_close_broadcasting_latest_txn(&chan.2, &node_a_id, message.clone())
			.unwrap();
		let reason =
			ClosureReason::HolderForceClosed { broadcasted_latest_txn: Some(true), message };
		check_closed_event!(nodes[1], 1, reason, [node_a_id], 100000);
		let mut added_monitors = nodes[1].chain_monitor.added_monitors.lock().unwrap();

		// Set the store's directory to read-only, which should result in
		// returning an unrecoverable failure when we then attempt to persist a
		// channel update.
		let path = &store.get_data_dir();
		let mut perms = fs::metadata(path).unwrap().permissions();
		perms.set_readonly(true);
		fs::set_permissions(path, perms).unwrap();

		let monitor_name = added_monitors[0].1.persistence_key();
		match store.persist_new_channel(monitor_name, &added_monitors[0].1) {
			ChannelMonitorUpdateStatus::UnrecoverableError => {},
			_ => panic!("unexpected result from persisting new channel"),
		}

		nodes[1].node.get_and_clear_pending_msg_events();
		added_monitors.clear();
	}

	// Test that if a store's directory name is invalid, monitor persistence
	// will fail.
	#[cfg(target_os = "windows")]
	#[test]
	fn test_fail_on_open() {
		// Set up a dummy channel and force close. This will produce a monitor
		// that we can then use to test persistence.
		let chanmon_cfgs = create_chanmon_cfgs(2);
		let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
		let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
		let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

		let node_a_id = nodes[0].node.get_our_node_id();

		let chan = create_announced_chan_between_nodes(&nodes, 0, 1);

		let message = "Channel force-closed".to_owned();
		nodes[1]
			.node
			.force_close_broadcasting_latest_txn(&chan.2, &node_a_id, message.clone())
			.unwrap();
		let reason =
			ClosureReason::HolderForceClosed { broadcasted_latest_txn: Some(true), message };
		check_closed_event!(nodes[1], 1, reason, [node_a_id], 100000);
		let mut added_monitors = nodes[1].chain_monitor.added_monitors.lock().unwrap();
		let update_map = nodes[1].chain_monitor.latest_monitor_update_id.lock().unwrap();
		let update_id = update_map.get(&added_monitors[0].1.channel_id()).unwrap();

		// Create the store with an invalid directory name and test that the
		// channel fails to open because the directories fail to be created. There
		// don't seem to be invalid filename characters on Unix that Rust doesn't
		// handle, hence why the test is Windows-only.
		let store = FilesystemStore::new(":<>/".into());

		let monitor_name = added_monitors[0].1.persistence_key();
		match store.persist_new_channel(monitor_name, &added_monitors[0].1) {
			ChannelMonitorUpdateStatus::UnrecoverableError => {},
			_ => panic!("unexpected result from persisting new channel"),
		}

		nodes[1].node.get_and_clear_pending_msg_events();
		added_monitors.clear();
	}
}

#[cfg(ldk_bench)]
/// Benches
pub mod bench {
	use criterion::Criterion;

	/// Bench!
	pub fn bench_sends(bench: &mut Criterion) {
		let store_a = super::FilesystemStore::new("bench_filesystem_store_a".into());
		let store_b = super::FilesystemStore::new("bench_filesystem_store_b".into());
		lightning::ln::channelmanager::bench::bench_two_sends(
			bench,
			"bench_filesystem_persisted_sends",
			store_a,
			store_b,
		);
	}
}
