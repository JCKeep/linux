// SPDX-License-Identifier: GPL-2.0

// Copyright (C) 2024 Google LLC.

//! Files and file descriptors.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h) and
//! [`include/linux/file.h`](srctree/include/linux/file.h)
#![allow(dead_code)]
use macros::vtable;

use crate::{
    bindings,
    cred::Credential,
    error::{code::*, from_result, Error, Result},
    mm,
    sync::poll::PollTable,
    types::{ARef, AlwaysRefCounted, ForeignOwnable, NotThreadSafe, Opaque},
    uaccess::{UserSlice, UserSliceReader, UserSliceWriter},
};
use core::{marker, mem, pin::Pin, ptr};

/// Flags associated with a [`File`].
pub mod flags {
    /// File is opened in append mode.
    pub const O_APPEND: u32 = bindings::O_APPEND;

    /// Signal-driven I/O is enabled.
    pub const O_ASYNC: u32 = bindings::FASYNC;

    /// Close-on-exec flag is set.
    pub const O_CLOEXEC: u32 = bindings::O_CLOEXEC;

    /// File was created if it didn't already exist.
    pub const O_CREAT: u32 = bindings::O_CREAT;

    /// Direct I/O is enabled for this file.
    pub const O_DIRECT: u32 = bindings::O_DIRECT;

    /// File must be a directory.
    pub const O_DIRECTORY: u32 = bindings::O_DIRECTORY;

    /// Like [`O_SYNC`] except metadata is not synced.
    pub const O_DSYNC: u32 = bindings::O_DSYNC;

    /// Ensure that this file is created with the `open(2)` call.
    pub const O_EXCL: u32 = bindings::O_EXCL;

    /// Large file size enabled (`off64_t` over `off_t`).
    pub const O_LARGEFILE: u32 = bindings::O_LARGEFILE;

    /// Do not update the file last access time.
    pub const O_NOATIME: u32 = bindings::O_NOATIME;

    /// File should not be used as process's controlling terminal.
    pub const O_NOCTTY: u32 = bindings::O_NOCTTY;

    /// If basename of path is a symbolic link, fail open.
    pub const O_NOFOLLOW: u32 = bindings::O_NOFOLLOW;

    /// File is using nonblocking I/O.
    pub const O_NONBLOCK: u32 = bindings::O_NONBLOCK;

    /// File is using nonblocking I/O.
    ///
    /// This is effectively the same flag as [`O_NONBLOCK`] on all architectures
    /// except SPARC64.
    pub const O_NDELAY: u32 = bindings::O_NDELAY;

    /// Used to obtain a path file descriptor.
    pub const O_PATH: u32 = bindings::O_PATH;

    /// Write operations on this file will flush data and metadata.
    pub const O_SYNC: u32 = bindings::O_SYNC;

    /// This file is an unnamed temporary regular file.
    pub const O_TMPFILE: u32 = bindings::O_TMPFILE;

    /// File should be truncated to length 0.
    pub const O_TRUNC: u32 = bindings::O_TRUNC;

    /// Bitmask for access mode flags.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::fs::file;
    /// # fn do_something() {}
    /// # let flags = 0;
    /// if (flags & file::flags::O_ACCMODE) == file::flags::O_RDONLY {
    ///     do_something();
    /// }
    /// ```
    pub const O_ACCMODE: u32 = bindings::O_ACCMODE;

    /// File is read only.
    pub const O_RDONLY: u32 = bindings::O_RDONLY;

    /// File is write only.
    pub const O_WRONLY: u32 = bindings::O_WRONLY;

    /// File can be both read and written.
    pub const O_RDWR: u32 = bindings::O_RDWR;
}

/// Wraps the kernel's `struct file`. Thread safe.
///
/// This represents an open file rather than a file on a filesystem. Processes generally reference
/// open files using file descriptors. However, file descriptors are not the same as files. A file
/// descriptor is just an integer that corresponds to a file, and a single file may be referenced
/// by multiple file descriptors.
///
/// # Refcounting
///
/// Instances of this type are reference-counted. The reference count is incremented by the
/// `fget`/`get_file` functions and decremented by `fput`. The Rust type `ARef<File>` represents a
/// pointer that owns a reference count on the file.
///
/// Whenever a process opens a file descriptor (fd), it stores a pointer to the file in its fd
/// table (`struct files_struct`). This pointer owns a reference count to the file, ensuring the
/// file isn't prematurely deleted while the file descriptor is open. In Rust terminology, the
/// pointers in `struct files_struct` are `ARef<File>` pointers.
///
/// ## Light refcounts
///
/// Whenever a process has an fd to a file, it may use something called a "light refcount" as a
/// performance optimization. Light refcounts are acquired by calling `fdget` and released with
/// `fdput`. The idea behind light refcounts is that if the fd is not closed between the calls to
/// `fdget` and `fdput`, then the refcount cannot hit zero during that time, as the `struct
/// files_struct` holds a reference until the fd is closed. This means that it's safe to access the
/// file even if `fdget` does not increment the refcount.
///
/// The requirement that the fd is not closed during a light refcount applies globally across all
/// threads - not just on the thread using the light refcount. For this reason, light refcounts are
/// only used when the `struct files_struct` is not shared with other threads, since this ensures
/// that other unrelated threads cannot suddenly start using the fd and close it. Therefore,
/// calling `fdget` on a shared `struct files_struct` creates a normal refcount instead of a light
/// refcount.
///
/// Light reference counts must be released with `fdput` before the system call returns to
/// userspace. This means that if you wait until the current system call returns to userspace, then
/// all light refcounts that existed at the time have gone away.
///
/// ### The file position
///
/// Each `struct file` has a position integer, which is protected by the `f_pos_lock` mutex.
/// However, if the `struct file` is not shared, then the kernel may avoid taking the lock as a
/// performance optimization.
///
/// The condition for avoiding the `f_pos_lock` mutex is different from the condition for using
/// `fdget`. With `fdget`, you may avoid incrementing the refcount as long as the current fd table
/// is not shared; it is okay if there are other fd tables that also reference the same `struct
/// file`. However, `fdget_pos` can only avoid taking the `f_pos_lock` if the entire `struct file`
/// is not shared, as different processes with an fd to the same `struct file` share the same
/// position.
///
/// To represent files that are not thread safe due to this optimization, the [`LocalFile`] type is
/// used.
///
/// ## Rust references
///
/// The reference type `&File` is similar to light refcounts:
///
/// * `&File` references don't own a reference count. They can only exist as long as the reference
///   count stays positive, and can only be created when there is some mechanism in place to ensure
///   this.
///
/// * The Rust borrow-checker normally ensures this by enforcing that the `ARef<File>` from which
///   a `&File` is created outlives the `&File`.
///
/// * Using the unsafe [`File::from_raw_file`] means that it is up to the caller to ensure that the
///   `&File` only exists while the reference count is positive.
///
/// * You can think of `fdget` as using an fd to look up an `ARef<File>` in the `struct
///   files_struct` and create an `&File` from it. The "fd cannot be closed" rule is like the Rust
///   rule "the `ARef<File>` must outlive the `&File`".
///
/// # Invariants
///
/// * All instances of this type are refcounted using the `f_count` field.
/// * There must not be any active calls to `fdget_pos` on this file that did not take the
///   `f_pos_lock` mutex.
#[repr(transparent)]
pub struct File {
    inner: Opaque<bindings::file>,
}

// SAFETY: This file is known to not have any active `fdget_pos` calls that did not take the
// `f_pos_lock` mutex, so it is safe to transfer it between threads.
unsafe impl Send for File {}

// SAFETY: This file is known to not have any active `fdget_pos` calls that did not take the
// `f_pos_lock` mutex, so it is safe to access its methods from several threads in parallel.
unsafe impl Sync for File {}

// SAFETY: The type invariants guarantee that `File` is always ref-counted. This implementation
// makes `ARef<File>` own a normal refcount.
unsafe impl AlwaysRefCounted for File {
    #[inline]
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::get_file(self.as_ptr()) };
    }

    #[inline]
    unsafe fn dec_ref(obj: ptr::NonNull<File>) {
        // SAFETY: To call this method, the caller passes us ownership of a normal refcount, so we
        // may drop it. The cast is okay since `File` has the same representation as `struct file`.
        unsafe { bindings::fput(obj.cast().as_ptr()) }
    }
}

/// Wraps the kernel's `struct file`. Not thread safe.
///
/// This type represents a file that is not known to be safe to transfer across thread boundaries.
/// To obtain a thread-safe [`File`], use the [`assume_no_fdget_pos`] conversion.
///
/// See the documentation for [`File`] for more information.
///
/// # Invariants
///
/// * All instances of this type are refcounted using the `f_count` field.
/// * If there is an active call to `fdget_pos` that did not take the `f_pos_lock` mutex, then it
///   must be on the same thread as this file.
///
/// [`assume_no_fdget_pos`]: LocalFile::assume_no_fdget_pos
pub struct LocalFile {
    inner: Opaque<bindings::file>,
}

// SAFETY: The type invariants guarantee that `LocalFile` is always ref-counted. This implementation
// makes `ARef<File>` own a normal refcount.
unsafe impl AlwaysRefCounted for LocalFile {
    #[inline]
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::get_file(self.as_ptr()) };
    }

    #[inline]
    unsafe fn dec_ref(obj: ptr::NonNull<LocalFile>) {
        // SAFETY: To call this method, the caller passes us ownership of a normal refcount, so we
        // may drop it. The cast is okay since `File` has the same representation as `struct file`.
        unsafe { bindings::fput(obj.cast().as_ptr()) }
    }
}

impl LocalFile {
    /// Constructs a new `struct file` wrapper from a file descriptor.
    ///
    /// The file descriptor belongs to the current process, and there might be active local calls
    /// to `fdget_pos` on the same file.
    ///
    /// To obtain an `ARef<File>`, use the [`assume_no_fdget_pos`] function to convert.
    ///
    /// [`assume_no_fdget_pos`]: LocalFile::assume_no_fdget_pos
    #[inline]
    pub fn fget(fd: u32) -> Result<ARef<LocalFile>, BadFdError> {
        // SAFETY: FFI call, there are no requirements on `fd`.
        let ptr = ptr::NonNull::new(unsafe { bindings::fget(fd) }).ok_or(BadFdError)?;

        // SAFETY: `bindings::fget` created a refcount, and we pass ownership of it to the `ARef`.
        //
        // INVARIANT: This file is in the fd table on this thread, so either all `fdget_pos` calls
        // are on this thread, or the file is shared, in which case `fdget_pos` calls took the
        // `f_pos_lock` mutex.
        Ok(unsafe { ARef::from_raw(ptr.cast()) })
    }

    /// Creates a reference to a [`LocalFile`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// * The caller must ensure that `ptr` points at a valid file and that the file's refcount is
    ///   positive for the duration of 'a.
    /// * The caller must ensure that if there is an active call to `fdget_pos` that did not take
    ///   the `f_pos_lock` mutex, then that call is on the current thread.
    #[inline]
    pub unsafe fn from_raw_file<'a>(ptr: *const bindings::file) -> &'a LocalFile {
        // SAFETY: The caller guarantees that the pointer is not dangling and stays valid for the
        // duration of 'a. The cast is okay because `File` is `repr(transparent)`.
        //
        // INVARIANT: The caller guarantees that there are no problematic `fdget_pos` calls.
        unsafe { &*ptr.cast() }
    }

    /// Assume that there are no active `fdget_pos` calls that prevent us from sharing this file.
    ///
    /// This makes it safe to transfer this file to other threads. No checks are performed, and
    /// using it incorrectly may lead to a data race on the file position if the file is shared
    /// with another thread.
    ///
    /// This method is intended to be used together with [`LocalFile::fget`] when the caller knows
    /// statically that there are no `fdget_pos` calls on the current thread. For example, you
    /// might use it when calling `fget` from an ioctl, since ioctls usually do not touch the file
    /// position.
    ///
    /// # Safety
    ///
    /// There must not be any active `fdget_pos` calls on the current thread.
    #[inline]
    pub unsafe fn assume_no_fdget_pos(me: ARef<LocalFile>) -> ARef<File> {
        // INVARIANT: There are no `fdget_pos` calls on the current thread, and by the type
        // invariants, if there is a `fdget_pos` call on another thread, then it took the
        // `f_pos_lock` mutex.
        //
        // SAFETY: `LocalFile` and `File` have the same layout.
        unsafe { ARef::from_raw(ARef::into_raw(me).cast()) }
    }

    /// Returns a raw pointer to the inner C struct.
    #[inline]
    pub fn as_ptr(&self) -> *mut bindings::file {
        self.inner.get()
    }

    /// Returns the credentials of the task that originally opened the file.
    pub fn cred(&self) -> &Credential {
        // SAFETY: It's okay to read the `f_cred` field without synchronization because `f_cred` is
        // never changed after initialization of the file.
        let ptr = unsafe { (*self.as_ptr()).f_cred };

        // SAFETY: The signature of this function ensures that the caller will only access the
        // returned credential while the file is still valid, and the C side ensures that the
        // credential stays valid at least as long as the file.
        unsafe { Credential::from_ptr(ptr) }
    }

    /// Returns the flags associated with the file.
    ///
    /// The flags are a combination of the constants in [`flags`].
    #[inline]
    pub fn flags(&self) -> u32 {
        // This `read_volatile` is intended to correspond to a READ_ONCE call.
        //
        // SAFETY: The file is valid because the shared reference guarantees a nonzero refcount.
        //
        // FIXME(read_once): Replace with `read_once` when available on the Rust side.
        unsafe { core::ptr::addr_of!((*self.as_ptr()).f_flags).read_volatile() }
    }
}

impl File {
    /// Creates a reference to a [`File`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// * The caller must ensure that `ptr` points at a valid file and that the file's refcount is
    ///   positive for the duration of 'a.
    /// * The caller must ensure that if there are active `fdget_pos` calls on this file, then they
    ///   took the `f_pos_lock` mutex.
    #[inline]
    pub unsafe fn from_raw_file<'a>(ptr: *const bindings::file) -> &'a File {
        // SAFETY: The caller guarantees that the pointer is not dangling and stays valid for the
        // duration of 'a. The cast is okay because `File` is `repr(transparent)`.
        //
        // INVARIANT: The caller guarantees that there are no problematic `fdget_pos` calls.
        unsafe { &*ptr.cast() }
    }
}

// Make LocalFile methods available on File.
impl core::ops::Deref for File {
    type Target = LocalFile;
    #[inline]
    fn deref(&self) -> &LocalFile {
        // SAFETY: The caller provides a `&File`, and since it is a reference, it must point at a
        // valid file for the desired duration.
        //
        // By the type invariants, there are no `fdget_pos` calls that did not take the
        // `f_pos_lock` mutex.
        unsafe { LocalFile::from_raw_file(self as *const File as *const bindings::file) }
    }
}

/// A file descriptor reservation.
///
/// This allows the creation of a file descriptor in two steps: first, we reserve a slot for it,
/// then we commit or drop the reservation. The first step may fail (e.g., the current process ran
/// out of available slots), but commit and drop never fail (and are mutually exclusive).
///
/// Dropping the reservation happens in the destructor of this type.
///
/// # Invariants
///
/// The fd stored in this struct must correspond to a reserved file descriptor of the current task.
pub struct FileDescriptorReservation {
    fd: u32,
    /// Prevent values of this type from being moved to a different task.
    ///
    /// The `fd_install` and `put_unused_fd` functions assume that the value of `current` is
    /// unchanged since the call to `get_unused_fd_flags`. By adding this marker to this type, we
    /// prevent it from being moved across task boundaries, which ensures that `current` does not
    /// change while this value exists.
    _not_send: NotThreadSafe,
}

impl FileDescriptorReservation {
    /// Creates a new file descriptor reservation.
    pub fn get_unused_fd_flags(flags: u32) -> Result<Self> {
        // SAFETY: FFI call, there are no safety requirements on `flags`.
        let fd: i32 = unsafe { bindings::get_unused_fd_flags(flags) };
        if fd < 0 {
            return Err(Error::from_errno(fd));
        }
        Ok(Self {
            fd: fd as u32,
            _not_send: NotThreadSafe,
        })
    }

    /// Returns the file descriptor number that was reserved.
    pub fn reserved_fd(&self) -> u32 {
        self.fd
    }

    /// Commits the reservation.
    ///
    /// The previously reserved file descriptor is bound to `file`. This method consumes the
    /// [`FileDescriptorReservation`], so it will not be usable after this call.
    pub fn fd_install(self, file: ARef<File>) {
        // SAFETY: `self.fd` was previously returned by `get_unused_fd_flags`. We have not yet used
        // the fd, so it is still valid, and `current` still refers to the same task, as this type
        // cannot be moved across task boundaries.
        //
        // Furthermore, the file pointer is guaranteed to own a refcount by its type invariants,
        // and we take ownership of that refcount by not running the destructor below.
        // Additionally, the file is known to not have any non-shared `fdget_pos` calls, so even if
        // this process starts using the file position, this will not result in a data race on the
        // file position.
        unsafe { bindings::fd_install(self.fd, file.as_ptr()) };

        // `fd_install` consumes both the file descriptor and the file reference, so we cannot run
        // the destructors.
        core::mem::forget(self);
        core::mem::forget(file);
    }
}

impl Drop for FileDescriptorReservation {
    fn drop(&mut self) {
        // SAFETY: By the type invariants of this type, `self.fd` was previously returned by
        // `get_unused_fd_flags`. We have not yet used the fd, so it is still valid, and `current`
        // still refers to the same task, as this type cannot be moved across task boundaries.
        unsafe { bindings::put_unused_fd(self.fd) };
    }
}

/// Represents the `EBADF` error code.
///
/// Used for methods that can only fail with `EBADF`.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct BadFdError;

impl From<BadFdError> for Error {
    #[inline]
    fn from(_: BadFdError) -> Error {
        EBADF
    }
}

impl core::fmt::Debug for BadFdError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad("EBADF")
    }
}

/// Equivalent to [`std::io::SeekFrom`].
///
/// [`std::io::SeekFrom`]: https://doc.rust-lang.org/std/io/enum.SeekFrom.html
pub enum SeekFrom {
    /// Equivalent to C's `SEEK_SET`.
    Start(u64),

    /// Equivalent to C's `SEEK_END`.
    End(i64),

    /// Equivalent to C's `SEEK_CUR`.
    Current(i64),
}

/// Allows the handling of ioctls defined with the `_IO`, `_IOR`, `_IOW`, and `_IOWR` macros.
///
/// For each macro, there is a handler function that takes the appropriate types as arguments.
pub trait IoctlHandler: Sync {
    /// The type of the first argument to each associated function.
    type Target<'a>;

    /// Handles ioctls defined with the `_IO` macro, that is, with no buffer as argument.
    fn pure(_this: Self::Target<'_>, _file: &File, _cmd: u32, _arg: usize) -> Result<i32> {
        Err(EINVAL)
    }

    /// Handles ioctls defined with the `_IOR` macro, that is, with an output buffer provided as
    /// argument.
    fn read(
        _this: Self::Target<'_>,
        _file: &File,
        _cmd: u32,
        _writer: &mut UserSliceWriter,
    ) -> Result<i32> {
        Err(EINVAL)
    }

    /// Handles ioctls defined with the `_IOW` macro, that is, with an input buffer provided as
    /// argument.
    fn write(
        _this: Self::Target<'_>,
        _file: &File,
        _cmd: u32,
        _reader: &mut UserSliceReader,
    ) -> Result<i32> {
        Err(EINVAL)
    }

    /// Handles ioctls defined with the `_IOWR` macro, that is, with a buffer for both input and
    /// output provided as argument.
    fn read_write(
        _this: Self::Target<'_>,
        _file: &File,
        _cmd: u32,
        _data: UserSlice,
    ) -> Result<i32> {
        Err(EINVAL)
    }
}

/// Represents an ioctl command.
///
/// It can use the components of an ioctl command to dispatch ioctls using
/// [`IoctlCommand::dispatch`].
pub struct IoctlCommand {
    cmd: u32,
    arg: usize,
    user_slice: Option<UserSlice>,
}

impl IoctlCommand {
    /// Constructs a new [`IoctlCommand`].
    fn new(cmd: u32, arg: usize) -> Self {
        let size = (cmd >> bindings::_IOC_SIZESHIFT) & bindings::_IOC_SIZEMASK;

        let user_slice = Some(UserSlice::new(arg as _, size as _));
        Self {
            cmd,
            arg,
            user_slice,
        }
    }

    /// Dispatches the given ioctl to the appropriate handler based on the value of the command. It
    /// also creates a [`UserSlice`], [`UserSliceReader`], or [`UserSliceWriter`]
    /// depending on the direction of the buffer of the command.
    ///
    /// It is meant to be used in implementations of [`Operations::ioctl`] and
    /// [`Operations::compat_ioctl`].
    pub fn dispatch<T: IoctlHandler>(
        &mut self,
        handler: T::Target<'_>,
        file: &File,
    ) -> Result<i32> {
        let dir = (self.cmd >> bindings::_IOC_DIRSHIFT) & bindings::_IOC_DIRMASK;
        if dir == bindings::_IOC_NONE {
            return T::pure(handler, file, self.cmd, self.arg);
        }

        let data = self.user_slice.take().ok_or(EINVAL)?;
        const READ_WRITE: u32 = bindings::_IOC_READ | bindings::_IOC_WRITE;
        match dir {
            bindings::_IOC_WRITE => T::write(handler, file, self.cmd, &mut data.reader()),
            bindings::_IOC_READ => T::read(handler, file, self.cmd, &mut data.writer()),
            READ_WRITE => T::read_write(handler, file, self.cmd, data),
            _ => Err(EINVAL),
        }
    }

    /// Returns the raw 32-bit value of the command and the ptr-sized argument.
    pub fn raw(&self) -> (u32, usize) {
        (self.cmd, self.arg)
    }
}

pub(crate) struct OperationsVtable<A, T>(marker::PhantomData<A>, marker::PhantomData<T>);

impl<A: OpenAdapter<T::OpenData>, T: Operations> OperationsVtable<A, T> {
    /// Called by the VFS when an inode should be opened.
    ///
    /// Calls `T::open` on the returned value of `A::convert`.
    ///
    /// # Safety
    ///
    /// The returned value of `A::convert` must be a valid non-null pointer and
    /// `T:open` must return a valid non-null pointer on an `Ok` result.
    unsafe extern "C" fn open_callback(
        inode: *mut bindings::inode,
        file: *mut bindings::file,
    ) -> core::ffi::c_int {
        from_result(|| {
            // SAFETY: `A::convert` must return a valid non-null pointer that
            // should point to data in the inode or file that lives longer
            // than the following use of `T::open`.
            let arg = unsafe { A::convert(inode, file) };
            // SAFETY: The C contract guarantees that `file` is valid. Additionally,
            // `fileref` never outlives this function, so it is guaranteed to be
            // valid.
            let fileref = unsafe { File::from_raw_file(file) };
            // SAFETY: `arg` was previously returned by `A::convert` and must
            // be a valid non-null pointer.
            let ptr = T::open(unsafe { &*arg }, fileref)?.into_foreign();
            // SAFETY: The C contract guarantees that `private_data` is available
            // for implementers of the file operations (no other C code accesses
            // it), so we know that there are no concurrent threads/CPUs accessing
            // it (it's not visible to any other Rust code).
            unsafe { (*file).private_data = ptr as *mut core::ffi::c_void };
            Ok(0)
        })
    }

    unsafe extern "C" fn read_callback(
        file: *mut bindings::file,
        buf: *mut core::ffi::c_char,
        len: core::ffi::c_size_t,
        offset: *mut bindings::loff_t,
    ) -> core::ffi::c_ssize_t {
        from_result(|| {
            let mut data = UserSlice::new(buf as _, len).writer();
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };
            // No `FMODE_UNSIGNED_OFFSET` support, so `offset` must be in [0, 2^63).
            // See <https://github.com/fishinabarrel/linux-kernel-module-rust/pull/113>.
            let read = T::read(
                f,
                unsafe { File::from_raw_file(file) },
                &mut data,
                unsafe { *offset }.try_into()?,
            )?;
            unsafe { (*offset) += bindings::loff_t::try_from(read).unwrap() };
            Ok(read as _)
        })
    }

    unsafe extern "C" fn write_callback(
        file: *mut bindings::file,
        buf: *const core::ffi::c_char,
        len: core::ffi::c_size_t,
        offset: *mut bindings::loff_t,
    ) -> core::ffi::c_ssize_t {
        from_result(|| {
            let mut data = UserSlice::new(buf as _, len).reader();
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };
            // No `FMODE_UNSIGNED_OFFSET` support, so `offset` must be in [0, 2^63).
            // See <https://github.com/fishinabarrel/linux-kernel-module-rust/pull/113>.
            let written = T::write(
                f,
                unsafe { File::from_raw_file(file) },
                &mut data,
                unsafe { *offset }.try_into()?,
            )?;
            unsafe { (*offset) += bindings::loff_t::try_from(written).unwrap() };
            Ok(written as _)
        })
    }

    unsafe extern "C" fn release_callback(
        _inode: *mut bindings::inode,
        file: *mut bindings::file,
    ) -> core::ffi::c_int {
        let ptr = mem::replace(unsafe { &mut (*file).private_data }, ptr::null_mut());
        T::release(unsafe { T::Data::from_foreign(ptr as _) }, unsafe {
            File::from_raw_file(file)
        });
        0
    }

    unsafe extern "C" fn llseek_callback(
        file: *mut bindings::file,
        offset: bindings::loff_t,
        whence: core::ffi::c_int,
    ) -> bindings::loff_t {
        from_result(|| {
            let off = match whence as u32 {
                bindings::SEEK_SET => SeekFrom::Start(offset.try_into()?),
                bindings::SEEK_CUR => SeekFrom::Current(offset),
                bindings::SEEK_END => SeekFrom::End(offset),
                _ => return Err(EINVAL),
            };
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };
            let off = T::seek(f, unsafe { File::from_raw_file(file) }, off)?;
            Ok(off as bindings::loff_t)
        })
    }

    unsafe extern "C" fn unlocked_ioctl_callback(
        file: *mut bindings::file,
        cmd: core::ffi::c_uint,
        arg: core::ffi::c_ulong,
    ) -> core::ffi::c_long {
        from_result(|| {
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };
            let mut cmd = IoctlCommand::new(cmd as _, arg as _);
            let ret = T::ioctl(f, unsafe { File::from_raw_file(file) }, &mut cmd)?;
            Ok(ret as _)
        })
    }

    unsafe extern "C" fn compat_ioctl_callback(
        file: *mut bindings::file,
        cmd: core::ffi::c_uint,
        arg: core::ffi::c_ulong,
    ) -> core::ffi::c_long {
        from_result(|| {
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };
            let mut cmd = IoctlCommand::new(cmd as _, arg as _);
            let ret = T::compat_ioctl(f, unsafe { File::from_raw_file(file) }, &mut cmd)?;
            Ok(ret as _)
        })
    }

    unsafe extern "C" fn mmap_callback(
        file: *mut bindings::file,
        vma: *mut bindings::vm_area_struct,
    ) -> core::ffi::c_int {
        from_result(|| {
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };

            // SAFETY: The C API guarantees that `vma` is valid for the duration of this call.
            // `area` only lives within this call, so it is guaranteed to be valid.
            let area = unsafe { mm::virt::VmArea::from_raw_mut(vma) };

            // SAFETY: The C API guarantees that `file` is valid for the duration of this call,
            // which is longer than the lifetime of the file reference.
            T::mmap(f, unsafe { File::from_raw_file(file) }, area)?;
            Ok(0)
        })
    }

    unsafe extern "C" fn fsync_callback(
        file: *mut bindings::file,
        start: bindings::loff_t,
        end: bindings::loff_t,
        datasync: core::ffi::c_int,
    ) -> core::ffi::c_int {
        from_result(|| {
            let start = start.try_into()?;
            let end = end.try_into()?;
            let datasync = datasync != 0;
            // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
            // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the
            // `release` callback, which the C API guarantees that will be called only when all
            // references to `file` have been released, so we know it can't be called while this
            // function is running.
            let f = unsafe { T::Data::borrow((*file).private_data) };
            let res = T::fsync(
                f,
                unsafe { File::from_raw_file(file) },
                start,
                end,
                datasync,
            )?;
            Ok(res.try_into().unwrap())
        })
    }

    unsafe extern "C" fn poll_callback(
        file: *mut bindings::file,
        wait: *mut bindings::poll_table_struct,
    ) -> bindings::__poll_t {
        // SAFETY: `private_data` was initialised by `open_callback` with a value returned by
        // `T::Data::into_foreign`. `T::Data::from_foreign` is only called by the `release`
        // callback, which the C API guarantees that will be called only when all references to
        // `file` have been released, so we know it can't be called while this function is running.
        let f = unsafe { T::Data::borrow((*file).private_data) };
        match T::poll(f, unsafe { File::from_raw_file(file) }, unsafe {
            &PollTable::from_ptr(wait)
        }) {
            Ok(v) => v,
            Err(_) => bindings::POLLERR,
        }
    }

    const VTABLE: bindings::file_operations = bindings::file_operations {
        open: Some(Self::open_callback),
        release: Some(Self::release_callback),
        read: if T::HAS_READ {
            Some(Self::read_callback)
        } else {
            None
        },
        write: if T::HAS_WRITE {
            Some(Self::write_callback)
        } else {
            None
        },
        llseek: if T::HAS_SEEK {
            Some(Self::llseek_callback)
        } else {
            None
        },

        check_flags: None,
        compat_ioctl: if T::HAS_COMPAT_IOCTL {
            Some(Self::compat_ioctl_callback)
        } else {
            None
        },
        copy_file_range: None,
        fallocate: None,
        fadvise: None,
        fasync: None,
        flock: None,
        flush: None,
        fsync: if T::HAS_FSYNC {
            Some(Self::fsync_callback)
        } else {
            None
        },
        get_unmapped_area: None,
        iterate_shared: None,
        iopoll: None,
        lock: None,
        mmap: if T::HAS_MMAP {
            Some(Self::mmap_callback)
        } else {
            None
        },
        owner: ptr::null_mut(),
        poll: if T::HAS_POLL {
            Some(Self::poll_callback)
        } else {
            None
        },
        read_iter: None,
        remap_file_range: None,
        setlease: None,
        show_fdinfo: None,
        splice_read: None,
        splice_write: None,
        unlocked_ioctl: if T::HAS_IOCTL {
            Some(Self::unlocked_ioctl_callback)
        } else {
            None
        },
        uring_cmd: None,
        uring_cmd_iopoll: None,
        write_iter: None,
        fop_flags: 0,
        splice_eof: None,
    };

    /// Builds an instance of [`struct file_operations`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that the adapter is compatible with the way the device is registered.
    pub(crate) const unsafe fn build() -> &'static bindings::file_operations {
        &Self::VTABLE
    }
}

/// Trait for extracting file open arguments from kernel data structures.
///
/// This is meant to be implemented by registration managers.
pub trait OpenAdapter<T: Sync> {
    /// Converts untyped data stored in [`struct inode`] and [`struct file`] (when [`struct
    /// file_operations::open`] is called) into the given type. For example, for `miscdev`
    /// devices, a pointer to the registered [`struct miscdev`] is stored in [`struct
    /// file::private_data`].
    ///
    /// # Safety
    ///
    /// This function must be called only when [`struct file_operations::open`] is being called for
    /// a file that was registered by the implementer. The returned pointer must be valid and
    /// not-null.
    unsafe fn convert(_inode: *mut bindings::inode, _file: *mut bindings::file) -> *const T;
}

/// Corresponds to the kernel's `struct file_operations`.
///
/// You implement this trait whenever you would create a `struct file_operations`.
///
/// File descriptors may be used from multiple threads/processes concurrently, so your type must be
/// [`Sync`]. It must also be [`Send`] because [`Operations::release`] will be called from the
/// thread that decrements that associated file's refcount to zero.
#[vtable]
pub trait Operations {
    /// The type of the context data returned by [`Operations::open`] and made available to
    /// other methods.
    type Data: ForeignOwnable + Send + Sync = ();

    /// The type of the context data passed to [`Operations::open`].
    type OpenData: Sync = ();

    /// Creates a new instance of this file.
    ///
    /// Corresponds to the `open` function pointer in `struct file_operations`.
    fn open(context: &Self::OpenData, file: &File) -> Result<Self::Data>;

    /// Cleans up after the last reference to the file goes away.
    ///
    /// Note that context data is moved, so it will be freed automatically unless the
    /// implementation moves it elsewhere.
    ///
    /// Corresponds to the `release` function pointer in `struct file_operations`.
    fn release(_data: Self::Data, _file: &File) {}

    /// Reads data from this file to the caller's buffer.
    ///
    /// Corresponds to the `read` and `read_iter` function pointers in `struct file_operations`.
    fn read(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _writer: &mut UserSliceWriter,
        _offset: u64,
    ) -> Result<usize> {
        Err(EINVAL)
    }

    /// Writes data from the caller's buffer to this file.
    ///
    /// Corresponds to the `write` and `write_iter` function pointers in `struct file_operations`.
    fn write(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _reader: &mut UserSliceReader,
        _offset: u64,
    ) -> Result<usize> {
        Err(EINVAL)
    }

    /// Changes the position of the file.
    ///
    /// Corresponds to the `llseek` function pointer in `struct file_operations`.
    fn seek(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _offset: SeekFrom,
    ) -> Result<u64> {
        Err(EINVAL)
    }

    /// Performs IO control operations that are specific to the file.
    ///
    /// Corresponds to the `unlocked_ioctl` function pointer in `struct file_operations`.
    fn ioctl(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _cmd: &mut IoctlCommand,
    ) -> Result<i32> {
        Err(ENOTTY)
    }

    /// Performs 32-bit IO control operations on that are specific to the file on 64-bit kernels.
    ///
    /// Corresponds to the `compat_ioctl` function pointer in `struct file_operations`.
    fn compat_ioctl(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _cmd: &mut IoctlCommand,
    ) -> Result<i32> {
        Err(ENOTTY)
    }

    /// Syncs pending changes to this file.
    ///
    /// Corresponds to the `fsync` function pointer in `struct file_operations`.
    fn fsync(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _start: u64,
        _end: u64,
        _datasync: bool,
    ) -> Result<u32> {
        Err(EINVAL)
    }

    /// Maps areas of the caller's virtual memory with device/file memory.
    ///
    /// Corresponds to the `mmap` function pointer in `struct file_operations`.
    fn mmap(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _vma: Pin<&mut mm::virt::VmArea>,
    ) -> Result {
        Err(EINVAL)
    }

    /// Checks the state of the file and optionally registers for notification when the state
    /// changes.
    ///
    /// Corresponds to the `poll` function pointer in `struct file_operations`.
    fn poll(
        _data: <Self::Data as ForeignOwnable>::Borrowed<'_>,
        _file: &File,
        _table: &PollTable,
    ) -> Result<u32> {
        Ok(bindings::POLLIN | bindings::POLLOUT | bindings::POLLRDNORM | bindings::POLLWRNORM)
    }
}
