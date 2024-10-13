// SPDX-License-Identifier: GPL-2.0

//! Wait queue
//!
//! C header: [`include/linux/wait.h`](srctree/include/linux/wait.h)

use crate::{prelude::*, stack_pin_init, sync::LockClassKey, task, types::Opaque};

/// Creates a [`Queue`] initialiser with the given name and a newly-created lock class.
///
/// It uses the name if one is given, otherwise it generates one based on the file name and line
/// number.
#[macro_export]
macro_rules! new_waitqueue {
    ($($name:literal)? $(,)?) => {
        $crate::wait::Queue::new(
            $crate::optional_name!($($name)?), $crate::static_lock_class!())
    };
}
pub use new_waitqueue;

/// wait queue flags
pub mod flags {
    /// This flag indicates that the task or work is exclusive in a wait queue.
    pub const WQ_FLAG_EXCLUSIVE: u32 = bindings::WQ_FLAG_EXCLUSIVE;
    /// This flag signifies that a task has been woken up from the wait queue.
    pub const WQ_FLAG_WOKENL: u32 = bindings::WQ_FLAG_WOKEN;
    /// A custom flag that can be used for user-defined purposes.
    pub const WQ_FLAG_CUSTOM: u32 = bindings::WQ_FLAG_CUSTOM;
    /// This flag indicates that the work has been completed or the task
    /// in the wait queue is finished.
    pub const WQ_FLAG_DONE: u32 = bindings::WQ_FLAG_DONE;
    /// This flag assigns priority to a task or work in the queue.
    /// When set, it ensures that tasks with higher priority get processed first
    /// relative to others in the same wait queue.
    pub const WQ_FLAG_PRIORITY: u32 = bindings::WQ_FLAG_PRIORITY;
}

/// A kernel wait queue
///
/// Wraps the kernel's C `wait_queue_head_t`.
#[pin_data]
#[repr(transparent)]
pub struct Queue {
    #[pin]
    wait_queue_head: Opaque<bindings::wait_queue_head_t>,
}

/// kernel wait queue is thread safe
unsafe impl Send for Queue {}
/// kernel wait queue is thread safe
unsafe impl Sync for Queue {}

impl Queue {
    /// create a wait queue
    pub fn new(name: &'static CStr, key: &'static LockClassKey) -> impl PinInit<Self> {
        pin_init!(Self {
            wait_queue_head <- Opaque::ffi_init(|slot| {
                unsafe { bindings::__init_waitqueue_head(slot, name.as_char_ptr(), key.as_ptr()) };
            })
        })
    }

    #[allow(unused_mut)]
    fn __wait_event<Cond>(&self, condition: Cond, state: i32, exclusive: bool) -> Result
    where
        Cond: Fn() -> bool,
    {
        // SAFETY: Just a FFI call
        let interruptible = unsafe { bindings::__wait_is_interruptible(state) };
        let flag = if exclusive {
            flags::WQ_FLAG_EXCLUSIVE
        } else {
            0
        };

        stack_pin_init!(let entry = WaitEntry::new(flag));
        let mut entry: Pin<&mut WaitEntry> = entry;

        loop {
            let ret = self.prepare_to_wait_event(entry.as_mut(), state);

            if condition() {
                break;
            }

            if interruptible && ret.is_err() {
                return ret;
            }

            // SAFETY: Just a FFI call
            unsafe { bindings::schedule() };
        }

        Ok(())
    }

    /// Wait in a queue uninterruptible
    pub fn wait_event<Cond>(&self, condition: Cond)
    where
        Cond: Fn() -> bool,
    {
        // SAFETY: not always safety, see https://lore.kernel.org/rust-for-linux/
        // 20241013.115033.709062352209779601.fujita.tomonori@gmail.com/
        // T/#ma421471ca0ff83b469533f3e8faf9ffc4a489522
        unsafe {
            bindings::might_sleep();
        }

        if condition() {
            return;
        }

        let _ = self.__wait_event(condition, task::TASK_UNINTERRUPTIBLE, false);
    }

    /// Wait in a queue interruptible
    pub fn wait_event_interruptible<Cond>(&self, condition: Cond)
    where
        Cond: Fn() -> bool,
    {
        // SAFETY: not always safety, see https://lore.kernel.org/rust-for-linux/
        // 20241013.115033.709062352209779601.fujita.tomonori@gmail.com/
        // T/#ma421471ca0ff83b469533f3e8faf9ffc4a489522
        unsafe {
            bindings::might_sleep();
        }

        if condition() {
            return;
        }

        let _ = self.__wait_event(condition, task::TASK_INTERRUPTIBLE, false);
    }

    /// Preparation for wait in a queue
    pub fn prepare_to_wait_event(
        &self,
        wait: Pin<&mut WaitEntry>,
        state: core::ffi::c_int,
    ) -> Result {
        // SAFETY: todo
        let ret = unsafe {
            bindings::prepare_to_wait_event(self.wait_queue_head.get(), wait.as_ptr(), state)
        };

        if ret != 0 {
            Err(crate::error::Error::from_errno(ret as i32))
        } else {
            Ok(())
        }
    }

    /// Clean up after waiting in a queue
    pub fn finish_wait(&self, wait: Pin<&mut WaitEntry>) {
        unsafe {
            bindings::finish_wait(self.wait_queue_head.get(), wait.as_ptr());
        }
    }

    /// Wake up threads uninterruptible blocked on a waitqueue.
    ///
    /// # Note
    ///
    /// If where's a exclusive wait entry in wait queue, only wake up first.
    pub fn wake_up(&self) {
        // SAFETY: Just a FFI call
        unsafe {
            let _ = bindings::wake_up(self.wait_queue_head.get());
        }
    }

    /// Wake up threads interruptible blocked on a waitqueue.
    ///
    /// # Note
    ///
    /// If where's a exclusive wait entry in wait queue, only wake up first.
    pub fn wake_up_interruptible(&self) {
        // SAFETY: Just a FFI call
        unsafe {
            let _ = bindings::wake_up_interruptible(self.wait_queue_head.get());
        }
    }
}

/// wrapper wait_queue_entry_t
#[pin_data]
#[repr(transparent)]
pub struct WaitEntry {
    #[pin]
    entry: Opaque<bindings::wait_queue_entry_t>,
}

impl WaitEntry {
    /// create a wait_queue_entry_t
    pub fn new(flags: u32) -> impl PinInit<Self> {
        pin_init!(Self {
            entry <- Opaque::ffi_init(|slot| {
                unsafe { bindings::init_wait_entry(slot, flags as core::ffi::c_int); }
            })
        })
    }

    /// get raw wait_queue_entry_t pointer
    pub fn as_ptr(&self) -> *mut bindings::wait_queue_entry_t {
        self.entry.get()
    }
}
