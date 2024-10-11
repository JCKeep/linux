// SPDX-License-Identifier: GPL-2.0

//! Wait queue
//!
//! C header: [`include/linux/wait.h`](srctree/include/linux/wait.h)

use crate::{prelude::*, types::Opaque};

/// A kernel wait queue
///
/// Wraps the kernel's C `wait_queue_head_t`.
#[pin_data]
#[repr(transparent)]
pub struct Queue {
    #[pin]
    wait_queue_head: Opaque<bindings::wait_queue_head_t>,
}

unsafe impl Send for Queue {}
unsafe impl Sync for Queue {}

impl Queue {
    /// create a wait queue
    pub fn new() -> impl PinInit<Self> {
        pin_init!(Self {
            wait_queue_head <- Opaque::ffi_init(|slot| {
                unsafe { bindings::init_waitqueue_head(slot) };
            })
        })
    }

    /// Wait uninterruptible
    pub fn wait_event<Cond>(&self, condition: Cond)
    where
        Cond: Fn() -> bool,
    {
        // SAFETY: Only a ffi function call
        unsafe { bindings::wait_event(self.wait_queue_head.get(), condition()) };
    }

    /// Wait interruptible
    pub fn wait_event_interruptible<Cond>(&self, condition: Cond)
    where
        Cond: Fn() -> bool,
    {
        // SAFETY: Only a ffi function call
        unsafe { bindings::wait_event_interruptible(self.wait_queue_head.get(), condition()) };
    }

    /// wake up all process in wait queue uninterruptible
    pub fn wake_up(&self) {
        // SAFETY: Only a ffi function call
        let _ = unsafe { bindings::wake_up(self.wait_queue_head.get()) };
    }

    /// wake up all process in wait queue interruptible
    pub fn wake_up_interruptible(&self) {
        // SAFETY: Only a ffi function call
        let _ = unsafe { bindings::wake_up_interruptible(self.wait_queue_head.get()) };
    }
}
