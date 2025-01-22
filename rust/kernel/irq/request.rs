// SPDX-License-Identifier: GPL-2.0
// SPDX-FileCopyrightText: Copyright 2025 Collabora ltd.

//! IRQ allocation and handling

use core::marker::PhantomPinned;
use core::ptr::addr_of_mut;

use init::pin_init_from_closure;

use crate::error::to_result;
use crate::prelude::*;
use crate::str::CStr;

/// Flags to be used when registering IRQ handlers.
///
/// They can be combined with the operators `|`, `&`, and `!`.
///
/// Values can be used from the [`flags`] module.
#[derive(Clone, Copy)]
pub struct Flags(u64);

impl core::ops::BitOr for Flags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitAnd for Flags {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl core::ops::Not for Flags {
    type Output = Self;
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

/// The flags that can be used when registering an IRQ handler.
pub mod flags {
    use super::Flags;

    use crate::bindings;

    /// Use the interrupt line as already configured.
    pub const TRIGGER_NONE: Flags = Flags(bindings::IRQF_TRIGGER_NONE as _);

    /// The interrupt is triggered when the signal goes from low to high.
    pub const TRIGGER_RISING: Flags = Flags(bindings::IRQF_TRIGGER_RISING as _);

    /// The interrupt is triggered when the signal goes from high to low.
    pub const TRIGGER_FALLING: Flags = Flags(bindings::IRQF_TRIGGER_FALLING as _);

    /// The interrupt is triggered while the signal is held high.
    pub const TRIGGER_HIGH: Flags = Flags(bindings::IRQF_TRIGGER_HIGH as _);

    /// The interrupt is triggered while the signal is held low.
    pub const TRIGGER_LOW: Flags = Flags(bindings::IRQF_TRIGGER_LOW as _);

    /// Allow sharing the irq among several devices.
    pub const SHARED: Flags = Flags(bindings::IRQF_SHARED as _);

    /// Set by callers when they expect sharing mismatches to occur.
    pub const PROBE_SHARED: Flags = Flags(bindings::IRQF_PROBE_SHARED as _);

    /// Flag to mark this interrupt as timer interrupt.
    pub const TIMER: Flags = Flags(bindings::IRQF_TIMER as _);

    /// Interrupt is per cpu.
    pub const PERCPU: Flags = Flags(bindings::IRQF_PERCPU as _);

    /// Flag to exclude this interrupt from irq balancing.
    pub const NOBALANCING: Flags = Flags(bindings::IRQF_NOBALANCING as _);

    /// Interrupt is used for polling (only the interrupt that is registered
    /// first in a shared interrupt is considered for performance reasons).
    pub const IRQPOLL: Flags = Flags(bindings::IRQF_IRQPOLL as _);

    /// Interrupt is not reenabled after the hardirq handler finished. Used by
    /// threaded interrupts which need to keep the irq line disabled until the
    /// threaded handler has been run.
    pub const ONESHOT: Flags = Flags(bindings::IRQF_ONESHOT as _);

    /// Do not disable this IRQ during suspend. Does not guarantee that this
    /// interrupt will wake the system from a suspended state.
    pub const NO_SUSPEND: Flags = Flags(bindings::IRQF_NO_SUSPEND as _);

    /// Force enable it on resume even if [`NO_SUSPEND`] is set.
    pub const FORCE_RESUME: Flags = Flags(bindings::IRQF_FORCE_RESUME as _);

    /// Interrupt cannot be threaded.
    pub const NO_THREAD: Flags = Flags(bindings::IRQF_NO_THREAD as _);

    /// Resume IRQ early during syscore instead of at device resume time.
    pub const EARLY_RESUME: Flags = Flags(bindings::IRQF_EARLY_RESUME as _);

    /// If the IRQ is shared with a NO_SUSPEND user, execute this interrupt
    /// handler after suspending interrupts. For system wakeup devices users
    /// need to implement wakeup detection in their interrupt handlers.
    pub const COND_SUSPEND: Flags = Flags(bindings::IRQF_COND_SUSPEND as _);

    /// Don't enable IRQ or NMI automatically when users request it. Users will
    /// enable it explicitly by `enable_irq` or `enable_nmi` later.
    pub const NO_AUTOEN: Flags = Flags(bindings::IRQF_NO_AUTOEN as _);

    /// Exclude from runnaway detection for IPI and similar handlers, depends on
    /// `PERCPU`.
    pub const NO_DEBUG: Flags = Flags(bindings::IRQF_NO_DEBUG as _);
}

/// The value that can be returned from an IrqHandler or a ThreadedIrqHandler.
pub enum IrqReturn {
    /// The interrupt was not from this device or was not handled.
    None = bindings::irqreturn_IRQ_NONE as _,

    /// The interrupt was handled by this device.
    Handled = bindings::irqreturn_IRQ_HANDLED as _,
}

/// Callbacks for an IRQ handler.
pub trait Handler: Sync {
    /// The actual handler function. As usual, sleeps are not allowed in IRQ
    /// context.
    fn handle_irq(&self) -> IrqReturn;
}

/// A registration of an IRQ handler for a given IRQ line.
///
/// # Examples
///
/// The following is an example of using `Registration`:
///
/// ```
/// use kernel::prelude::*;
/// use kernel::irq::request::flags;
/// use kernel::irq::request::Registration;
/// use kernel::irq::request::IrqReturn;
/// use kernel::sync::Arc;
/// use kernel::sync::SpinLock;
/// use kernel::c_str;
/// use kernel::alloc::flags::GFP_KERNEL;
///
/// // Declare a struct that will be passed in when the interrupt fires. The u32
/// // merely serves as an example of some internal data.
/// struct Data(SpinLock<u32>);
///
/// // [`handle_irq`] takes &self. This example illustrates interior
/// // mutability can be used when share the data between process context and IRQ
/// // context.
/// //
/// // Ideally, this example would be using a version of SpinLock that is aware
/// // of `spin_lock_irqsave` and `spin_lock_irqrestore`, but that is not yet
/// // implemented.
///
/// type Handler = Data;
///
/// impl kernel::irq::request::Handler for Handler {
///     // This is executing in IRQ context in some CPU. Other CPUs can still
///     // try to access to data.
///     fn handle_irq(&self) -> IrqReturn {
///         // We now have exclusive access to the data by locking the SpinLock.
///         let mut data = self.0.lock();
///         *data += 1;
///
///         IrqReturn::Handled
///     }
/// }
///
/// // This is running in process context.
/// fn register_irq(irq: u32, handler: Handler) -> Result<Arc<Registration<Handler>>> {
///     let registration = Registration::register(irq, flags::SHARED, c_str!("my-device"), handler);
///
///     // You can have as many references to the registration as you want, so
///     // multiple parts of the driver can access it.
///     let registration = Arc::pin_init(registration, GFP_KERNEL)?;
///
///     // The handler may be called immediately after the function above
///     // returns, possibly in a different CPU.
///
///     {
///         // The data can be accessed from the process context too.
///         let mut data = registration.handler().0.lock();
///         *data = 42;
///     }
///
///     Ok(registration)
/// }
///
/// # Ok::<(), Error>(())
///```
///
/// # Invariants
///
/// * We own an irq handler using `&self` as its private data.
///
#[pin_data(PinnedDrop)]
pub struct Registration<T: Handler> {
    irq: u32,
    #[pin]
    handler: T,
    #[pin]
    /// Pinned because we need address stability so that we can pass a pointer
    /// to the callback.
    _pin: PhantomPinned,
}

impl<T: Handler> Registration<T> {
    /// Registers the IRQ handler with the system for the given IRQ number. The
    /// handler must be able to be called as soon as this function returns.
    pub fn register(
        irq: u32,
        flags: Flags,
        name: &'static CStr,
        handler: T,
    ) -> impl PinInit<Self, Error> {
        let closure = move |slot: *mut Self| {
            // SAFETY: The slot passed to pin initializer is valid for writing.
            unsafe {
                slot.write(Self {
                    irq,
                    handler,
                    _pin: PhantomPinned,
                })
            };

            // SAFETY:
            // - The callbacks are valid for use with request_irq.
            // - If this succeeds, the slot is guaranteed to be valid until the
            // destructor of Self runs, which will deregister the callbacks
            // before the memory location becomes invalid.
            let res = to_result(unsafe {
                bindings::request_irq(
                    irq,
                    Some(handle_irq_callback::<T>),
                    flags.0,
                    name.as_char_ptr(),
                    &*slot as *const _ as *mut core::ffi::c_void,
                )
            });

            if res.is_err() {
                // SAFETY: We are returning an error, so we can destroy the slot.
                unsafe { core::ptr::drop_in_place(addr_of_mut!((*slot).handler)) };
            }

            res
        };

        // SAFETY:
        // - if this returns Ok, then every field of `slot` is fully
        // initialized.
        // - if this returns an error, then the slot does not need to remain
        // valid.
        unsafe { pin_init_from_closure(closure) }
    }

    /// Returns a reference to the handler that was registered with the system.
    pub fn handler(&self) -> &T {
        // SAFETY: `handler` is initialized in `register`, and we require that
        // T: Sync.
        &self.handler
    }
}

#[pinned_drop]
impl<T: Handler> PinnedDrop for Registration<T> {
    fn drop(self: Pin<&mut Self>) {
        // SAFETY:
        // - `self.irq` is the same as the one passed to `reques_irq`.
        // -  `&self` was passed to `request_irq` as the cookie. It is
        // guaranteed to be unique by the type system, since each call to
        // `register` will return a different instance of `Registration`.
        //
        // Notice that this will block until all handlers finish executing,
        // i.e.: at no point will &self be invalid while the handler is running.
        unsafe { bindings::free_irq(self.irq, &*self as *const Self as *mut core::ffi::c_void) };
    }
}

/// The value that can be returned from `ThreadedHandler::handle_irq`.
pub enum ThreadedIrqReturn {
    /// The interrupt was not from this device or was not handled.
    None = bindings::irqreturn_IRQ_NONE as _,

    /// The interrupt was handled by this device.
    Handled = bindings::irqreturn_IRQ_HANDLED as _,

    /// The handler wants the handler thread to wake up.
    WakeThread = bindings::irqreturn_IRQ_WAKE_THREAD as _,
}

/// Callbacks for a threaded IRQ handler.
pub trait ThreadedHandler: Sync {
    /// The actual handler function. As usual, sleeps are not allowed in IRQ
    /// context.
    fn handle_irq(&self) -> ThreadedIrqReturn;

    /// The threaded handler function. This function is called from the irq
    /// handler thread, which is automatically created by the system.
    fn thread_fn(&self) -> IrqReturn;
}

/// A registration of a threaded IRQ handler for a given IRQ line.
///
/// Two callbacks are required: one to handle the IRQ, and one to handle any
/// other work in a separate thread.
///
/// The thread handler is only called if the IRQ handler returns `WakeThread`.
///
/// # Examples
///
/// The following is an example of using `ThreadedRegistration`:
///
/// ```
/// use kernel::prelude::*;
/// use kernel::irq::request::flags;
/// use kernel::irq::request::ThreadedIrqReturn;
/// use kernel::irq::request::ThreadedRegistration;
/// use kernel::irq::request::IrqReturn;
/// use kernel::sync::Arc;
/// use kernel::sync::SpinLock;
/// use kernel::alloc::flags::GFP_KERNEL;
/// use kernel::c_str;
///
/// // Declare a struct that will be passed in when the interrupt fires. The u32
/// // merely serves as an example of some internal data.
/// struct Data(SpinLock<u32>);
///
/// // [`handle_irq`] takes &self. This example illustrates interior
/// // mutability can be used when share the data between process context and IRQ
/// // context.
/// //
/// // Ideally, this example would be using a version of SpinLock that is aware
/// // of `spin_lock_irqsave` and `spin_lock_irqrestore`, but that is not yet
/// // implemented.
///
/// type Handler = Data;
///
/// impl kernel::irq::request::ThreadedHandler for Handler {
///     // This is executing in IRQ context in some CPU. Other CPUs can still
///     // try to access to data.
///     fn handle_irq(&self) -> ThreadedIrqReturn {
///         // We now have exclusive access to the data by locking the SpinLock.
///         let mut data = self.0.lock();
///         *data += 1;
///
///         // By returning `WakeThread`, we indicate to the system that the
///         // thread function should be called. Otherwise, return
///         // ThreadedIrqReturn::Handled.
///         ThreadedIrqReturn::WakeThread
///     }
///
///     // This will run (in a separate kthread) iff `handle_irq` returns
///     // `WakeThread`.
///     fn thread_fn(&self) -> IrqReturn {
///         // We now have exclusive access to the data by locking the SpinLock.
///         let mut data = self.0.lock();
///         *data += 1;
///
///         IrqReturn::Handled
///     }
/// }
///
/// // This is running in process context.
/// fn register_threaded_irq(irq: u32, handler: Handler) -> Result<Arc<ThreadedRegistration<Handler>>> {
///     let registration = ThreadedRegistration::register(irq, flags::SHARED, c_str!("my-device"), handler);
///
///     // You can have as many references to the registration as you want, so
///     // multiple parts of the driver can access it.
///     let registration = Arc::pin_init(registration, GFP_KERNEL)?;
///
///     // The handler may be called immediately after the function above
///     // returns, possibly in a different CPU.
///
///     {
///         // The data can be accessed from the process context too.
///         let mut data = registration.handler().0.lock();
///         *data = 42;
///     }
///
///     Ok(registration)
/// }
///
///
/// # Ok::<(), Error>(())
///```
///
/// # Invariants
///
/// * We own an irq handler using `&self` as its private data.
///
#[pin_data(PinnedDrop)]
pub struct ThreadedRegistration<T: ThreadedHandler> {
    irq: u32,
    #[pin]
    handler: T,
    #[pin]
    /// Pinned because we need address stability so that we can pass a pointer
    /// to the callback.
    _pin: PhantomPinned,
}

impl<T: ThreadedHandler> ThreadedRegistration<T> {
    /// Registers the IRQ handler with the system for the given IRQ number. The
    /// handler must be able to be called as soon as this function returns.
    pub fn register(
        irq: u32,
        flags: Flags,
        name: &'static CStr,
        handler: T,
    ) -> impl PinInit<Self, Error> {
        let closure = move |slot: *mut Self| {
            // SAFETY: The slot passed to pin initializer is valid for writing.
            unsafe {
                slot.write(Self {
                    irq,
                    handler,
                    _pin: PhantomPinned,
                })
            };

            // SAFETY:
            // - The callbacks are valid for use with request_threaded_irq.
            // - If this succeeds, the slot is guaranteed to be valid until the
            // destructor of Self runs, which will deregister the callbacks
            // before the memory location becomes invalid.
            let res = to_result(unsafe {
                bindings::request_threaded_irq(
                    irq,
                    Some(handle_threaded_irq_callback::<T>),
                    Some(thread_fn_callback::<T>),
                    flags.0,
                    name.as_char_ptr(),
                    slot.cast(),
                )
            });

            if res.is_err() {
                // SAFETY: We are returning an error, so we can destroy the slot.
                unsafe { core::ptr::drop_in_place(addr_of_mut!((*slot).handler)) };
            }

            res
        };

        // SAFETY:
        // - if this returns Ok(()), then every field of `slot` is fully
        // initialized.
        // - if this returns an error, then the slot does not need to remain
        // valid.
        unsafe { pin_init_from_closure(closure) }
    }

    /// Returns a reference to the handler that was registered with the system.
    pub fn handler(&self) -> &T {
        // SAFETY: `handler` is initialized in `register`, and we require that
        // T: Sync.
        &self.handler
    }
}

#[pinned_drop]
impl<T: ThreadedHandler> PinnedDrop for ThreadedRegistration<T> {
    fn drop(self: Pin<&mut Self>) {
        // SAFETY:
        // - `self.irq` is the same as the one passed to `request_threaded_irq`.
        // -  `&self` was passed to `request_threaded_irq` as the cookie. It is
        // guaranteed to be unique by the type system, since each call to
        // `register` will return a different instance of
        // `ThreadedRegistration`.
        //
        // Notice that this will block until all handlers finish executing, so,
        // at no point will &self be invalid while the handler is running.
        unsafe { bindings::free_irq(self.irq, &*self as *const Self as *mut core::ffi::c_void) };
    }
}

/// # Safety
///
/// This function should be only used as the callback in `request_irq`.
unsafe extern "C" fn handle_irq_callback<T: Handler>(
    _irq: i32,
    ptr: *mut core::ffi::c_void,
) -> core::ffi::c_uint {
    // SAFETY: `ptr` is a pointer to T set in `Registration::new`
    let data = unsafe { &*(ptr as *const T) };
    T::handle_irq(data) as _
}

/// # Safety
///
/// This function should be only used as the callback in `request_threaded_irq`.
unsafe extern "C" fn handle_threaded_irq_callback<T: ThreadedHandler>(
    _irq: i32,
    ptr: *mut core::ffi::c_void,
) -> core::ffi::c_uint {
    // SAFETY: `ptr` is a pointer to T set in `ThreadedRegistration::new`
    let data = unsafe { &*(ptr as *const T) };
    T::handle_irq(data) as _
}

/// # Safety
///
/// This function should be only used as the callback in `request_threaded_irq`.
unsafe extern "C" fn thread_fn_callback<T: ThreadedHandler>(
    _irq: i32,
    ptr: *mut core::ffi::c_void,
) -> core::ffi::c_uint {
    // SAFETY: `ptr` is a pointer to T set in `ThreadedRegistration::new`
    let data = unsafe { &*(ptr as *const T) };
    T::thread_fn(data) as _
}
