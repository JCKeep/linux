// SPDX-License-Identifier: GPL-2.0

//! IRQ manager
use crate::bindings;

/// enable handling of an irq
///
/// # Safety
///
/// - Call from IRQ context must promiss irq_chip has no buslock.
#[inline]
pub unsafe fn enable_irq(irq: u32) {
    // SAFETY: Just FFI call, and caller promiss that irq_chip has no buslock.
    unsafe { bindings::enable_irq(irq) };
}

/// disable an irq without waiting
///
/// # Note
///
/// This function may be called from IRQ context.
#[inline]
pub fn disable_irq_nosync(irq: u32) {
    // SAFETY: Just FFI call
    unsafe { bindings::disable_irq_nosync(irq) };
}

/// disable an irq and wait for completion
///
/// # Safety
///
/// - Can only be called from preemptible code as it might sleep when
///   an interrupt thread is associated to `irq`.
#[inline]
pub unsafe fn disable_irq(irq: u32) {
    // SAFETY: Just FFI call, and caller promiss that be called from preemptible code.
    unsafe { bindings::disable_irq(irq) };
}
