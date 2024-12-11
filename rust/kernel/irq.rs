// SPDX-License-Identifier: GPL-2.0

//! Interrupt Request (IRQ) Handling Utilities
//!
//! This module provides constants and enums for working with IRQs in a kernel
//! context, including support for shared IRQs and return values for interrupt
//! handlers.

/// Constant indicating a shared IRQ.
///
/// When an IRQ is shared, multiple devices can use the same IRQ line, and each
/// device's handler must check if the interrupt belongs to its device before processing it.
///
/// Equivalent to `IRQF_SHARED` in the C bindings.
pub const IRQ_SHARED: u32 = bindings::IRQF_SHARED;

/// Enum representing possible return values from an IRQ handler.
///
/// These return values indicate how the kernel should proceed after the handler
/// is executed. They are mapped from the corresponding constants in the C bindings.
pub enum IrqReturn {
    /// Indicates that the IRQ was not handled by this handler.
    ///
    /// This is equivalent to `IRQ_NONE` in the C bindings.
    None = bindings::irqreturn_IRQ_NONE as _,

    /// Indicates that the IRQ was successfully handled by this handler.
    ///
    /// This is equivalent to `IRQ_HANDLED` in the C bindings.
    Handled = bindings::irqreturn_IRQ_HANDLED as _,

    /// Indicates that the IRQ handler requests the kernel to wake up a
    /// threaded handler to complete the processing of this interrupt.
    ///
    /// This is equivalent to `IRQ_WAKE_THREAD` in the C bindings.
    WakeThread = bindings::irqreturn_IRQ_WAKE_THREAD as _,
}
