// SPDX-License-Identifier: GPL-2.0

//! Traits for transmuting types.

use core::slice;
use kernel::types::{LittleEndian, LE};

/// Types for which any bit pattern is valid.
///
/// Not all types are valid for all values. For example, a `bool` must be either zero or one, so
/// reading arbitrary bytes into something that contains a `bool` is not okay.
///
/// It's okay for the type to have padding, as initializing those bytes has no effect.
///
/// # Safety
///
/// All bit-patterns must be valid for this type. This type must not have interior mutability.
pub unsafe trait FromBytes: Sized {
    /// Converts the given byte slice into a shared reference to [`Self`].
    ///
    /// It fails if the size or alignment requirements are not satisfied.
    fn from_bytes(data: &[u8], offset: usize) -> Option<&Self> {
        if offset > data.len() {
            return None;
        }
        let data = &data[offset..];
        let ptr = data.as_ptr();
        if ptr as usize % align_of::<Self>() != 0 || data.len() < size_of::<Self>() {
            return None;
        }
        // SAFETY: The memory is valid for read because we have a reference to it. We have just
        // checked the minimum size and alignment as well.
        Some(unsafe { &*ptr.cast() })
    }

    /// Converts the given byte slice into a shared slice of [`Self`].
    ///
    /// It fails if the size or alignment requirements are not satisfied.
    fn from_bytes_to_slice(data: &[u8]) -> Option<&[Self]> {
        let ptr = data.as_ptr();
        if ptr as usize % align_of::<Self>() != 0 {
            return None;
        }
        // SAFETY: The memory is valid for read because we have a reference to it. We have just
        // checked the minimum alignment as well, and the length of the slice is calculated from
        // the length of `Self`.
        Some(unsafe { core::slice::from_raw_parts(ptr.cast(), data.len() / size_of::<Self>()) })
    }
}

macro_rules! impl_frombytes {
    ($($({$($generics:tt)*})? $t:ty, )*) => {
        // SAFETY: Safety comments written in the macro invocation.
        $(unsafe impl$($($generics)*)? FromBytes for $t {})*
    };
}

impl_frombytes! {
    // SAFETY: All bit patterns are acceptable values of the types below.
    u8, u16, u32, u64, usize,
    i8, i16, i32, i64, isize,

    // SAFETY: If all bit patterns are acceptable for individual values in an array, then all bit
    // patterns are also acceptable for arrays of that type.
    {<T: FromBytes, const N: usize>} [T; N],
    {<T: FromBytes + Copy + LittleEndian>} LE<T>,
}

/// Derive [`FromBytes`] for the structs defined in the block.
///
/// # Examples
///
/// ```
/// kernel::derive_frombytes! {
///     #[repr(C)]
///     struct SuperBlock {
///         a: u16,
///         _padding: [u8; 6],
///         b: u64,
///     }
///
///     #[repr(C)]
///     struct Inode {
///         a: u16,
///         b: u16,
///         c: u32,
///     }
/// }
/// ```
#[macro_export]
macro_rules! derive_frombytes {
    ($($(#[$outer:meta])* $outerv:vis struct $name:ident {
        $($(#[$m:meta])* $v:vis $id:ident : $t:ty),* $(,)?
    })*)=> {
        $(
            $(#[$outer])*
            $outerv struct $name {
                $(
                    $(#[$m])*
                    $v $id: $t,
                )*
            }
            unsafe impl $crate::transmute::FromBytes for $name {}
            const _: () = {
                const fn is_readable_from_bytes<T: $crate::transmute::FromBytes>() {}
                $(is_readable_from_bytes::<$t>();)*
            };
        )*
    };
}

/// Types that can be viewed as an immutable slice of initialized bytes.
///
/// If a struct implements this trait, then it is okay to copy it byte-for-byte to userspace. This
/// means that it should not have any padding, as padding bytes are uninitialized. Reading
/// uninitialized memory is not just undefined behavior, it may even lead to leaking sensitive
/// information on the stack to userspace.
///
/// The struct should also not hold kernel pointers, as kernel pointer addresses are also considered
/// sensitive. However, leaking kernel pointers is not considered undefined behavior by Rust, so
/// this is a correctness requirement, but not a safety requirement.
///
/// # Safety
///
/// Values of this type may not contain any uninitialized bytes. This type must not have interior
/// mutability.
pub unsafe trait AsBytes: Sized {}

macro_rules! impl_asbytes {
    ($($({$($generics:tt)*})? $t:ty, )*) => {
        // SAFETY: Safety comments written in the macro invocation.
        $(unsafe impl$($($generics)*)? AsBytes for $t {})*
    };
}

impl_asbytes! {
    // SAFETY: Instances of the following types have no uninitialized portions.
    u8, u16, u32, u64, usize,
    i8, i16, i32, i64, isize,
    bool,
    char,

    // SAFETY: If individual values in an array have no uninitialized portions, then the array
    // itself does not have any uninitialized portions either.
    {<T: AsBytes, const N: usize>} [T; N],
}

/// Casts the type of a slice to another.
///
/// # Examples
///
/// ```rust
/// # use kernel::transmute::cast_slice;
/// #[repr(transparent)]
/// #[derive(Debug)]
/// struct Container<T>(T);
///
/// let array = [0u32; 42];
/// let slice = &array;
/// // SAFETY: `Container<T>` transparently wraps a `T`.
/// let container_slice = unsafe { cast_slice(slice) };
/// pr_info!("{container_slice}");
/// ```
///
/// # Safety
/// - `T` and `U` must have the same layout.
pub unsafe fn cast_slice<T, U>(slice: &[T]) -> &[U] {
    // CAST: by the safety requirements, `T` and `U` have the same layout.
    let ptr = slice.as_ptr().cast::<U>();
    // SAFETY: `ptr` and `len` come from the same slice reference.
    unsafe { slice::from_raw_parts(ptr, slice.len()) }
}

/// Casts the type of a slice to another.
///
/// Also see [`cast_slice`].
///
/// # Safety
/// - `T` and `U` must have the same layout.
pub unsafe fn cast_slice_mut<T, U>(slice: &mut [T]) -> &mut [U] {
    // CAST: by the safety requirements, `T` and `U` have the same layout.
    let ptr = slice.as_mut_ptr().cast::<U>();
    // SAFETY: `ptr` and `len` come from the same slice reference.
    unsafe { slice::from_raw_parts_mut(ptr, slice.len()) }
}
