// SPDX-License-Identifier: GPL-2.0

//! Accessing (DeviceTree/ACPI) firmware properties.
//!
//! C header: [`include/linux/property.h`](srctree/include/linux/property.h)

use crate::{
    bindings,
    device::Device,
    error::{to_result, Result},
    prelude::*,
    str::CStr,
    transmute::{AsBytes, FromBytes},
};

use core::mem;
use core::mem::MaybeUninit;

/// A trait for integer types.
///
/// This trait limits [`FromBytes`] and [`AsBytes`] to integer types only. Excluding the
/// array types. The integer types are `u8`, `u16`, `u32`, `u64`, `usize`, `i8`, `i16`,
/// `i32`, `i64` and `isize`. Additionally, the size of these types is encoded in the
/// `IntSize` enum.
trait Integer: FromBytes + AsBytes + Copy {
    /// The size of the integer type.
    const SIZE: IntSize;
}

/// The sizes of the integer types. Either 8, 16, 32 or 64 bits.
enum IntSize {
    /// 8 bits
    S8,
    /// 16 bits
    S16,
    /// 32 bits
    S32,
    /// 64 bits
    S64,
}

macro_rules! impl_int {
    ($($typ:ty),* $(,)?) => {$(
        impl Integer for $typ {
            const SIZE: IntSize = match size_of::<Self>() {
                1 => IntSize::S8,
                2 => IntSize::S16,
                4 => IntSize::S32,
                8 => IntSize::S64,
                _ => panic!("invalid size"),
            };
        }
    )*};
}

impl_int! {
    u8, u16, u32, u64, usize,
    i8, i16, i32, i64, isize,
}

/// Reads an array of integers from the device firmware.
fn read_array<T: Integer>(
    device: &Device,
    name: &CStr,
    val: Option<&mut [MaybeUninit<T>]>,
) -> Result<usize> {
    let (ptr, len) = match val {
        // The read array data case.
        Some(val) => (val.as_mut_ptr(), val.len()),
        // The read count case.
        None => (core::ptr::null_mut(), 0_usize),
    };
    let ret = match T::SIZE {
        // SAFETY: `device_property_read_u8_array` is called with a valid device pointer and name.
        IntSize::S8 => unsafe {
            bindings::device_property_read_u8_array(
                device.as_raw(),
                name.as_ptr() as *const i8,
                ptr as *mut u8,
                len,
            )
        },
        // SAFETY: `device_property_read_u16_array` is called with a valid device pointer and name.
        IntSize::S16 => unsafe {
            bindings::device_property_read_u16_array(
                device.as_raw(),
                name.as_ptr() as *const i8,
                ptr as *mut u16,
                len,
            )
        },
        // SAFETY: `device_property_read_u32_array` is called with a valid device pointer and name.
        IntSize::S32 => unsafe {
            bindings::device_property_read_u32_array(
                device.as_raw(),
                name.as_ptr() as *const i8,
                ptr as *mut u32,
                len,
            )
        },
        // SAFETY: `device_property_read_u64_array` is called with a valid device pointer and name.
        IntSize::S64 => unsafe {
            bindings::device_property_read_u64_array(
                device.as_raw(),
                name.as_ptr() as *const i8,
                ptr as *mut u64,
                len,
            )
        },
    };
    to_result(ret)?;
    Ok(ret.try_into()?)
}

/// A trait for reading (DeviceTree/ACPI) firmware properties.
///
/// This trait serves as an interface to the device property API
/// which is a firmware agnostic API for reading properties from
/// firmware (DeviceTree/ACPI) device nodes and swnodes.
///
/// While the C API takes a pointer to a caller allocated variable/buffer,
/// this trait is designed to return a value and can be used in struct
/// initialization.
///
/// There are mandatory and optional properties. If a property is mandatory
/// it has to be there. If it is not found an error is printed and returned.
/// If a property is optional and found the value is returned. If it is not
/// found the default value is returned. If the default value is not provided,
/// an error is printed and returned.
///
/// This logic is controlled via the `default` parameter of type `Option<>`.
/// If `default` is `None` the property is assumed to be mandatory. If `default`
/// is `Some(<default_val>)` the property is assumed to be optional and the
/// `default_val` is returned in case the optional property is not found.
///
/// However, this doesn't apply to boolean properties. For boolean properties
/// the property exists or not. If it exists, it returns true, otherwise false.
/// So `Some(<default_val>)` does not make sense in this case and should be `None`.
/// An error is printed and returned if this not the case.
///
/// As errors are printed in above cases users of this trait are supposed
/// to *not* do any additional error printing. Of course, appropriate error handling
/// (without printing) needs to be implemented.
///
/// *Note*: To build and run below examples as `rustdoc` tests the additional kernel
/// Kconfig options `CONFIG_OF` and `CONFIG_OF_UNITTEST` need to be enabled. This
/// even works on non-ARM architectures as a test device tree is built into the
/// kernel, then.
///
/// # Examples
///
/// ```
/// # mod property_example {
/// #
/// # use kernel::{c_str, of, platform, prelude::*};
/// #
/// # struct PropertyExample {
/// #     pdev: platform::Device,
/// # }
/// #
/// # kernel::of_device_table!(
/// #     OF_TABLE,
/// #     MODULE_OF_TABLE,
/// #     <PropertyExample as platform::Driver>::IdInfo,
/// #     [(of::DeviceId::new(c_str!("test,rust-device")), ())]
/// # );
/// #
/// # impl platform::Driver for PropertyExample {
/// # type IdInfo = ();
/// # const ID_TABLE: platform::IdTable<Self::IdInfo> = &OF_TABLE;
/// #
/// # fn probe(
/// #   pdev: &mut platform::Device,
/// #   info: Option<&Self::IdInfo>
/// # ) -> Result<Pin<KBox<Self>>> {
/// # let dev = pdev.as_ref();
/// #
/// # dev_err!(dev, "The following two error messages are intended and correct from the tests:\n");
/// #
/// // Read an existing property as bool. This has two use cases:
/// // a) Get the value of a boolean property (true == exist, false == don't exist).
/// // b) Check if a property exists. Not limited to boolean properties.
/// let prop = dev.property_read::<bool>(c_str!("test,u32-prop"), None);
/// # //assert_eq!(prop, Ok(true)); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:?}\n", prop); // Debug only, drop later
/// if prop != Ok(true) {return Err(EINVAL);}
///
/// // Reading a non-existing property as bool should return false.
/// let prop = dev.property_read::<bool>(c_str!("test,bool-prop"), None);
/// # //assert_eq!(prop, Ok(false)); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:?}\n", prop); // Debug only, drop later
/// if prop != Ok(false) {return Err(EINVAL);}
///
/// // Invalid, returns with error. Don't use `Some(<bool>)` here (correct would be `None`).
/// // Should print an error.
/// let prop = dev.property_read::<bool>(c_str!("test,bool-prop"), Some(true));
/// # //assert_eq!(prop, Err(EINVAL)); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:?}\n", prop); // Debug only, drop later
/// if prop != Err(EINVAL) {return Err(EINVAL);}
///
/// // 'property_read::<integer>' or 'property_read::<array>' can read either optional or
/// // mandatory properties. If the property is mandatory and not found, it will print an
/// // error message and return with error. If the property is optional and not found, it
/// // will return with the given default value.
/// //
/// // Assume 'test,u32-optional' is an optional property which does not exist.
/// let prop: u32 = dev.property_read(c_str!("test,u32-optional"), Some(0xdb))?;
/// # //assert_eq!(prop, 0xdb); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:#x}\n", prop); // Debug only, drop later
/// if prop != 0xdb {return Err(EINVAL);}
///
/// // Assume 'test,u32-mandatory' is a mandatory property which does not exist.
/// // Should print an error.
/// let prop = dev.property_read::<u32>(c_str!("test,u32-mandatory"), None);
/// # //assert_eq!(prop, Err(EINVAL)); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:?}\n", prop); // Debug only, drop later
/// if prop != Err(EINVAL) {return Err(EINVAL);}
///
/// // Some examples for mandatory property which does exist.
/// // First in Turbofish syntax.
/// let prop = dev.property_read::<u32>(c_str!("test,u32-prop"), None)?;
/// # //assert_eq!(prop, Err(EINVAL)); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:#x}\n", prop); // Debug only, drop later
/// if prop != 0xdeadbeef {return Err(EINVAL);}
///
/// // Second with type annotation.
/// let prop: u32 = dev.property_read(c_str!("test,u32-prop"), None)?;
/// # //assert_eq!(prop, Err(EINVAL)); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:#x}\n", prop); // Debug only, drop later
/// if prop != 0xdeadbeef {return Err(EINVAL);}
///
/// // Reading a mandatory array of integers.
/// let prop: [i16; 4] = dev.property_read(c_str!("test,i16-array"), None)?;
/// # //assert_eq!(prop, [1, 2, -3, -4]); // FIXME: How to build this?
/// # dev_info!(dev, "prop: {:?}\n", prop); // Debug only, drop later
/// if prop != [1, 2, -3, -4] {return Err(EINVAL);}
///
/// // Getting the length of the 16 bits array.
/// let length = dev.property_count_elem::<i16>(c_str!("test,i16-array"))?;
/// # //assert_eq!(length, 4); // FIXME: How to build this?
/// # dev_info!(dev, "length: {}\n", length); // Debug only, drop later
/// if length != 4 {return Err(EINVAL);}
///
/// // Match a string.
/// let idx = dev.property_match_string::<usize>(c_str!("compatible"), c_str!("test,rust-device"));
/// # //assert_eq!(idx, Ok(0)); // FIXME: How to build this?
/// # dev_info!(dev, "idx: {:?}\n", idx); // Debug only, drop later
/// if idx != Ok(0) {return Err(EINVAL);}
/// #
/// # let drvdata = KBox::new(Self { pdev: pdev.clone() }, GFP_KERNEL)?;
/// #
/// # Ok(drvdata.into())
/// # }
/// # }
/// #
/// # kernel::module_platform_driver! {
/// #     type: PropertyExample,
/// #     name: "rust_property_example",
/// #     author: "Rob Herring and Dirk Behme",
/// #     description: "Rust Property Example driver",
/// #     license: "GPL v2",
/// # }
/// # }
/// ```
/// The above examples intentionally don't print any error messages (e.g. with `dev_err!()`).
/// The called abstractions already print error messages if needed what is considered to be
/// sufficient. The goal is to be less verbose regarding error messages.
pub trait FwProperty: Sized {
    /// Reads a property from the device.
    fn read_property(device: &Device, name: &CStr, default: Option<Self>) -> Result<Self>;

    /// Gets the properties element count.
    fn count_elem(device: &Device, name: &CStr) -> Result<usize>;

    /// Returns if a firmware string property `name` has match for `match_str`.
    fn match_string(device: &Device, name: &CStr, match_str: &CStr) -> Result<usize> {
        // SAFETY: `device_property_match_string` is called with a valid device pointer and name.
        let ret = unsafe {
            bindings::device_property_match_string(
                device.as_raw(),
                name.as_ptr() as *const i8,
                match_str.as_ptr() as *const i8,
            )
        };
        to_result(ret)?;
        Ok(ret as usize)
    }
}

impl FwProperty for bool {
    fn read_property(device: &Device, name: &CStr, default: Option<Self>) -> Result<Self> {
        if default.is_some() {
            dev_err!(
                device,
                "Error: Default value should be 'None' for reading boolean property"
            );
            return Err(EINVAL);
        }
        // SAFETY: `device_property_present` is called with a valid device pointer and name.
        Ok(unsafe {
            bindings::device_property_present(device.as_raw(), name.as_ptr() as *const i8)
        })
    }

    /// Gets the properties element count.
    // FIXME: Could this be made to be a build time error?
    fn count_elem(device: &Device, _name: &CStr) -> Result<usize> {
        dev_err!(
            device,
            "Error: Boolean type does not implement element count"
        );
        Err(EINVAL)
    }
}

impl<T: Integer + Copy> FwProperty for T {
    fn read_property(device: &Device, name: &CStr, default: Option<Self>) -> Result<Self> {
        let mut val: [MaybeUninit<T>; 1] = [const { MaybeUninit::uninit() }; 1];
        match read_array(device, name, Some(&mut val)) {
            // SAFETY: `read_array` returns with valid data
            Ok(_) => Ok(unsafe { mem::transmute_copy(&val[0]) }),
            Err(e) => match default {
                Some(default) => Ok(default),
                None => {
                    dev_err!(
                        device,
                        "Error: Mandatory property '{}' does not exist ({:?})",
                        name,
                        e
                    );
                    Err(e)
                }
            },
        }
    }

    /// Gets the properties element count.
    fn count_elem(device: &Device, name: &CStr) -> Result<usize> {
        read_array::<T>(device, name, None)
    }
}

impl<T: Integer, const N: usize> FwProperty for [T; N] {
    fn read_property(device: &Device, name: &CStr, default: Option<Self>) -> Result<Self> {
        let mut val: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];
        match read_array(device, name, Some(&mut val)) {
            // SAFETY: `read_array` returns with valid data
            Ok(_) => Ok(unsafe { mem::transmute_copy(&val) }),
            Err(e) => match default {
                Some(default) => Ok(default),
                None => {
                    dev_err!(
                        device,
                        "Error: Mandatory property '{}' does not exist {:?}",
                        name,
                        e
                    );
                    Err(e)
                }
            },
        }
    }

    /// Gets the properties element count.
    // FIXME: Could this be made to be a build time error?
    fn count_elem(device: &Device, _name: &CStr) -> Result<usize> {
        dev_err!(device, "Error: Array type does not implement element count");
        Err(EINVAL)
    }
}
