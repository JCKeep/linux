// SPDX-License-Identifier: GPL-2.0

//! Character devices.
#![allow(dead_code)]
use core::ptr::NonNull;

use crate::{
    error::{code, Error, Result},
    fs::file,
    str::CStr,
    ThisModule,
};

/// dev_t in C
pub type Devt = bindings::dev_t;

/// Character device.
pub struct Cdev(NonNull<bindings::cdev>);

impl Cdev {
    /// Alloc a Character devices.
    pub fn alloc(
        fops: &'static bindings::file_operations,
        module: &'static ThisModule,
    ) -> Result<Self> {
        let cdev = unsafe { bindings::cdev_alloc() };
        let mut cdev = NonNull::new(cdev).ok_or(code::ENOMEM)?;

        // SAFETY: todo
        unsafe {
            cdev.as_mut().ops = fops;
            cdev.as_mut().owner = module.as_ptr();
        }

        Ok(Self(cdev))
    }

    /// Add a char device to the system
    pub fn add(&mut self, dev: Devt, count: u32) -> Result {
        // SAFETY: todo
        let err = unsafe { bindings::cdev_add(self.0.as_ptr(), dev, count) };

        if err < 0 {
            return Err(Error::from_errno(err));
        }

        Ok(())
    }
}

impl Drop for Cdev {
    fn drop(&mut self) {
        // SAFETY: todo
        unsafe {
            bindings::cdev_del(self.0.as_ptr());
        }
    }
}

struct RegistrationInner<const N: usize> {
    dev: Devt,
    used: usize,
    cdevs: [Option<Cdev>; N],
}

/// char device registration
pub struct Registration<const N: usize = 1> {
    name: &'static CStr,
    firstminor: u32,
    module: &'static ThisModule,
    inner: Option<RegistrationInner<N>>,
}

impl<const N: usize> Registration<N> {
    /// todo
    pub fn new(name: &'static CStr, module: &'static ThisModule, firstminor: u32) -> Self {
        Self {
            name,
            firstminor,
            module,
            inner: None,
        }
    }

    /// todo
    pub fn register<T: file::Operations<OpenData = ()>>(&mut self) -> Result {
        if self.inner.is_none() {
            let mut dev = 0;
            // SAFETY: todo
            let err = unsafe {
                bindings::alloc_chrdev_region(
                    &mut dev,
                    self.firstminor,
                    N as u32,
                    self.name.as_char_ptr(),
                )
            };

            if err < 0 {
                return Err(Error::from_errno(err));
            }

            self.inner = Some(RegistrationInner {
                dev,
                used: 0,
                cdevs: [const { None::<Cdev> }; N],
            });
        }

        let inner = self.inner.as_mut().unwrap();
        if inner.used == N {
            return Err(code::EINVAL);
        }

        // SAFETY: todo
        let mut cdev = Cdev::alloc(
            unsafe { file::OperationsVtable::<Self, T>::build() },
            self.module,
        )?;
        cdev.add(inner.dev + inner.used as Devt, 1)?;
        inner.cdevs[inner.used] = Some(cdev);
        inner.used += 1;

        Ok(())
    }
}

impl<const N: usize> file::OpenAdapter<()> for Registration<N> {
    // SAFETY: only return (), never use
    unsafe fn convert(_inode: *mut bindings::inode, _file: *mut bindings::file) -> *const () {
        &()
    }
}

impl<const N: usize> Drop for Registration<N> {
    fn drop(&mut self) {
        if let Some(inner) = self.inner.as_mut() {
            for cdev in &mut inner.cdevs {
                cdev.take();
            }

            // SAFETY: todo
            unsafe {
                bindings::unregister_chrdev_region(inner.dev, N as u32);
            }
        }
    }
}

// SAFETY: todo
unsafe impl<const N: usize> Sync for Registration<N> {}
// SAFETY: todo
unsafe impl<const N: usize> Send for Registration<N> {}
