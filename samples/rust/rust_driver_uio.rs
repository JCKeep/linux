// SPDX-License-Identifier: GPL-2.0

//! Rust Platform UIO driver sample.

use kernel::{
    c_str,
    mm::virt::VmAreaNew,
    new_spinlock_irq,
    of::{DeviceId, IdTable},
    page::PAGE_SIZE,
    platform,
    prelude::*,
    sync::{Arc, ArcBorrow, SpinLockIrq},
    uio::{self, UioDevice, UioDeviceOptions},
};

kernel::module_platform_driver! {
    type: SampleUioDriver,
    name: "rust_driver_uio",
    author: "Guangbo Cui",
    description: "Rust Sample Platform UIO driver",
    license: "GPL v2",
}

const HELLO_WORLD: &[u8] = b"Hello World from rust uio driver\0";

struct SampleUioDriver {
    pdev: platform::Device,
    _uio_registration: Pin<KBox<uio::Registration<SimpleUioDriver>>>,
}

type DriverData = VBox<[u8; PAGE_SIZE]>;
struct SimpleUioDriver;

struct Info(u32);

kernel::of_device_table!(
    OF_TABLE,
    MODULE_OF_TABLE,
    <SampleUioDriver as platform::Driver>::IdInfo,
    [(DeviceId::new(c_str!("rust,rust-platform-drv")), Info(42))]
);

impl platform::Driver for SampleUioDriver {
    type IdInfo = Info;
    const OF_ID_TABLE: Option<IdTable<Self::IdInfo>> = Some(&OF_TABLE);

    fn probe(pdev: &mut platform::Device, info: Option<&Self::IdInfo>) -> Result<Pin<KBox<Self>>> {
        dev_info!(pdev.as_ref(), "Probe Rust Platform UIO driver sample.\n");

        if let Some(info) = info {
            dev_info!(
                pdev.as_ref(),
                "Probed by OF compatible match  with info: '{}'.\n",
                info.0
            );
        }

        let dev = pdev.as_ref();
        let mut options = UioDeviceOptions::new(c_str!("rust_uio"), c_str!("0.0.1"));

        let data = Arc::pin_init(
            new_spinlock_irq!(VBox::new([0_u8; PAGE_SIZE], GFP_KERNEL)?),
            GFP_KERNEL,
        )?;

        options.mem[0].setup_mem(
            Some(c_str!("test")),
            data.lock().as_ptr() as _,
            PAGE_SIZE,
            uio::MemType::Virtual,
        );

        let registration = KBox::pin_init(
            uio::Registration::register(&THIS_MODULE, dev, options, data),
            GFP_KERNEL,
        )?;

        let drvdata = KBox::new(
            Self {
                pdev: pdev.clone(),
                _uio_registration: registration,
            },
            GFP_KERNEL,
        )?;

        Ok(drvdata.into())
    }
}

impl Drop for SampleUioDriver {
    fn drop(&mut self) {
        dev_info!(
            self.pdev.as_ref(),
            "Remove Rust Platform UIO driver sample.\n"
        );
    }
}

#[vtable]
impl UioDevice for SimpleUioDriver {
    type Data = Arc<SpinLockIrq<DriverData>>;

    fn open(info: &uio::Info, data: ArcBorrow<'_, SpinLockIrq<DriverData>>) -> Result {
        dev_info!(info.as_dev(), "rust uio device open\n");

        // SAFETY: todo
        unsafe {
            core::ptr::copy_nonoverlapping(
                HELLO_WORLD.as_ptr(),
                data.lock().as_mut_ptr(),
                HELLO_WORLD.len(),
            );
        }

        Ok(())
    }

    fn release(info: &uio::Info, _data: ArcBorrow<'_, SpinLockIrq<DriverData>>) {
        dev_info!(info.as_dev(), "rust uio device close\n");
    }

    fn mmap(
        info: &uio::Info,
        _data: ArcBorrow<'_, SpinLockIrq<DriverData>>,
        vma: &VmAreaNew,
    ) -> Result {
        let mem_info = info.get_uio_mem();

        vma.set_dontdump();
        vma.set_dontexpand();

        let mixed_vma = vma.set_mixedmap();

        // SAFETY: todo
        let raw_page = unsafe { kernel::bindings::vmalloc_to_page(mem_info[0].addr() as _) };

        // SAFETY: todo
        unsafe {
            kernel::bindings::vm_insert_page(mixed_vma.as_ptr(), vma.start(), raw_page);
        }

        Ok(())
    }
}
