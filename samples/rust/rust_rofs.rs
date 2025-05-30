// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

#![allow(clippy::ignored_unit_patterns)]
use kernel::fs::{
    address_space, dentry, dentry::DEntry, file, file::File, inode, inode::INode, sb, Offset,
};
use kernel::prelude::*;
use kernel::str::CString;
use kernel::types::{ARef, Either, Locked};
use kernel::uaccess::UserSliceWriter;
use kernel::{c_str, folio::Folio, folio::PageCache, fs, time::UNIX_EPOCH};

kernel::module_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

struct Entry {
    name: &'static [u8],
    ino: u64,
    etype: inode::Type,
    contents: &'static [u8],
}

const ENTRIES: [Entry; 4] = [
    Entry {
        name: b".",
        ino: 1,
        etype: inode::Type::Dir,
        contents: b"",
    },
    Entry {
        name: b"..",
        ino: 1,
        etype: inode::Type::Dir,
        contents: b"",
    },
    Entry {
        name: b"test.txt",
        ino: 2,
        etype: inode::Type::Reg,
        contents: b"hello world\n",
    },
    Entry {
        name: b"link.txt",
        ino: 3,
        etype: inode::Type::Lnk(Some(Either::Right(c_str!("./test.txt")))),
        contents: b"./test.txt",
    },
];

const DIR_FOPS: file::Ops<RoFs> = file::Ops::new::<RoFs>();
const DIR_IOPS: inode::Ops<RoFs> = inode::Ops::new::<RoFs>();
const FILE_AOPS: address_space::Ops<RoFs> = address_space::Ops::new::<RoFs>();

#[vtable]
impl fs::Context<Self> for RoFs {
    type Data = ();

    kernel::define_fs_params! {(),
        {flag, "flag", |_, v| { pr_info!("flag passed-in: {v}\n"); Ok(()) } },
        {flag_no, "flagno", |_, v| { pr_info!("flagno passed-in: {v}\n"); Ok(()) } },
        {bool, "bool", |_, v| { pr_info!("bool passed-in: {v}\n"); Ok(()) } },
        {u32, "u32", |_, v| { pr_info!("u32 passed-in: {v}\n"); Ok(()) } },
        {u32oct, "u32oct", |_, v| { pr_info!("u32oct passed-in: {v}\n"); Ok(()) } },
        {u32hex, "u32hex", |_, v| { pr_info!("u32hex passed-in: {v}\n"); Ok(()) } },
        {s32, "s32", |_, v| { pr_info!("s32 passed-in: {v}\n"); Ok(()) } },
        {u64, "u64", |_, v| { pr_info!("u64 passed-in: {v}\n"); Ok(()) } },
        {string, "string", |_, v| { pr_info!("string passed-in: {v}\n"); Ok(()) } },
        {enum, "enum", [("first", 10), ("second", 20)], |_, v| {
            pr_info!("enum passed-in: {v}\n"); Ok(()) }
        },
    }

    fn try_new() -> Result {
        pr_info!("context created!\n");
        Ok(())
    }
}

struct RoFs;

impl RoFs {
    fn iget(sb: &sb::SuperBlock<Self>, e: &'static Entry) -> Result<ARef<INode<Self>>> {
        let mut new = match sb.get_or_create_inode(e.ino)? {
            Either::Left(existing) => return Ok(existing),
            Either::Right(new) => new,
        };

        let (mode, nlink, size, typ) = match e.etype {
            inode::Type::Dir => {
                new.set_iops(DIR_IOPS).set_fops(DIR_FOPS);
                (0o555, 2, ENTRIES.len().try_into()?, inode::Type::Dir)
            }
            inode::Type::Reg => {
                new.set_fops(file::Ops::generic_ro_file())
                    .set_aops(FILE_AOPS);
                (0o444, 1, e.contents.len().try_into()?, inode::Type::Reg)
            }
            inode::Type::Lnk(Some(Either::Right(s))) => {
                new.set_iops(inode::Ops::simple_symlink_inode());
                (
                    0o444,
                    1,
                    e.contents.len().try_into()?,
                    inode::Type::Lnk(Some(Either::Right(s))),
                )
            }
            _ => return Err(ENOENT),
        };

        new.init(inode::Params {
            typ,
            mode,
            size,
            blocks: (u64::try_from(size)?).div_ceil(512),
            nlink,
            uid: 0,
            gid: 0,
            atime: UNIX_EPOCH,
            ctime: UNIX_EPOCH,
            mtime: UNIX_EPOCH,
            value: e,
        })
    }
}

impl fs::FileSystem for RoFs {
    type Context = Self;
    type Data = ();
    type INodeData = &'static Entry;
    const NAME: &'static CStr = c_str!("rust_rofs");

    fn fill_super(
        _data: (),
        sb: &mut sb::SuperBlock<Self, sb::New>,
        _: Option<inode::Mapper>,
    ) -> Result {
        sb.set_magic(0x52555354);
        Ok(())
    }

    fn init_root(sb: &sb::SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        let inode = Self::iget(sb, &ENTRIES[0])?;
        dentry::Root::try_new(inode)
    }
}

#[vtable]
impl inode::Operations for RoFs {
    type FileSystem = Self;

    fn get_link<'a>(
        _dentry: Option<&DEntry<Self::FileSystem>>,
        _inode: &'a INode<Self::FileSystem>,
    ) -> Result<Either<CString, &'a CStr>> {
        pr_err!("get_link called on read-only file system\n");

        // This file system does not support symlinks.
        Err(ENOTSUPP)
    }

    fn lookup(
        parent: &Locked<&INode<Self>, inode::ReadSem>,
        dentry: dentry::Unhashed<'_, Self>,
    ) -> Result<Option<ARef<DEntry<Self>>>> {
        // SAFETY: todo
        pr_info!("lookup called for dentry: {:?}\n", unsafe {
            CStr::from_bytes_with_nul_unchecked(dentry.name())
        });

        if parent.ino() != 1 {
            return dentry.splice_alias(None);
        }

        let name = dentry.name();
        for e in &ENTRIES {
            if name == e.name {
                let inode = Self::iget(parent.super_block(), e)?;
                return dentry.splice_alias(Some(inode));
            }
        }

        dentry.splice_alias(None)
    }
}

#[vtable]
impl address_space::Operations for RoFs {
    type FileSystem = Self;

    fn read_folio(_: Option<&File<Self>>, mut folio: Locked<&Folio<PageCache<Self>>>) -> Result {
        let data = folio.inode().data().contents;
        let pos = usize::try_from(folio.pos()).unwrap_or(usize::MAX);
        let copied = if pos >= data.len() {
            0
        } else {
            let to_copy = core::cmp::min(data.len() - pos, folio.size());
            folio.write(0, &data[pos..][..to_copy])?;
            to_copy
        };

        folio.zero_out(copied, folio.size() - copied)?;
        folio.mark_uptodate();
        folio.flush_dcache();

        Ok(())
    }
}

#[vtable]
impl file::Operations for RoFs {
    type FileSystem = Self;

    fn seek(file: &File<Self>, offset: Offset, whence: file::Whence) -> Result<Offset> {
        file::generic_seek(file, offset, whence)
    }

    fn read(_: &File<Self>, _: &mut UserSliceWriter, _: &mut Offset) -> Result<usize> {
        Err(EISDIR)
    }

    fn read_dir(
        _file: &File<Self>,
        inode: &Locked<&INode<Self>, inode::ReadSem>,
        emitter: &mut file::DirEmitter,
    ) -> Result {
        if inode.ino() != 1 {
            return Ok(());
        }

        let pos = emitter.pos();
        if pos >= ENTRIES.len().try_into()? {
            return Ok(());
        }

        for e in ENTRIES.iter().skip(pos.try_into()?) {
            if !emitter.emit(1, e.name, e.ino, (&e.etype).into()) {
                break;
            }
        }

        Ok(())
    }
}
