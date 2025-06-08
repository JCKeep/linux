// SPDX-License-Identifier: GPL-2.0

//! Definitions of tarfs structures.

use core::cmp;

use kernel::{
    c_str,
    folio::Folio,
    fs::{
        self, address_space, dentry, file,
        inode::{self, ReadSem},
        iomap, sb, Context, DEntry, File, INode, Offset, SuperBlock,
    },
    macros::vtable,
    page::PAGE_SIZE,
    prelude::*,
    str::CString,
    time::Timespec,
    transmute::FromBytes,
    types::{ARef, Either, Locked, LE},
    uaccess,
};

use crate::defs::{
    DirEntry, Group, Super, EXT2_DIND_BLOCK, EXT2_IND_BLOCK, EXT2_NDIR_BLOCKS, EXT2_TIND_BLOCK,
};

mod defs {
    use kernel::types::LE;

    /*
     * Constants relative to the data blocks
     */
    pub(crate) const EXT2_NDIR_BLOCKS: usize = 12;
    pub(crate) const EXT2_IND_BLOCK: usize = EXT2_NDIR_BLOCKS;
    pub(crate) const EXT2_DIND_BLOCK: usize = EXT2_IND_BLOCK + 1;
    pub(crate) const EXT2_TIND_BLOCK: usize = EXT2_DIND_BLOCK + 1;
    pub(crate) const EXT2_N_BLOCKS: usize = EXT2_TIND_BLOCK + 1;

    kernel::derive_frombytes! {
        // TODO: Simplify this.
        #[repr(C)]
        pub(crate) struct Super {
            pub(crate) inodes_count: LE<u32>,
            pub(crate) blocks_count: LE<u32>,
            pub(crate) r_blocks_count: LE<u32>,
            pub(crate) free_blocks_count: LE<u32>,    /* Free blocks count */
            pub(crate) free_inodes_count: LE<u32>,    /* Free inodes count */
            pub(crate) first_data_block: LE<u32>, /* First Data Block */
            pub(crate) log_block_size: LE<u32>,   /* Block size */
            pub(crate) log_frag_size: LE<u32>,    /* Fragment size */
            pub(crate) blocks_per_group: LE<u32>, /* # Blocks per group */
            pub(crate) frags_per_group: LE<u32>,  /* # Fragments per group */
            pub(crate) inodes_per_group: LE<u32>, /* # Inodes per group */
            pub(crate) mtime: LE<u32>,         /* Mount time */
            pub(crate) wtime: LE<u32>,         /* Write time */
            pub(crate) mnt_count: LE<u16>,             /* Mount count */
            pub(crate) max_mnt_count: LE<u16>, /* Maximal mount count */
            pub(crate) magic: LE<u16>,         /* Magic signature */
            pub(crate) state: LE<u16>,         /* File system state */
            pub(crate) errors: LE<u16>,                /* Behaviour when detecting errors */
            pub(crate) minor_rev_level: LE<u16>,       /* minor revision level */
            pub(crate) lastcheck: LE<u32>,             /* time of last check */
            pub(crate) checkinterval: LE<u32>, /* max. time between checks */
            pub(crate) creator_os: LE<u32>,            /* OS */
            pub(crate) rev_level: LE<u32>,             /* Revision level */
            pub(crate) def_resuid: LE<u16>,            /* Default uid for reserved blocks */
            pub(crate) def_resgid: LE<u16>,            /* Default gid for reserved blocks */
            /*
            * These fields are for EXT2_DYNAMIC_REV superblocks only.
            *
            * Note: the difference between the compatible feature set and
            * the incompatible feature set is that if there is a bit set
            * in the incompatible feature set that the kernel doesn't
            * know about, it should refuse to mount the filesystem.
            *
            * e2fsck's requirements are more strict; if it doesn't know
            * about a feature in either the compatible or incompatible
            * feature set, it must abort and not try to meddle with
            * things it doesn't understand...
            */
            pub(crate) first_ino: LE<u32>,             /* First non-reserved inode */
            pub(crate) inode_size: LE<u16>,          /* size of inode structure */
            pub(crate) block_group_nr: LE<u16>,        /* block group # of this superblock */
            pub(crate) feature_compat: LE<u32>,        /* compatible feature set */
            pub(crate) feature_incompat: LE<u32>,      /* incompatible feature set */
            pub(crate) feature_ro_compat: LE<u32>,     /* readonly-compatible feature set */
            pub(crate) uuid: [u8; 16], /* 128-bit uuid for volume */
            pub(crate) volume_name: [u8; 16],  /* volume name */
            pub(crate) last_mounted: [u8; 64],         /* directory where last mounted */
            pub(crate) algorithm_usage_bitmap: LE<u32>, /* For compression */
            /*
            * Performance hints.  Directory preallocation should only
            * happen if the EXT2_COMPAT_PREALLOC flag is on.
            */
            pub(crate) prealloc_blocks: u8,    /* Nr of blocks to try to preallocate*/
            pub(crate) prealloc_dir_blocks: u8,        /* Nr to preallocate for dirs */
            padding1: u16,
            /*
            * Journaling support valid if EXT3_FEATURE_COMPAT_HAS_JOURNAL set.
            */
            pub(crate) journal_uuid: [u8; 16], /* uuid of journal superblock */
            pub(crate) journal_inum: u32,              /* inode number of journal file */
            pub(crate) journal_dev: u32,               /* device number of journal file */
            pub(crate) last_orphan: u32,               /* start of list of inodes to delete */
            pub(crate) hash_seed: [u32; 4],            /* HTREE hash seed */
            pub(crate) def_hash_version: u8,   /* Default hash version to use */
            pub(crate) reserved_char_pad: u8,
            pub(crate) reserved_word_pad: u16,
            pub(crate) default_mount_opts: LE<u32>,
            pub(crate) first_meta_bg: LE<u32>,         /* First metablock block group */
            reserved: [u32; 190],   /* Padding to the end of the block */
        }

        #[repr(C)]
        #[derive(Clone, Copy)]
        pub(crate) struct Group {
            /// Blocks bitmap block.
            pub block_bitmap: LE<u32>,

            /// Inodes bitmap block.
            pub inode_bitmap: LE<u32>,

            /// Inodes table block.
            pub inode_table: LE<u32>,

            /// Number of free blocks.
            pub free_blocks_count: LE<u16>,

            /// Number of free inodes.
            pub free_inodes_count: LE<u16>,

            /// Number of directories.
            pub used_dirs_count: LE<u16>,

            pad: LE<u16>,
            reserved: [u32; 3],
        }

        #[repr(C)]
        pub(crate) struct INode {
            pub mode: LE<u16>,          /* File mode */
            pub uid: LE<u16>,           /* Low 16 bits of Owner Uid */
            pub size: LE<u32>,          /* Size in bytes */
            pub atime: LE<u32>, /* Access time */
            pub ctime: LE<u32>, /* Creation time */
            pub mtime: LE<u32>, /* Modification time */
            pub dtime: LE<u32>, /* Deletion Time */
            pub gid: LE<u16>,           /* Low 16 bits of Group Id */
            pub links_count: LE<u16>,   /* Links count */
            pub blocks: LE<u32>,        /* Blocks count */
            pub flags: LE<u32>, /* File flags */
            pub reserved1: LE<u32>,
            pub block: [LE<u32>; EXT2_N_BLOCKS],/* Pointers to blocks */
            pub generation: LE<u32>,    /* File version (for NFS) */
            pub file_acl: LE<u32>,      /* File ACL */
            pub dir_acl: LE<u32>,       /* Directory ACL */
            pub faddr: LE<u32>, /* Fragment address */
        }

        #[repr(C)]
        pub(crate) struct DirEntry {
            pub(crate) inode: LE<u32>,                 /* Inode number */
            pub(crate) rec_len: LE<u16>,               /* Directory entry length */
            pub(crate) name_len: u8,           /* Name length */
            pub(crate) file_type: u8, // TODO: This only exists if the "filetype" feature flag is set.
        }
    }

    pub(crate) const FT_REG_FILE: u8 = 1;
    pub(crate) const FT_DIR: u8 = 2;
    pub(crate) const FT_CHRDEV: u8 = 3;
    pub(crate) const FT_BLKDEV: u8 = 4;
    pub(crate) const FT_FIFO: u8 = 5;
    pub(crate) const FT_SOCK: u8 = 6;
    pub(crate) const FT_SYMLINK: u8 = 7;
}

kernel::module_fs! {
    type: Ext2Fs,
    name: "ext2",
    author: "Wedson Almeida Filho <walmeida@microsoft.com>",
    description: "ext2 file system",
    license: "GPL",
}

const SECTOR_SIZE: usize = 512;
const SB_OFFSET: u64 = 1024;

struct INodeData {
    data_blocks: [u32; defs::EXT2_N_BLOCKS],
}

struct Ext2Fs {
    block_size: u64,
    _block_size_bits: u32,
    inodes_per_group: u32,
    inode_count: u32,
    inode_size: usize,
    group: KVec<defs::Group>,
}

impl Ext2Fs {
    fn iget(sb: &SuperBlock<Self>, ino: u64) -> Result<ARef<INode<Self>>> {
        let s = sb.data();
        // TODO: Use constants.
        if ino < 2 || ino > s.inode_count.into() {
            return Err(ENOENT);
        }
        let group = usize::try_from((ino - 1) / u64::from(s.inodes_per_group))?;
        let offset = (ino - 1) % u64::from(s.inodes_per_group);

        if usize::try_from(group)? >= s.group.len() {
            return Err(ENOENT);
        }

        // Create an inode or find an existing (cached) one.
        let mut inode = match sb.get_or_create_inode(ino)? {
            Either::Left(existing) => return Ok(existing),
            Either::Right(new) => new,
        };

        let inodes_block = u64::from(s.group[group].inode_table.value());
        let inodes_per_block = s.block_size / s.inode_size as u64;
        let inode_block = offset / inodes_per_block;
        let offset = usize::try_from(offset % inodes_per_block)?;

        let bh = sb.bread(inodes_block + inode_block)?;
        let b = bh.data();
        let idata = defs::INode::from_bytes(b, offset * s.inode_size).ok_or(EIO)?;
        let mode = idata.mode.value();

        // TODO: What else is allowed?
        // Ignore inodes that have unknown mode bits.
        if (mode & !(fs::mode::S_IFMT | 0o777)) != 0 {
            return Err(ENOENT);
        }

        const DIR_FOPS: file::Ops<Ext2Dir> = file::Ops::new();
        const DIR_IOPS: inode::Ops<Ext2Dir> = inode::Ops::new();
        const FILE_AOPS: address_space::Ops<Ext2Fs> = iomap::ro_aops::<Ext2Fs>();

        let size = idata.size.value().try_into()?;
        let typ = match mode & fs::mode::S_IFMT {
            fs::mode::S_IFREG => {
                inode
                    .set_aops(FILE_AOPS)
                    .set_fops(file::Ops::<()>::generic_ro_file());
                inode::Type::Reg
            }
            fs::mode::S_IFDIR => {
                inode.set_iops(DIR_IOPS).set_fops(DIR_FOPS);
                inode::Type::Dir
            }
            fs::mode::S_IFLNK => {
                if idata.blocks.value() == 0 {
                    const OFFSET: usize = core::mem::offset_of!(defs::INode, block);
                    let name = &b[offset * s.inode_size + OFFSET..];
                    let name_len = idata.size.value() as usize;
                    if name_len > name.len() || name_len == 0 {
                        return Err(EIO);
                    }
                    inode.set_iops(inode::Ops::<()>::simple_symlink_inode());
                    let s = CStr::from_bytes_with_nul(name).map_err(|err| {
                        pr_err!("Invalid symlink name: {err:?}\n");
                        ENOENT
                    })?;
                    inode::Type::Lnk(Some(CString::try_from(s)?))
                } else {
                    inode
                        .set_aops(FILE_AOPS)
                        .set_iops(inode::Ops::<()>::page_symlink_inode());
                    inode::Type::Lnk(None)
                }
            }
            fs::mode::S_IFSOCK => inode::Type::Sock,
            fs::mode::S_IFIFO => inode::Type::Fifo,
            fs::mode::S_IFCHR => {
                let (major, minor) = decode_dev(&idata.block);
                inode::Type::Chr(major, minor)
            }
            fs::mode::S_IFBLK => {
                let (major, minor) = decode_dev(&idata.block);
                inode::Type::Blk(major, minor)
            }
            _ => return Err(ENOENT),
        };
        inode.init(inode::Params {
            typ,
            mode: mode & 0o777,
            size,
            blocks: idata.blocks.value().into(),
            nlink: idata.links_count.value().into(),
            uid: idata.uid.value().into(),
            gid: idata.gid.value().into(),
            ctime: Timespec::new(idata.ctime.value().into(), 0)?,
            mtime: Timespec::new(idata.mtime.value().into(), 0)?,
            atime: Timespec::new(idata.atime.value().into(), 0)?,
            value: INodeData {
                data_blocks: core::array::from_fn(|i| idata.block[i].value()),
            },
        })
    }

    fn offsets<'a>(&self, mut block: u64, out: &'a mut [u32]) -> Option<&'a [u32]> {
        let ptrs = self.block_size / (size_of::<u32>() as u64);
        let ptr_mask = ptrs - 1;
        let ptr_bits = ptrs.trailing_zeros();

        if block < EXT2_NDIR_BLOCKS as u64 {
            out[0] = block as u32;
            return Some(&out[..1]);
        }

        block -= EXT2_NDIR_BLOCKS as u64;
        if block < ptrs {
            out[0] = EXT2_IND_BLOCK as u32;
            out[1] = block as u32;
            return Some(&out[..2]);
        }

        block -= ptrs;
        if block < (1 << (2 * ptr_bits)) {
            out[0] = EXT2_DIND_BLOCK as u32;
            out[1] = (block >> ptr_bits) as u32;
            out[2] = (block & ptr_mask) as u32;
            return Some(&out[..3]);
        }

        block -= ptrs * ptrs;
        if block < ptrs * ptrs * ptrs {
            out[0] = EXT2_TIND_BLOCK as u32;
            out[1] = (block >> (2 * ptr_bits)) as u32;
            out[2] = ((block >> ptr_bits) & ptr_mask) as u32;
            out[3] = (block & ptr_mask) as u32;
            return Some(&out[..4]);
        }

        None
    }

    fn offset_to_block(inode: &INode<Self>, block: Offset) -> Result<u64> {
        let mut indices = [0u32; 4];
        let boffsets = inode
            .super_block()
            .data()
            .offsets(block as u64, &mut indices)
            .ok_or(EIO)?;
        let mut boffset = inode.data().data_blocks[boffsets[0] as usize];
        for i in &boffsets[1..] {
            let bh = inode.super_block().bread(u64::from(boffset))?;
            let b = bh.data();
            let table = LE::<u32>::from_bytes_to_slice(b).ok_or(EIO)?;
            boffset = table[*i as usize].value();
        }
        Ok(boffset.into())
    }

    fn for_each_block(
        inode: &INode<Self>,
        first: Offset,
        len: Offset,
        mut cb: impl FnMut(&[u8]) -> Result<bool>,
    ) -> Result<()> {
        if first >= inode.size() {
            return Ok(());
        }
        let limit_len = cmp::min(len, inode.size() - first);
        let limit = first.checked_add(limit_len).ok_or(EIO)?;

        let data = inode.super_block().data();
        let block_size = data.block_size as Offset;
        let mut next = first;
        while next < limit {
            let block = next / block_size;
            let avail = cmp::min(block_size - (next % block_size), limit - next);
            let boffset = Self::offset_to_block(inode, block)?;
            let bh = inode.super_block().bread(boffset)?;
            if !cb(&bh.data()[(next % block_size) as usize..][..avail as usize])? {
                break;
            }

            next += avail;
        }

        Ok(())
    }
}

impl fs::FileSystem for Ext2Fs {
    type Data = KBox<Self>;
    type INodeData = INodeData;
    const NAME: &'static CStr = c_str!("rust-ext2");
    const SUPER_TYPE: sb::Type = sb::Type::BlockDev;

    #[allow(clippy::ignored_unit_patterns)]
    fn fill_super(
        _: <Self::Context as Context<Self>>::Data,
        sb: &mut SuperBlock<Self, sb::New>,
        _: Option<inode::Mapper>,
    ) -> Result<Self::Data> {
        let scount = sb.sector_count();
        if scount < (SB_OFFSET + size_of::<Super>() as u64) / SECTOR_SIZE as u64 {
            pr_err!("Block device is too small: sector count={scount}\n");
            return Err(ENXIO);
        }

        let mut folio = Folio::alloc(0)?;
        sb.sread(
            SB_OFFSET / SECTOR_SIZE as u64,
            (size_of::<Super>() + SECTOR_SIZE + 1) / SECTOR_SIZE,
            &mut folio,
        )?;
        let mapped = folio.map(0)?;
        let s = Super::from_bytes(&mapped, 0).ok_or(EIO)?;
        let block_size_bits = s.log_block_size.value();
        let block_size = 1024u64 << block_size_bits;
        let inodes_per_group = s.inodes_per_group.value();
        let inode_count = s.inodes_count.value();
        let inode_size = s.inode_size.value().into();

        if s.first_data_block.value() >= s.blocks_count.value() {
            return Err(ENXIO);
        }

        // TODO: Replicate checks from fs/ext2/super.c.
        let group_count = usize::try_from(
            (s.blocks_count.value() - s.first_data_block.value() - 1) / s.blocks_per_group.value()
                + 1,
        )?;
        drop(mapped);
        // TODO: Do we need this?
        //let gdt_block_offset = SB_OFFSET / block_size + 1;
        let mut groups = Vec::new();
        groups.reserve(group_count, GFP_KERNEL)?;

        let gd_per_page = PAGE_SIZE / size_of::<defs::Group>();
        let mut remain = group_count;
        let mut offset = (SB_OFFSET / block_size + 1) * block_size / SECTOR_SIZE as u64;
        for _ in 0..group_count.div_ceil(gd_per_page) {
            sb.sread(offset, PAGE_SIZE / SECTOR_SIZE, &mut folio)?;
            for g in Group::from_bytes_to_slice(&folio.map(0)?).ok_or(EIO)? {
                pr_info!("Group: {}\n", g.inode_table.value());
                groups.push(*g, GFP_KERNEL)?;
                remain -= 1;
                if remain == 0 {
                    break;
                }
            }
            offset += (PAGE_SIZE / SECTOR_SIZE) as u64;
        }

        Ok(KBox::new(
            Ext2Fs {
                block_size,
                _block_size_bits: block_size_bits,
                inodes_per_group,
                inode_count,
                inode_size,
                group: groups,
            },
            GFP_KERNEL,
        )?)
    }

    fn init_root(sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        let inode = Self::iget(sb, 2)?;
        dentry::Root::try_new(inode)
    }
}

#[vtable]
impl file::Operations for Ext2Dir {
    type FileSystem = Ext2Fs;

    fn seek(file: &File<Ext2Fs>, offset: Offset, whence: file::Whence) -> Result<Offset> {
        file::generic_seek(file, offset, whence)
    }

    fn read(_: &File<Ext2Fs>, _: &mut uaccess::UserSliceWriter, _: &mut Offset) -> Result<usize> {
        Err(EISDIR)
    }

    fn read_dir(
        _file: &File<Ext2Fs>,
        inode: &Locked<&INode<Self::FileSystem>, inode::ReadSem>,
        emitter: &mut file::DirEmitter,
    ) -> Result {
        Ext2Fs::for_each_block(inode, emitter.pos(), Offset::MAX, |data| {
            let mut offset = 0usize;
            let mut acc: Offset = 0;
            while data.len() - offset > size_of::<DirEntry>() {
                let dirent = DirEntry::from_bytes(data, offset).ok_or(EIO)?;
                offset += size_of::<DirEntry>();

                let name_len = usize::from(dirent.name_len);
                if data.len() - offset < name_len {
                    return Err(EIO);
                }

                let name = &data[offset..][..name_len];
                // TODO: Check this.
                offset = offset - size_of::<DirEntry>() + usize::from(dirent.rec_len.value());
                if offset > data.len() {
                    return Err(EIO);
                }

                acc += Offset::from(dirent.rec_len.value());
                let t = match dirent.file_type {
                    defs::FT_REG_FILE => file::DirEntryType::Reg,
                    defs::FT_DIR => file::DirEntryType::Dir,
                    defs::FT_SYMLINK => file::DirEntryType::Lnk,
                    defs::FT_CHRDEV => file::DirEntryType::Chr,
                    defs::FT_BLKDEV => file::DirEntryType::Blk,
                    defs::FT_FIFO => file::DirEntryType::Fifo,
                    defs::FT_SOCK => file::DirEntryType::Sock,
                    _ => continue,
                };

                let ino = dirent.inode.value();
                if ino == 0 {
                    continue;
                }

                if !emitter.emit(acc, name, dirent.inode.value().into(), t) {
                    return Ok(false);
                }
                acc = 0;
            }
            Ok(true)
        })
    }
}

struct Ext2Dir;

#[vtable]
impl inode::Operations for Ext2Dir {
    type FileSystem = Ext2Fs;

    fn lookup(
        parent: &Locked<&INode<Self::FileSystem>, ReadSem>,
        dentry: dentry::Unhashed<'_, Self::FileSystem>,
    ) -> Result<Option<ARef<DEntry<Self::FileSystem>>>> {
        let mut ino = None;

        Ext2Fs::for_each_block(parent, 0, Offset::MAX, |data| {
            let mut offset = 0usize;
            while data.len() - offset > size_of::<DirEntry>() {
                let dirent = DirEntry::from_bytes(data, offset).ok_or(EIO)?;
                offset += size_of::<DirEntry>();

                let name_len = usize::from(dirent.name_len);
                if data.len() - offset < name_len {
                    return Err(EIO);
                }

                let name = &data[offset..][..name_len];

                offset = offset - size_of::<DirEntry>() + usize::from(dirent.rec_len.value());
                if offset > data.len() {
                    return Err(EIO);
                }

                let eino = dirent.inode.value();
                if eino == 0 {
                    continue;
                }

                if name == dentry.name() {
                    ino = Some(eino.into());
                    return Ok(false);
                }
            }
            Ok(true)
        })?;

        // Populate the dentry if found.
        if let Some(v) = ino {
            match Ext2Fs::iget(parent.super_block(), v) {
                Ok(inode) => return dentry.splice_alias(Some(inode)),
                Err(e) => {
                    if e != ENOENT {
                        return Err(e);
                    }
                }
            }
        }

        dentry.splice_alias(None)
    }
}

impl iomap::Operations for Ext2Fs {
    type FileSystem = Self;

    fn begin<'a>(
        inode: &'a INode<Self>,
        pos: Offset,
        length: Offset,
        _flags: u32,
        map: &mut iomap::Map<'a>,
        _srcmap: &mut iomap::Map<'a>,
    ) -> Result {
        let size = inode.size();
        if pos >= size {
            map.set_offset(pos)
                .set_length(length.try_into()?)
                .set_flags(iomap::map_flags::MERGED)
                .set_type(iomap::Type::Hole);
            return Ok(());
        }

        let block_size = inode.super_block().data().block_size as Offset;
        let block = pos / block_size;

        let boffset = Self::offset_to_block(inode, block)?;
        map.set_offset(block * block_size)
            .set_length(block_size as u64)
            .set_flags(iomap::map_flags::MERGED)
            .set_type(iomap::Type::Mapped)
            .set_bdev(Some(inode.super_block().bdev()))
            .set_addr(boffset * block_size as u64);

        Ok(())
    }
}

fn decode_dev(block: &[LE<u32>]) -> (u32, u32) {
    let v = block[0].value();
    if v != 0 {
        ((v >> 8) & 255, v & 255)
    } else {
        let v = block[1].value();
        ((v & 0xfff00) >> 8, (v & 0xff) | ((v >> 12) & 0xfff00))
    }
}
