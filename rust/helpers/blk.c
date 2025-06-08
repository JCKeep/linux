// SPDX-License-Identifier: GPL-2.0

#include <linux/blk-mq.h>
#include <linux/blkdev.h>
#include <linux/buffer_head.h>

void *rust_helper_blk_mq_rq_to_pdu(struct request *rq)
{
	return blk_mq_rq_to_pdu(rq);
}

struct request *rust_helper_blk_mq_rq_from_pdu(void *pdu)
{
	return blk_mq_rq_from_pdu(pdu);
}

sector_t rust_helper_bdev_nr_sectors(struct block_device *bdev)
{
	return bdev_nr_sectors(bdev);
}

struct inode *rust_helper_BD_INODE(struct block_device *bdev)
{
	return BD_INODE(bdev);
}

#ifdef CONFIG_BUFFER_HEAD
struct buffer_head *rust_helper_sb_bread(struct super_block *sb,
					 sector_t block)
{
	return sb_bread(sb, block);
}

void rust_helper_get_bh(struct buffer_head *bh)
{
	get_bh(bh);
}

void rust_helper_put_bh(struct buffer_head *bh)
{
	put_bh(bh);
}
#endif