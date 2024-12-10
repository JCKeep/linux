// SPDX-License-Identifier: GPL-2.0

#include <linux/gfp.h>
#include <linux/highmem.h>

struct page *rust_helper_alloc_pages(gfp_t gfp_mask, unsigned int order)
{
	return alloc_pages(gfp_mask, order);
}

void *rust_helper_kmap_local_page(struct page *page)
{
	return kmap_local_page(page);
}

void rust_helper_kunmap_local(const void *addr)
{
	kunmap_local(addr);
}

unsigned long rust_helper_virt_to_phys(const void *kaddr)
{
	return virt_to_phys((volatile void *)kaddr);
}