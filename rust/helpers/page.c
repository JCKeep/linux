// SPDX-License-Identifier: GPL-2.0

#include <linux/gfp.h>
#include <linux/highmem.h>
#include <linux/pagemap.h>

struct page *rust_helper_alloc_pages(gfp_t gfp_mask, unsigned int order)
{
	return alloc_pages(gfp_mask, order);
}

void *rust_helper_kmap_local_page(struct page *page)
{
	return kmap_local_page(page);
}

void *rust_helper_kmap_local_folio(struct folio *folio, size_t offset)
{
	return kmap_local_folio(folio, offset);
}

void rust_helper_kunmap_local(const void *addr)
{
	kunmap_local(addr);
}

struct folio *rust_helper_read_mapping_folio(struct address_space *mapping,
					     pgoff_t index, struct file *file)
{
	return read_mapping_folio(mapping, index, file);
}

void rust_helper_mapping_set_large_folios(struct address_space *mapping)
{
	mapping_set_large_folios(mapping);
}

void rust_helper_folio_get(struct folio *folio)
{
	folio_get(folio);
}

void rust_helper_folio_put(struct folio *folio)
{
	folio_put(folio);
}

void rust_helper_folio_lock(struct folio *folio)
{
	folio_lock(folio);
}

void rust_helper_folio_mark_uptodate(struct folio *folio)
{
	folio_mark_uptodate(folio);
}

void *rust_helper_kmap(struct page *page)
{
	return kmap(page);
}

void rust_helper_kunmap(struct page *page)
{
	kunmap(page);
}

struct page *rust_helper_folio_page(struct folio *folio, size_t n)
{
	return folio_page(folio, n);
}

loff_t rust_helper_folio_pos(struct folio *folio)
{
	return folio_pos(folio);
}

size_t rust_helper_folio_size(struct folio *folio)
{
	return folio_size(folio);
}

bool rust_helper_folio_test_uptodate(struct folio *folio)
{
	return folio_test_uptodate(folio);
}

bool rust_helper_folio_test_highmem(struct folio *folio)
{
	return folio_test_highmem(folio);
}

struct folio *rust_helper_folio_alloc(gfp_t gfp, unsigned int order)
{
	return folio_alloc(gfp, order);
}