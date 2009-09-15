/* Copyright (c) 2009 The Regents of the University  of California. 
 * See the COPYRIGHT files at the top of this source tree for full 
 * license information.
 * 
 * Kevin Klues <klueska@cs.berkeley.edu>    
 */

#ifdef __SHARC__
#pragma nosharc
#define SINIT(x) x
#endif

#include <sys/queue.h>
#include <page_alloc.h>
#include <pmap.h>
#include <kmalloc.h>

// llc stands for last-level-cache
uint16_t RO llc_num_colors;
spinlock_t colored_page_free_list_lock;

page_list_t LCKD(&colored_page_free_list_lock) * CT(llc_num_colors) RO
  colored_page_free_list = NULL;

static void page_alloc_bootstrap(cache_t RO* llc) {
	// Initialize the properties of the last level cache used by this allocator
	size_t nc = get_cache_num_page_colors(llc);
	llc_num_colors = SINIT(nc);

	// Allocate space for the array required to manage the free lists
	size_t list_size = llc_num_colors*sizeof(page_list_t);
	page_list_t LCKD(&colored_page_free_list_lock)*tmp =
	    (page_list_t*)boot_alloc(list_size,PGSIZE);
	colored_page_free_list = SINIT(tmp);
}

/*
 * Initialize the memory free lists.
 * After this point, ONLY use the functions below
 * to allocate and deallocate physical memory via the 
 * page_free_lists. 
 */
void page_alloc_init() 
{
	cache_t RO* llc = available_caches.llc;

	// First Bootstrap the page alloc process
	static bool RO bootstrapped = FALSE;
	if(!bootstrapped) {
		bootstrapped = SINIT(TRUE);
		page_alloc_bootstrap(llc);
	}

	// Then, initialize the array required to manage the colored page free list
	for(int i=0; i<llc_num_colors; i++) {
		LIST_INIT(&(colored_page_free_list[i]));
	}

	//  Then, mark the pages already in use by the kernel. 
	//  1) Mark page 0 as in use.
	//     This way we preserve the real-mode IDT and BIOS structures
	//     in case we ever need them.  (Currently we don't, but...)
	//  2) Mark the rest of base memory as free.
	//  3) Then comes the IO hole [IOPHYSMEM, EXTPHYSMEM).
	//     Mark it as in use so that it can never be allocated.      
	//  4) Then extended memory [EXTPHYSMEM, ...).
	//     Some of it is in use, some is free.
	int i;
	extern char (SNT RO end)[];
	physaddr_t physaddr_after_kernel = PADDR(PTRROUNDUP(boot_freemem, PGSIZE));

	pages[0].page_ref = 1;
	// alloc the second page, since we will need it later to init the other cores
	// probably need to be smarter about what page we use (make this dynamic) TODO
	pages[1].page_ref = 1;
	for (i = 2; i < PPN(IOPHYSMEM); i++) {
		pages[i].page_ref = 0;
		LIST_INSERT_HEAD(
		   &(colored_page_free_list[get_page_color(page2ppn(&pages[i]), llc)]),
		   &pages[i],
		   page_link
		);
	}
	for (i = PPN(IOPHYSMEM); i < PPN(EXTPHYSMEM); i++) {
		pages[i].page_ref = 1;
	}
	for (i = PPN(EXTPHYSMEM); i < PPN(physaddr_after_kernel); i++) {
		pages[i].page_ref = 1;
	}
	for (i = PPN(physaddr_after_kernel); i < PPN(maxaddrpa); i++) {
		pages[i].page_ref = 0;
		LIST_INSERT_HEAD(
		   &(colored_page_free_list[get_page_color(page2ppn(&pages[i]), llc)]),
		   &pages[i],
		   page_link
		);
	}
	// this block out all memory above maxaddrpa.  will need another mechanism
	// to allocate and map these into the kernel address space
	for (i = PPN(maxaddrpa); i < npages; i++) {
		pages[i].page_ref = 1;
	}
}

