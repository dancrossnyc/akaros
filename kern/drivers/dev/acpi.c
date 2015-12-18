/*
 * This file is part of the UCB release of Plan 9. It is subject to the license
 * terms in the LICENSE file found in the top-level directory of this
 * distribution and at http://akaros.cs.berkeley.edu/files/Plan9License. No
 * part of the UCB release of Plan 9, including this file, may be copied,
 * modified, propagated, or distributed except according to the terms contained
 * in the LICENSE file.
 */

#include <vfs.h>
#include <kfs.h>
#include <slab.h>
#include <kmalloc.h>
#include <kref.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <error.h>
#include <cpio.h>
#include <pmap.h>
#include <smp.h>
#include <ip.h>
#include <ns.h>
#include <acpi.h>

#include "../timers/hpet.h"

#ifdef CONFIG_X86
#include <arch/pci.h>
#endif

/* -----------------------------------------------------------------------------
 * Basic ACPI device.
 *
 * The qid.Path will be made unique by incrementing lastpath. lastpath starts
 * at Qroot.
 *
 * Qtbl will return a pointer to the Atable, which includes the signature, OEM
 * data, and so on.
 *
 * Raw, at any level, dumps the raw table at that level, which by the ACPI
 * flattened tree layout will include all descendents.
 *
 * Qpretty, at any level, will print the pretty form for that level and all
 * descendants.
 */
enum {
	Qroot = 0,

	// The type is the qid.path mod NQtypes.
	Qdir = 0,
	Qpretty,
	Qraw,
	Qtbl,
	NQtypes,
};

#define ATABLEBUFSZ	ROUNDUP(sizeof(struct Atable), 16)

static uint64_t lastpath;
static struct Slice emptyslice;
struct dev acpidevtab;

static char *devname(void)
{
	return acpidevtab.name;
}

/*
 * ACPI 4.0 Support.
 * Still WIP.
 *
 * This driver locates tables and parses only a small subset
 * of tables. All other tables are mapped and kept for the user-level
 * interpreter.
 */
static struct cmdtab ctls[] = {
	{CMregion, "region", 6},
	{CMgpe, "gpe", 3},
};

static struct dirtab acpidir[] = {
	{".", {Qroot, 0, QTDIR}, 0, DMDIR | 0555},
};

static struct Facs *facs;		/* Firmware ACPI control structure */
static struct Fadt *fadt;		/* Fixed ACPI description to reach ACPI regs */
static struct Atable *root;
static struct Xsdt *xsdt;		/* XSDT table */
static struct Atable *tfirst;	/* loaded DSDT/SSDT/... tables */
static struct Atable *tlast;	/* pointer to last table */
struct Atable *apics;			/* APIC info */
struct Atable *srat;			/* System resource affinity used by physalloc */
struct Dmar *dmar;
static struct Slit *slit;		/* Sys locality info table used by scheduler */
static struct Atable *msct;		/* Maximum system characteristics table */
static struct Reg *reg;			/* region used for I/O */
static struct Gpe *gpes;		/* General purpose events */
static int ngpes;

static char *regnames[] = {
	"mem", "io", "pcicfg", "embed",
	"smb", "cmos", "pcibar", "ipmi",
};

/*
 * Lists to store RAM that we copy ACPI tables into. When we map a new
 * ACPI list into the kernel, we copy it into a specifically RAM buffer
 * (to make sure it's not coming from e.g. slow device memory). We store
 * pointers to those buffers on these lists.
 */
struct Acpilist {
	struct Acpilist *next;
	size_t size;
	int8_t raw[];
};

static struct Acpilist *acpilists;

/*
 * A tracking structure for growing lists of Atables during parsing.
 */
struct Slice {
	void **ptrs;
	size_t len;
	size_t size;
};

void slinit(struct Slice *slice)
{
	memset(slice, 0, sizeof(*slice));
}

void slclear(struct Slice *slice)
{
	slice->len = 0;
	memset(slice->ptrs, 0, sizeof(*slice->ptrs) * slice->size);
}

void *slget(struct Slice *slice, size_t i)
{
	if (i >= slice->len)
		return NULL;
	return slice->ptrs[i];
}

void slput(struct Slice *slice, size_t i, void *p)
{
	if (i >= slice->len)
		return;
	slice->ptrs[i] = p;
}

void sldel(struct Slice *slice, size_t i)
{
	if (i >= slice->len)
		return;
	memmove(slice->ptrs + i, slice->ptrs + i + 1,
	        (slice->len - i + 1) * sizeof(void *));
	slice->len--;
}

void append(struct Slice *s, void *p)
{
	if (s->len == s->size) {
		void **ps;
		if (s->size == 0)
			s->size = 4;
		s->size *= 2;
		ps = kreallocarray(s->ptrs, s->size, sizeof(void *), KMALLOC_WAIT);
		assert(ps != NULL);		/* XXX: if size*sizeof(void*) overflows. */
		s->ptrs = ps;
	}
	s->ptrs[s->len] = p;
	s->len++;
}

size_t len(struct Slice *slice) { return slice->len; }

void *finalize(struct Slice *slice)
{
	void **ps;

	ps = kreallocarray(slice->ptrs, slice->len, sizeof(void *), KMALLOC_WAIT);
	assert(ps != NULL);
	slice->len = 0;
	slice->size = 0;
	slice->ptrs = NULL;

	return ps;
}

void sldestroy(struct Slice *slice)
{
	kfree(slice->ptrs);
	slice->ptrs = NULL;
	slice->size = 0;
	slice->len = 0;
}

struct Atable *mkatable(int type, char *name, uint8_t *raw,
						size_t rawsize, size_t addsize)
{
	void *m;
	struct Atable *t;

	m = kzmalloc(ATABLEBUFSZ + addsize, KMALLOC_WAIT);
	if (m == NULL)
		panic("no memory for more aml tables");
	t = m;
	t->tbl = NULL;
	if (addsize != 0)
		t->tbl = m + ATABLEBUFSZ;
	t->rawsize = rawsize;
	t->raw = raw;
	strlcpy(t->name, name, sizeof(t->name));
	mkqid(&t->qid,  lastpath++, 0, DMDIR);
	mkqid(&t->rqid, lastpath++, 0, 0);
	mkqid(&t->pqid, lastpath++, 0, 0);
	mkqid(&t->tqid, lastpath++, 0, 0);

	return t;
}

static struct Atable *finatable(struct Atable *t, struct Slice *slice)
{
	size_t n;
	struct Atable *tail;
	struct dirtab *dirs;

	n = len(slice);
	t->nchildren = n;
	t->children = finalize(slice);
	dirs = kreallocarray(NULL, n + NQtypes, sizeof(struct dirtab),
	                     KMALLOC_WAIT);
	assert(dirs != NULL);
	dirs[0] = (struct dirtab){ ".",      t->qid,   0, 0555 };
	dirs[1] = (struct dirtab){ "pretty", t->pqid,  0, 0444 };
	dirs[2] = (struct dirtab){ "raw",    t->rqid,  0, 0444 };
	dirs[3] = (struct dirtab){ "table",  t->tqid,  0, 0444 };
	for (size_t i = 0; i < n; i++) {
		strlcpy(dirs[i + NQtypes].name, t->children[i]->name, KNAMELEN);
		dirs[i + NQtypes].qid = t->children[i]->qid;
		dirs[i + NQtypes].length = 0;
		dirs[i + NQtypes].perm = 0555;
	}
	t->cdirs = dirs;
	tail = NULL;
	while (n-- > 0) {
		t->children[n]->next = tail;
		tail = t->children[n];
	}

	return t;
}

static char *dumpGas(char *start, char *end, char *prefix, struct Gas *g);
static void dumpxsdt(void);

static char *acpiregstr(int id)
{
	static char buf[20];		/* BUG */

	if (id >= 0 && id < ARRAY_SIZE(regnames)) {
		return regnames[id];
	}
	seprintf(buf, buf + sizeof(buf), "spc:%#x", id);
	return buf;
}

static int acpiregid(char *s)
{
	for (int i = 0; i < ARRAY_SIZE(regnames); i++)
		if (strcmp(regnames[i], s) == 0)
			return i;
	return -1;
}

/*
 * TODO(rminnich): Fix these if we're ever on a different-endian machine.
 * They are specific to little-endian processors and are not portable.
 */
static uint8_t mget8(uintptr_t p, void *unused)
{
	uint8_t *cp = (uint8_t *) p;
	return *cp;
}

static void mset8(uintptr_t p, uint8_t v, void *unused)
{
	uint8_t *cp = (uint8_t *) p;
	*cp = v;
}

static uint16_t mget16(uintptr_t p, void *unused)
{
	uint16_t *cp = (uint16_t *) p;
	return *cp;
}

static void mset16(uintptr_t p, uint16_t v, void *unused)
{
	uint16_t *cp = (uint16_t *) p;
	*cp = v;
}

static uint32_t mget32(uintptr_t p, void *unused)
{
	uint32_t *cp = (uint32_t *) p;
	return *cp;
}

static void mset32(uintptr_t p, uint32_t v, void *unused)
{
	uint32_t *cp = (uint32_t *) p;
	*cp = v;
}

static uint64_t mget64(uintptr_t p, void *unused)
{
	uint64_t *cp = (uint64_t *) p;
	return *cp;
}

static void mset64(uintptr_t p, uint64_t v, void *unused)
{
	uint64_t *cp = (uint64_t *) p;
	*cp = v;
}

static uint8_t ioget8(uintptr_t p, void *unused)
{
	return inb(p);
}

static void ioset8(uintptr_t p, uint8_t v, void *unused)
{
	outb(p, v);
}

static uint16_t ioget16(uintptr_t p, void *unused)
{
	return inw(p);
}

static void ioset16(uintptr_t p, uint16_t v, void *unused)
{
	outw(p, v);
}

static uint32_t ioget32(uintptr_t p, void *unused)
{
	return inl(p);
}

static void ioset32(uintptr_t p, uint32_t v, void *unused)
{
	outl(p, v);
}

/*
 * TODO(rminnich): these cfgs are hacky. Maybe all the struct Reg should have
 * struct pci_device or something?
 */
static uint8_t cfgget8(uintptr_t p, void *r)
{
	struct Reg *ro = r;
	struct pci_device pcidev;

	explode_tbdf(ro->tbdf);
	return pcidev_read8(&pcidev, p);
}

static void cfgset8(uintptr_t p, uint8_t v, void *r)
{
	struct Reg *ro = r;
	struct pci_device pcidev;

	explode_tbdf(ro->tbdf);
	pcidev_write8(&pcidev, p, v);
}

static uint16_t cfgget16(uintptr_t p, void *r)
{
	struct Reg *ro = r;
	struct pci_device pcidev;

	explode_tbdf(ro->tbdf);
	return pcidev_read16(&pcidev, p);
}

static void cfgset16(uintptr_t p, uint16_t v, void *r)
{
	struct Reg *ro = r;
	struct pci_device pcidev;

	explode_tbdf(ro->tbdf);
	pcidev_write16(&pcidev, p, v);
}

static uint32_t cfgget32(uintptr_t p, void *r)
{
	struct Reg *ro = r;
	struct pci_device pcidev;

	explode_tbdf(ro->tbdf);
	return pcidev_read32(&pcidev, p);
}

static void cfgset32(uintptr_t p, uint32_t v, void *r)
{
	struct Reg *ro = r;
	struct pci_device pcidev;

	explode_tbdf(ro->tbdf);
	pcidev_write32(&pcidev, p, v);
}

static struct Regio memio = {
	NULL,
	mget8, mset8, mget16, mset16,
	mget32, mset32, mget64, mset64
};

static struct Regio ioio = {
	NULL,
	ioget8, ioset8, ioget16, ioset16,
	ioget32, ioset32, NULL, NULL
};

static struct Regio cfgio = {
	NULL,
	cfgget8, cfgset8, cfgget16, cfgset16,
	cfgget32, cfgset32, NULL, NULL
};

/*
 * Copy memory, 1/2/4/8-bytes at a time, to/from a region.
 */
static long
regcpy(struct Regio *dio, uintptr_t da, struct Regio *sio,
	   uintptr_t sa, long len, int align)
{
	int n, i;

	printd("regcpy %#p %#p %#p %#p\n", da, sa, len, align);
	if ((len % align) != 0)
		printd("regcpy: bug: copy not aligned. truncated\n");
	n = len / align;
	for (i = 0; i < n; i++) {
		switch (align) {
			case 1:
				printd("cpy8 %#p %#p\n", da, sa);
				dio->set8(da, sio->get8(sa, sio->arg), dio->arg);
				break;
			case 2:
				printd("cpy16 %#p %#p\n", da, sa);
				dio->set16(da, sio->get16(sa, sio->arg), dio->arg);
				break;
			case 4:
				printd("cpy32 %#p %#p\n", da, sa);
				dio->set32(da, sio->get32(sa, sio->arg), dio->arg);
				break;
			case 8:
				printd("cpy64 %#p %#p\n", da, sa);
				warn("Not doing set64 for some reason, fix me!");
				//  dio->set64(da, sio->get64(sa, sio->arg), dio->arg);
				break;
			default:
				panic("regcpy: align bug");
		}
		da += align;
		sa += align;
	}
	return n * align;
}

/*
 * Perform I/O within region in access units of accsz bytes.
 * All units in bytes.
 */
static long regio(struct Reg *r, void *p, uint32_t len, uintptr_t off, int iswr)
{
	struct Regio rio;
	uintptr_t rp;

	printd("reg%s %s %#p %#p %#lx sz=%d\n",
		   iswr ? "out" : "in", r->name, p, off, len, r->accsz);
	rp = 0;
	if (off + len > r->len) {
		printd("regio: access outside limits");
		len = r->len - off;
	}
	if (len <= 0) {
		printd("regio: zero len\n");
		return 0;
	}
	switch (r->spc) {
		case Rsysmem:
			if (r->p == NULL)
				r->p = KADDR_NOCHECK(r->base);
			if (r->p == NULL)
				error(EFAIL, "regio: vmap/KADDR failed");
			rp = (uintptr_t) r->p + off;
			rio = memio;
			break;
		case Rsysio:
			rp = r->base + off;
			rio = ioio;
			break;
		case Rpcicfg:
			rp = r->base + off;
			rio = cfgio;
			rio.arg = r;
			break;
		case Rpcibar:
		case Rembed:
		case Rsmbus:
		case Rcmos:
		case Ripmi:
		case Rfixedhw:
			printd("regio: reg %s not supported\n", acpiregstr(r->spc));
			error(EFAIL, "region not supported");
	}
	if (iswr)
		regcpy(&rio, rp, &memio, (uintptr_t) p, len, r->accsz);
	else
		regcpy(&memio, (uintptr_t) p, &rio, rp, len, r->accsz);
	return len;
}

/*
 * Compute and return SDT checksum: '0' is a correct sum.
 */
static uint8_t sdtchecksum(void *addr, int len)
{
	uint8_t *p, sum;

	sum = 0;
	for (p = addr; len-- > 0; p++)
		sum += *p;

	return sum;
}

static void *sdtmap(uintptr_t pa, size_t *n, int cksum)
{
	struct Sdthdr *sdt;
	struct Acpilist *p;

	if (!pa) {
		printk("sdtmap: NULL pa\n");
		return NULL;
	}
	sdt = KADDR_NOCHECK(pa);
	if (sdt == NULL) {
		printk("acpi: vmap: NULL\n");
		return NULL;
	}
	*n = l32get(sdt->length);
	if (!*n) {
		printk("sdt has zero length: pa = %p, sig = %.4s\n", pa, sdt->sig);
		return NULL;
	}
	if (cksum != 0 && sdtchecksum(sdt, *n) != 0) {
		printk("acpi: SDT: bad checksum. pa = %p, len = %lu\n", pa, *n);
		return NULL;
	}
	p = kzmalloc(sizeof(struct Acpilist) + *n, KMALLOC_WAIT);
	if (p == NULL) {
		panic("sdtmap: memory allocation failed for %lu bytes", *n);
	}
	memmove(p->raw, (void *)sdt, *n);
	p->size = *n;
	p->next = acpilists;
	acpilists = p;

	return p->raw;
}

static int loadfacs(uintptr_t pa)
{
	size_t n;

	facs = sdtmap(pa, &n, 0);
	if (facs == NULL) {
		return -1;
	}
	if (memcmp(facs->sig, "FACS", 4) != 0) {
		facs = NULL;
		return -1;
	}

	/* no unmap */
	printd("acpi: facs: hwsig: %#p\n", facs->hwsig);
	printd("acpi: facs: wakingv: %#p\n", facs->wakingv);
	printd("acpi: facs: flags: %#p\n", facs->flags);
	printd("acpi: facs: glock: %#p\n", facs->glock);
	printd("acpi: facs: xwakingv: %#p\n", facs->xwakingv);
	printd("acpi: facs: vers: %#p\n", facs->vers);
	printd("acpi: facs: ospmflags: %#p\n", facs->ospmflags);
	return 0;
}

static void loaddsdt(uintptr_t pa)
{
	size_t n;
	uint8_t *dsdtp;

	dsdtp = sdtmap(pa, &n, 1);
	if (dsdtp == NULL) {
		return;
	}
}

static void gasget(struct Gas *gas, uint8_t *p)
{
	gas->spc = p[0];
	gas->len = p[1];
	gas->off = p[2];
	gas->accsz = p[3];
	gas->addr = l64get(p + 4);
}

static char *dumpfadt(char *start, char *end, struct Fadt *fp)
{
	if (2 == 0) {
		return NULL;
	}

	start = seprintf(start, end, "acpi: FADT@%p\n", fp);
	start = seprintf(start, end, "acpi: fadt: facs: $%p\n", fp->facs);
	start = seprintf(start, end, "acpi: fadt: dsdt: $%p\n", fp->dsdt);
	start = seprintf(start, end, "acpi: fadt: pmprofile: $%p\n", fp->pmprofile);
	start = seprintf(start, end, "acpi: fadt: sciint: $%p\n", fp->sciint);
	start = seprintf(start, end, "acpi: fadt: smicmd: $%p\n", fp->smicmd);
	start =
		seprintf(start, end, "acpi: fadt: acpienable: $%p\n", fp->acpienable);
	start =
		seprintf(start, end, "acpi: fadt: acpidisable: $%p\n", fp->acpidisable);
	start = seprintf(start, end, "acpi: fadt: s4biosreq: $%p\n", fp->s4biosreq);
	start = seprintf(start, end, "acpi: fadt: pstatecnt: $%p\n", fp->pstatecnt);
	start =
		seprintf(start, end, "acpi: fadt: pm1aevtblk: $%p\n", fp->pm1aevtblk);
	start =
		seprintf(start, end, "acpi: fadt: pm1bevtblk: $%p\n", fp->pm1bevtblk);
	start =
		seprintf(start, end, "acpi: fadt: pm1acntblk: $%p\n", fp->pm1acntblk);
	start =
		seprintf(start, end, "acpi: fadt: pm1bcntblk: $%p\n", fp->pm1bcntblk);
	start = seprintf(start, end, "acpi: fadt: pm2cntblk: $%p\n", fp->pm2cntblk);
	start = seprintf(start, end, "acpi: fadt: pmtmrblk: $%p\n", fp->pmtmrblk);
	start = seprintf(start, end, "acpi: fadt: gpe0blk: $%p\n", fp->gpe0blk);
	start = seprintf(start, end, "acpi: fadt: gpe1blk: $%p\n", fp->gpe1blk);
	start = seprintf(start, end, "acpi: fadt: pm1evtlen: $%p\n", fp->pm1evtlen);
	start = seprintf(start, end, "acpi: fadt: pm1cntlen: $%p\n", fp->pm1cntlen);
	start = seprintf(start, end, "acpi: fadt: pm2cntlen: $%p\n", fp->pm2cntlen);
	start = seprintf(start, end, "acpi: fadt: pmtmrlen: $%p\n", fp->pmtmrlen);
	start =
		seprintf(start, end, "acpi: fadt: gpe0blklen: $%p\n", fp->gpe0blklen);
	start =
		seprintf(start, end, "acpi: fadt: gpe1blklen: $%p\n", fp->gpe1blklen);
	start = seprintf(start, end, "acpi: fadt: gp1base: $%p\n", fp->gp1base);
	start = seprintf(start, end, "acpi: fadt: cstcnt: $%p\n", fp->cstcnt);
	start = seprintf(start, end, "acpi: fadt: plvl2lat: $%p\n", fp->plvl2lat);
	start = seprintf(start, end, "acpi: fadt: plvl3lat: $%p\n", fp->plvl3lat);
	start = seprintf(start, end, "acpi: fadt: flushsz: $%p\n", fp->flushsz);
	start =
		seprintf(start, end, "acpi: fadt: flushstride: $%p\n", fp->flushstride);
	start = seprintf(start, end, "acpi: fadt: dutyoff: $%p\n", fp->dutyoff);
	start = seprintf(start, end, "acpi: fadt: dutywidth: $%p\n", fp->dutywidth);
	start = seprintf(start, end, "acpi: fadt: dayalrm: $%p\n", fp->dayalrm);
	start = seprintf(start, end, "acpi: fadt: monalrm: $%p\n", fp->monalrm);
	start = seprintf(start, end, "acpi: fadt: century: $%p\n", fp->century);
	start =
		seprintf(start, end, "acpi: fadt: iapcbootarch: $%p\n",
				 fp->iapcbootarch);
	start = seprintf(start, end, "acpi: fadt: flags: $%p\n", fp->flags);
	start = dumpGas(start, end, "acpi: fadt: resetreg: ", &fp->resetreg);
	start = seprintf(start, end, "acpi: fadt: resetval: $%p\n", fp->resetval);
	start = seprintf(start, end, "acpi: fadt: xfacs: %p\n", fp->xfacs);
	start = seprintf(start, end, "acpi: fadt: xdsdt: %p\n", fp->xdsdt);
	start = dumpGas(start, end, "acpi: fadt: xpm1aevtblk:", &fp->xpm1aevtblk);
	start = dumpGas(start, end, "acpi: fadt: xpm1bevtblk:", &fp->xpm1bevtblk);
	start = dumpGas(start, end, "acpi: fadt: xpm1acntblk:", &fp->xpm1acntblk);
	start = dumpGas(start, end, "acpi: fadt: xpm1bcntblk:", &fp->xpm1bcntblk);
	start = dumpGas(start, end, "acpi: fadt: xpm2cntblk:", &fp->xpm2cntblk);
	start = dumpGas(start, end, "acpi: fadt: xpmtmrblk:", &fp->xpmtmrblk);
	start = dumpGas(start, end, "acpi: fadt: xgpe0blk:", &fp->xgpe0blk);
	start = dumpGas(start, end, "acpi: fadt: xgpe1blk:", &fp->xgpe1blk);
	return start;
}

static struct Atable *parsefadt(char *name, uint8_t *p, size_t rawsize)
{
	struct Atable *t;
	struct Fadt *fp;

	t = mkatable(FADT, name, p, rawsize, sizeof(struct Fadt));

	if (rawsize < 116) {
		printk("ACPI: unusually short FADT, aborting!\n");
		return t;
	}
	/* for now, keep the globals. We'll get rid of them later. */
	fp = t->tbl;
	fadt = fp;
	fp->facs = l32get(p + 36);
	fp->dsdt = l32get(p + 40);
	fp->pmprofile = p[45];
	fp->sciint = l16get(p + 46);
	fp->smicmd = l32get(p + 48);
	fp->acpienable = p[52];
	fp->acpidisable = p[53];
	fp->s4biosreq = p[54];
	fp->pstatecnt = p[55];
	fp->pm1aevtblk = l32get(p + 56);
	fp->pm1bevtblk = l32get(p + 60);
	fp->pm1acntblk = l32get(p + 64);
	fp->pm1bcntblk = l32get(p + 68);
	fp->pm2cntblk = l32get(p + 72);
	fp->pmtmrblk = l32get(p + 76);
	fp->gpe0blk = l32get(p + 80);
	fp->gpe1blk = l32get(p + 84);
	fp->pm1evtlen = p[88];
	fp->pm1cntlen = p[89];
	fp->pm2cntlen = p[90];
	fp->pmtmrlen = p[91];
	fp->gpe0blklen = p[92];
	fp->gpe1blklen = p[93];
	fp->gp1base = p[94];
	fp->cstcnt = p[95];
	fp->plvl2lat = l16get(p + 96);
	fp->plvl3lat = l16get(p + 98);
	fp->flushsz = l16get(p + 100);
	fp->flushstride = l16get(p + 102);
	fp->dutyoff = p[104];
	fp->dutywidth = p[105];
	fp->dayalrm = p[106];
	fp->monalrm = p[107];
	fp->century = p[108];
	fp->iapcbootarch = l16get(p + 109);
	fp->flags = l32get(p + 112);

	/*
	 * qemu gives us a 116 byte fadt, though i haven't seen any HW do that.
	 * The right way to do this is to realloc the table and fake it out.
	 */
	if (rawsize < 244)
		return t;

	gasget(&fp->resetreg, p + 116);
	fp->resetval = p[128];
	fp->xfacs = l64get(p + 132);
	fp->xdsdt = l64get(p + 140);
	gasget(&fp->xpm1aevtblk, p + 148);
	gasget(&fp->xpm1bevtblk, p + 160);
	gasget(&fp->xpm1acntblk, p + 172);
	gasget(&fp->xpm1bcntblk, p + 184);
	gasget(&fp->xpm2cntblk, p + 196);
	gasget(&fp->xpmtmrblk, p + 208);
	gasget(&fp->xgpe0blk, p + 220);
	gasget(&fp->xgpe1blk, p + 232);

	if (fp->xfacs != 0)
		loadfacs(fp->xfacs);
	else
		loadfacs(fp->facs);

	if (fp->xdsdt == (uint64_t)fp->dsdt)	/* acpica */
		loaddsdt(fp->xdsdt);
	else
		loaddsdt(fp->dsdt);
	finatable(t, &emptyslice);

	return t;
}

static char *dumpmsct(char *start, char *end, struct Atable *table)
{
	struct Msct *msct;

	if (!table)
		return start;
	msct = table->tbl;
	if (!msct)
		return start;

	start = seprintf(start, end, "acpi: msct: %d doms %d clkdoms %#p maxpa\n",
					 msct->ndoms, msct->nclkdoms, msct->maxpa);
	for (int i = 0; i < table->nchildren; i++) {
		struct Atable *domtbl = table->children[i]->tbl;
		struct Mdom *st = domtbl->tbl;
		start = seprintf(start, end, "\t[%d:%d] %d maxproc %#p maxmmem\n",
						 st->start, st->end, st->maxproc, st->maxmem);
	}
	start = seprintf(start, end, "\n");

	return start;
}

/*
 * XXX: should perhaps update our idea of available memory.
 * Else we should remove this code.
 */
static struct Atable *parsemsct(char *name, uint8_t *raw, size_t rawsize)
{
	struct Atable *t;
	struct Msct *msct;
	uint8_t *r, *re;
	struct Mdom **stl, *st;
	size_t off, nmdom;
	int i;

	re = raw + rawsize;
	off = l32get(raw + 36);
	nmdom = 0;
	for (r = raw + off, re = raw + rawsize; r < re; r += 22)
		nmdom++;
	t = mkatable(MSCT, name, raw, rawsize,
	             sizeof(struct Msct) + nmdom * sizeof(struct Mdom));
	msct = t->tbl;
	msct->ndoms = l32get(raw + 40) + 1;
	msct->nclkdoms = l32get(raw + 44) + 1;
	msct->maxpa = l64get(raw + 48);
	msct->nmdom = nmdom;
	msct->dom = NULL;
	if (nmdom != 0)
		msct->dom = (void *)msct + sizeof(struct Msct);
	for (i = 0, r = raw; i < nmdom; i++, r += 22) {
		msct->dom[i].start = l32get(r + 2);
		msct->dom[i].end = l32get(r + 6);
		msct->dom[i].maxproc = l32get(r + 10);
		msct->dom[i].maxmem = l64get(r + 14);
	}
	finatable(t, &emptyslice);

	return t;
}

static char *dmartype[] = {"DRHD", "RMRR", "ATSR", "RHSA", "ANDD", };

/* TODO(rminnich): only handles on IOMMU for now. */
static char *dumpdmar(char *start, char *end, struct Dmar *dt)
{
	if (dmar == NULL)
		return start;
	start = seprintf(start, end, "acpi: DMAR@%p:\n", dt);
	start = seprintf(start, end,
			 "\tdmar: intr_remap %d haw %d entries %d\n",
			 dmar->intr_remap, dmar->haw, dt->numentry);
	for(int i = 0; i < dt->numentry; i++) {
		struct Dtab *dtab = &dt->dtab[i];
		int t = dtab->type;
		start = seprintf(start, end, "\t%s: ", dmartype[t]);
		// TODO: function pointers in an array? probably. */
		switch(t) {
		case DRHD:
			start = seprintf(start, end, "%s 0x%02x 0x%016x\n",
							 dtab->drhd.all & 1 ? "INCLUDE_PCI_ALL" : "Scoped",
							 dtab->drhd.segment, dtab->drhd.base);
			break;
		default:
			start = seprintf(start, end, "Unsupported: type %t\n", t);
			break;
		}
	}
	return start;
}

static char *dumpsrat(char *start, char *end, struct Atable *table)
{
	start = seprintf(start, end, "acpi: SRAT@%p:\n", table->tbl);
	for (; table != NULL; table = table->next) {
		struct Srat *st = table->tbl;
		switch (st->type) {
			case SRlapic:
				start =
					seprintf(start, end,
							 "\tlapic: dom %d apic %d sapic %d clk %d\n",
							 st->lapic.dom, st->lapic.apic, st->lapic.sapic,
							 st->lapic.clkdom);
				break;
			case SRmem:
				start = seprintf(start, end, "\tmem: dom %d %#p %#p %c%c\n",
								 st->mem.dom, st->mem.addr, st->mem.len,
								 st->mem.hplug ? 'h' : '-',
								 st->mem.nvram ? 'n' : '-');
				break;
			case SRlx2apic:
				start =
					seprintf(start, end, "\tlx2apic: dom %d apic %d clk %d\n",
							 st->lx2apic.dom, st->lx2apic.apic,
							 st->lx2apic.clkdom);
				break;
			default:
				start = seprintf(start, end, "\t<unknown srat entry>\n");
		}
	}
	start = seprintf(start, end, "\n");
	return start;
}

static struct Atable *parsesrat(char *name, uint8_t *p, size_t rawsize)
{

	struct Atable *t, *tt, *tail;
	uint8_t *pe;
	int stlen, flags;
	struct Slice slice;
	char buf[16];
	int i;
	struct Srat *st;

	if (srat != NULL) {
		panic("acpi: two SRATs?\n");
	}

	t = mkatable(SRAT, name, p, rawsize, 0);
	slinit(&slice);
	pe = p + rawsize;
	for (p += 48, i = 0; p < pe; p += stlen, i++) {
		snprintf(buf, sizeof(buf), "%d", i);
		stlen = p[1];
		tt = mkatable(SRAT, buf, p, stlen, sizeof(struct Srat));
		st = tt->tbl;
		st->type = p[0];
		switch (st->type) {
			case SRlapic:
				st->lapic.dom = p[2] | p[9] << 24 | p[10] << 16 | p[11] << 8;
				st->lapic.apic = p[3];
				st->lapic.sapic = p[8];
				st->lapic.clkdom = l32get(p + 12);
				if (l32get(p + 4) == 0) {
					kfree(tt);
					tt = NULL;
				}
				break;
			case SRmem:
				st->mem.dom = l32get(p + 2);
				st->mem.addr = l64get(p + 8);
				st->mem.len = l64get(p + 16);
				flags = l32get(p + 28);
				if ((flags & 1) == 0) {	/* not enabled */
					kfree(tt);
					tt = NULL;
				} else {
					st->mem.hplug = flags & 2;
					st->mem.nvram = flags & 4;
				}
				break;
			case SRlx2apic:
				st->lx2apic.dom = l32get(p + 4);
				st->lx2apic.apic = l32get(p + 8);
				st->lx2apic.clkdom = l32get(p + 16);
				if (l32get(p + 12) == 0) {
					kfree(tt);
					tt = NULL;
				}
				break;
			default:
				printd("unknown SRAT structure\n");
				kfree(tt);
				tt = NULL;
				break;
		}
		if (tt != NULL)
			append(&slice, tt);
	}
	srat = finatable(t, &slice);

	return srat;
}

static char *dumpslit(char *start, char *end, struct Slit *sl)
{
	int i;

	if (!sl)
		return start;
	start = seprintf(start, end, "acpi slit:\n");
	for (i = 0; i < sl->rowlen * sl->rowlen; i++) {
		start = seprintf(start, end,
						 "slit: %ux\n",
						 sl->e[i / sl->rowlen][i % sl->rowlen].dist);
	}
	start = seprintf(start, end, "\n");
	return start;
}

static int cmpslitent(void *v1, void *v2)
{
	struct SlEntry *se1, *se2;

	se1 = v1;
	se2 = v2;
	return se1->dist - se2->dist;
}

static struct Atable *parseslit(char *name, uint8_t *raw, size_t rawsize)
{
	struct Atable *t;
	uint8_t *r, *re;
	int i, j, k;
	struct SlEntry *se;
	size_t addsize, rowlen;
	void *p;

	addsize = sizeof(*slit);
	rowlen = l64get(raw + 36);
	addsize += rowlen * sizeof(struct SlEntry *);
	addsize += sizeof(struct SlEntry) * rowlen * rowlen;

	t = mkatable(SLIT, name, raw, rawsize, addsize);
	slit = t->tbl;
	slit->rowlen = rowlen;
	p = (void *)slit + sizeof(*slit);
	slit->e = p;
	p += rowlen * sizeof(struct SlEntry *);
	for (i = 0; i < rowlen; i++) {
		slit->e[i] = p;
		p += sizeof(struct SlEntry) * rowlen;
	}
	for (i = 0, r = raw + 44, re = raw + rawsize; r < re; r++, i++) {
		int j = i / rowlen;
		int k = i % rowlen;
		se = &slit->e[j][k];
		se->dom = k;
		se->dist = *r;
	}

#if 0
	/* TODO: might need to sort this shit */
	for (i = 0; i < slit->rowlen; i++)
		qsort(slit->e[i], slit->rowlen, sizeof(slit->e[0][0]), cmpslitent);
#endif
	finatable(t, &emptyslice);

	return t;
}

uintptr_t acpimblocksize(uintptr_t addr, int *dom)
{
	struct Atable *tl;

	for (tl = srat; tl != NULL; tl = tl->next) {
		struct Srat *sl = tl->tbl;
		if (sl->type == SRmem)
			if (sl->mem.addr <= addr && sl->mem.addr + sl->mem.len > addr) {
				*dom = sl->mem.dom;
				return sl->mem.len - (addr - sl->mem.addr);
			}
	}

	return 0;
}

int pickcore(int mycolor, int index)
{
	int color;
	int ncorepercol;

	if (slit == NULL) {
		return 0;
	}
	ncorepercol = num_cores / slit->rowlen;
	color = slit->e[mycolor][index / ncorepercol].dom;
	return color * ncorepercol + index % ncorepercol;
}

static char *polarity[4] = {
	"polarity/trigger like in ISA",
	"active high",
	"BOGUS POLARITY",
	"active low"
};

static char *trigger[] = {
	"BOGUS TRIGGER",
	"edge",
	"BOGUS TRIGGER",
	"level"
};

static char *printiflags(char *start, char *end, int flags)
{

	return seprintf(start, end, "[%s,%s]",
					polarity[flags & AFpmask], trigger[(flags & AFtmask) >> 2]);
}

static char *dumpmadt(char *start, char *end, struct Atable *apics)
{
	struct Madt *mt;

	mt = apics->tbl;
	if (mt == NULL) {
		return seprintf(start, end, "acpi: no MADT");
	}
	start = seprintf(start, end, "acpi: MADT@%p: lapic paddr %p pcat %d:\n",
	                 mt, mt->lapicpa, mt->pcat);
	for (int i = 0; i < apics->nchildren; i++) {
		struct Atable *apic = apics->children[i];
		struct Apicst *st = apic->tbl;
		switch (st->type) {
			case ASlapic:
				start =
					seprintf(start, end, "\tlapic pid %d id %d\n",
							 st->lapic.pid, st->lapic.id);
				break;
			case ASioapic:
			case ASiosapic:
				start =
					seprintf(start, end,
							 "\tioapic id %d addr %p ibase %d\n",
							 st->ioapic.id, st->ioapic.addr, st->ioapic.ibase);
				break;
			case ASintovr:
				start =
					seprintf(start, end, "\tintovr irq %d intr %d flags $%p",
							 st->intovr.irq, st->intovr.intr, st->intovr.flags);
				start = printiflags(start, end, st->intovr.flags);
				start = seprintf(start, end, "\n");
				break;
			case ASnmi:
				start = seprintf(start, end, "\tnmi intr %d flags $%p\n",
								 st->nmi.intr, st->nmi.flags);
				break;
			case ASlnmi:
				start =
					seprintf(start, end, "\tlnmi pid %d lint %d flags $%p\n",
							 st->lnmi.pid, st->lnmi.lint, st->lnmi.flags);
				break;
			case ASlsapic:
				start =
					seprintf(start, end,
							 "\tlsapic pid %d id %d eid %d puid %d puids %s\n",
							 st->lsapic.pid, st->lsapic.id, st->lsapic.eid,
							 st->lsapic.puid, st->lsapic.puids);
				break;
			case ASintsrc:
				start =
					seprintf(start, end,
							 "\tintr type %d pid %d peid %d iosv %d intr %d %#x\n",
							 st->type, st->intsrc.pid, st->intsrc.peid,
							 st->intsrc.iosv, st->intsrc.intr,
							 st->intsrc.flags);
				start = printiflags(start, end, st->intsrc.flags);
				start = seprintf(start, end, "\n");
				break;
			case ASlx2apic:
				start =
					seprintf(start, end, "\tlx2apic puid %d id %d\n",
							 st->lx2apic.puid, st->lx2apic.id);
				break;
			case ASlx2nmi:
				start =
					seprintf(start, end, "\tlx2nmi puid %d intr %d flags $%p\n",
							 st->lx2nmi.puid, st->lx2nmi.intr,
							 st->lx2nmi.flags);
				break;
			default:
				start = seprintf(start, end, "\t<unknown madt entry>\n");
		}
	}
	start = seprintf(start, end, "\n");
	return start;
}

static struct Atable *parsemadt(char *name, uint8_t *p, size_t size)
{
	struct Atable *t, *tt, *tail;
	uint8_t *pe;
	struct Madt *mt;
	struct Apicst *st, *l;
	int id;
	size_t stlen;
	char buf[16];
	int i;
	struct Slice slice;

	slinit(&slice);
	t = mkatable(MADT, name, p, size, sizeof(struct Madt));
	mt = t->tbl;
	mt->lapicpa = l32get(p + 36);
	mt->pcat = l32get(p + 40);
	pe = p + size;
	for (p += 44, i = 0; p < pe; p += stlen, i++) {
		snprintf(buf, sizeof(buf), "%d", i);
		stlen = p[1];
		tt = mkatable(APIC, buf, p, stlen, sizeof(struct Apicst));
		st = tt->tbl;
		st->type = p[0];
		switch (st->type) {
			case ASlapic:
				st->lapic.pid = p[2];
				st->lapic.id = p[3];
				if (l32get(p + 4) == 0) {
					kfree(tt);
					tt = NULL;
				}
				break;
			case ASioapic:
				st->ioapic.id = id = p[2];
				st->ioapic.addr = l32get(p + 4);
				st->ioapic.ibase = l32get(p + 8);
				/* ioapic overrides any ioapic entry for the same id */
				for (int i = 0; i < len(&slice); i++) {
					l = ((struct Atable *)slget(&slice, i))->tbl;
					if (l->type == ASiosapic && l->iosapic.id == id) {
						st->ioapic = l->iosapic;
						/* we leave it linked; could be removed */
						break;
					}
				}
				break;
			case ASintovr:
				st->intovr.irq = p[3];
				st->intovr.intr = l32get(p + 4);
				st->intovr.flags = l16get(p + 8);
				break;
			case ASnmi:
				st->nmi.flags = l16get(p + 2);
				st->nmi.intr = l32get(p + 4);
				break;
			case ASlnmi:
				st->lnmi.pid = p[2];
				st->lnmi.flags = l16get(p + 3);
				st->lnmi.lint = p[5];
				break;
			case ASladdr:
				/* This is for 64 bits, perhaps we should not
				 * honor it on 32 bits.
				 */
				mt->lapicpa = l64get(p + 8);
				break;
			case ASiosapic:
				id = st->iosapic.id = p[2];
				st->iosapic.ibase = l32get(p + 4);
				st->iosapic.addr = l64get(p + 8);
				/* iosapic overrides any ioapic entry for the same id */
				for (int i = 0; i < len(&slice); i++) {
					l = ((struct Atable*)slget(&slice, i))->tbl;
					if (l->type == ASioapic && l->ioapic.id == id) {
						l->ioapic = st->iosapic;
						kfree(tt);
						tt = NULL;
						break;
					}
				}
				break;
			case ASlsapic:
				st->lsapic.pid = p[2];
				st->lsapic.id = p[3];
				st->lsapic.eid = p[4];
				st->lsapic.puid = l32get(p + 12);
				if (l32get(p + 8) == 0) {
					kfree(tt);
					tt = NULL;
				} else
					kstrdup(&st->lsapic.puids, (char *)p + 16);
				break;
			case ASintsrc:
				st->intsrc.flags = l16get(p + 2);
				st->type = p[4];
				st->intsrc.pid = p[5];
				st->intsrc.peid = p[6];
				st->intsrc.iosv = p[7];
				st->intsrc.intr = l32get(p + 8);
				st->intsrc.any = l32get(p + 12);
				break;
			case ASlx2apic:
				st->lx2apic.id = l32get(p + 4);
				st->lx2apic.puid = l32get(p + 12);
				if (l32get(p + 8) == 0) {
					kfree(tt);
					tt = NULL;
				}
				break;
			case ASlx2nmi:
				st->lx2nmi.flags = l16get(p + 2);
				st->lx2nmi.puid = l32get(p + 4);
				st->lx2nmi.intr = p[8];
				break;
			default:
				printd("unknown APIC structure\n");
				kfree(tt);
				tt = NULL;
		}
		if (tt != NULL)
			append(&slice, tt);
	}
	apics = finatable(t, &slice);

	return apics;
}

/*
 * one function for each type of scope.
 */
static void dscopes(uint8_t *p, struct Dtab *dtab, int tablen)
{
	int i;
	int curoffset = 0;
	dtab->drhd.nscope = 0;
	printk("dscopes@%p, %d scopes: ", &p[curoffset], tablen - curoffset);
	hexdump(&p[curoffset], tablen - curoffset);
	for(i = curoffset; i < tablen; i += 4){
		/* this is PAINFUL. We read the tbdf, look it up, read
		 * the next scope, look that up w.r.t the one we have,
		 * blah blah. Who designs this stuff? */
	}

}

static int dtab(uint8_t *p, struct Dtab *dtab)
{
	int len;
	dtab->type = l16get(p);
	p += 2;
	len = l16get(p);
	p += 2;
	switch(dtab->type) {
	case DRHD:
		dtab->drhd.all = p[0] & 1;
		p++;
		p++; /* reserved */
		dtab->drhd.segment = l16get(p);
		p += 2;
		dtab->drhd.base = l64get(p);
		p += 8;
		/* NOTE: if all is set, there should be no scopes of type
		 * This being ACPI, where vendors randomly copy tables
		 * from one system to another, and creating breakage,
		 * anything is possible. But we'll warn them.
		 */
		dscopes(p, dtab, len);
		break;
	default:
		break;
	}

	/* N.B. We always skip over any unprocessed bits. */
	return len;
}

static struct Atable *parsedmar(char *name, uint8_t *raw, size_t rawsize)
{
	struct Atable *t;

	t = mkatable(DMAR, name, raw, rawsize, 0);

	return finatable(t, &emptyslice);

#if 0
	int i;
	int baselen = len > 38 ? 38 : len;
	int nentry, off;

	/* count the entries */
	for (nentry = 0, off = 48; off < len; nentry++) {
		int dslen = p[off+2]|(p[off+3]<<8);
		printk("@%d it is %p 0x%x/0x%x\n",
			   nentry, p, p[off]|(p[off+1]<<8), dslen);
		off = off + dslen;
	}
	printk("DMAR: %d entries\n", nentry);
	a->tbl = dmar = kzmalloc(sizeof(*dmar) + nentry * sizeof(dmar->dtab[0]), 1);
	dmar->numentry = nentry;
	/* the table can be only partly filled. Don't we all love ACPI?
	 * No, we f@@@ing hate it.
	 */
	if (baselen >= 38 && p[37] &1 1) {
		dmar->intr_remap = 1;
	if (baselen >= 37)
		dmar->haw = p[36] + 1;
	/* now we get to walk all the 2 byte elements, ain't it
	 * grand.
	 */
	for(off = 48, i = 0; i < nentry; i++) {
		int dslen = p[2+off]|(p[off+3]<<8);
		printk("@%d it is %p 0x%x/0x%x\n",
			   i, &p[off], p[off]|(p[off+1]<<8), dslen);
		dtab(&p[off], &dmar->dtab[i]);
		off += dslen;
	}
#endif
}

/*
 * Map the table and keep it there.
 */
static struct Atable *parsessdt(char *name, uint8_t *raw, size_t size)
{
	struct Atable *t;
	struct Sdthdr *h;

	/*
	 * We found it and it is too small.
	 * Simply return with no side effect.
	 */
	if (size < Sdthdrsz) {
		return NULL;
	}
	t = mkatable(SSDT, name, raw, size, 0);
	h = (struct Sdthdr *)raw;
	memmove(t->name, h->sig, sizeof(h->sig));
	t->name[sizeof(h->sig)] = '\0';

	return finatable(t, &emptyslice);
}

static char *dumptable(char *start, char *end, char *sig, uint8_t *p, int l)
{
	int n, i;

	if (2 > 1) {
		start = seprintf(start, end, "%s @ %#p\n", sig, p);
		if (2 > 2)
			n = l;
		else
			n = 256;
		for (i = 0; i < n; i++) {
			if ((i % 16) == 0)
				start = seprintf(start, end, "%x: ", i);
			start = seprintf(start, end, " %2.2ux", p[i]);
			if ((i % 16) == 15)
				start = seprintf(start, end, "\n");
		}
		start = seprintf(start, end, "\n");
		start = seprintf(start, end, "\n");
	}
	return start;
}

static char *seprinttable(char *s, char *e, struct Atable *t)
{
	uint8_t *p;
	int i, n;

	p = (uint8_t *)t->tbl;	/* include header */
	n = t->rawsize;
	s = seprintf(s, e, "%s @ %#p\n", t->name, p);
	for (i = 0; i < n; i++) {
		if ((i % 16) == 0)
			s = seprintf(s, e, "%x: ", i);
		s = seprintf(s, e, " %2.2ux", p[i]);
		if ((i % 16) == 15)
			s = seprintf(s, e, "\n");
	}
	return seprintf(s, e, "\n\n");
}

static void *rsdsearch(char *signature)
{
	uintptr_t p;
	uint8_t *bda;
	void *rsd;

	/*
	 * Search for the data structure signature:
	 * 1) in the BIOS ROM between 0xE0000 and 0xFFFFF.
	 */
	return sigscan(KADDR(0xE0000), 0x20000, signature);
}

/*
 * Note: some of this comment is from the unfinished user interpreter.
 *
 * The DSDT is always given to the user interpreter.
 * Tables listed here are also loaded from the XSDT:
 * MSCT, MADT, and FADT are processed by us, because they are
 * required to do early initialization before we have user processes.
 * Other tables are given to the user level interpreter for
 * execution.
 *
 * These historically returned a value to tell acpi whether or not it was okay
 * to unmap the table.  (return 0 means there was no table, meaning it was okay
 * to unmap).  We just use the kernbase mapping, so it's irrelevant.
 *
 * N.B. The intel source code defines the constants for ACPI in a
 * non-endian-independent manner. Rather than bring in the huge wad o' code
 * that represents, we just the names.
 */
struct Parser {
	char *sig;
	struct Atable *(*parse)(char *name, uint8_t *raw, size_t rawsize);
};


static struct Parser ptable[] = {
	{"FACP", parsefadt},
	{"APIC", parsemadt},
	{"DMAR", parsedmar},
	{"SRAT", parsesrat},
	{"SLIT", parseslit},
	{"MSCT", parsemsct},
	{"SSDT", parsessdt},
//	{"HPET", acpihpet},
};

/*
 * process xsdt table and load tables with sig, or all if NULL.
 * (XXX: should be able to search for sig, oemid, oemtblid)
 */
static void parsexsdt(struct Atable *root)
{
	struct Sdthdr *sdt;
	struct Atable *table;
	struct Slice slice;
	ERRSTACK(1);
	size_t l, end;
	uintptr_t dhpa;
	struct Atable *n;
	uint8_t *tbl;

	slinit(&slice);
	if (waserror()) {
		sldestroy(&slice);
		return;
	}

	tbl = xsdt->p + sizeof(struct Sdthdr);
	end = xsdt->len - sizeof(struct Sdthdr);
	for (int i = 0; i < end; i += xsdt->asize) {
		dhpa = (xsdt->asize == 8) ? l64get(tbl + i) : l32get(tbl + i);
		if ((sdt = sdtmap(dhpa, &l, 1)) == NULL)
			continue;
		printd("acpi: %s addr %#p\n", tsig, sdt);
		for (int j = 0; j < ARRAY_SIZE(ptable); j++) {
			if (memcmp(sdt->sig, ptable[j].sig, sizeof(sdt->sig)) == 0) {
				table = ptable[j].parse(ptable[j].sig, (void *)sdt, l);
				if (table != NULL) {
					table->parent = root;
					append(&slice, table);
				}
				break;
			}
		}
	}
	finatable(root, &slice);
}

static void parsersdptr(void)
{
	struct Rsdp *rsd;
	int asize, cksum;
	uintptr_t sdtpa;

	static_assert(sizeof(struct Sdthdr) == 36);

	/* Find the root pointer. */
	if ((rsd = rsdsearch("RSD PTR ")) == NULL) {
		printk("NO RSDP\n");
		return;
	}

	/*
	 * Initialize the root of ACPI parse tree.
	 */
	lastpath = Qroot;
	root = mkatable(XSDT, ".", NULL, 0, sizeof(struct Xsdt));
	root->parent = root;

	printd("/* RSDP */ struct Rsdp = {%08c, %x, %06c, %x, %p, %d, %p, %x}\n",
		   rsd->signature, rsd->rchecksum, rsd->oemid, rsd->revision,
		   *(uint32_t *)rsd->raddr, *(uint32_t *)rsd->length,
		   *(uint32_t *)rsd->xaddr, rsd->xchecksum);

	printd("acpi: RSD PTR@ %#p, physaddr $%p length %ud %#llux rev %d\n",
		   rsd, l32get(rsd->raddr), l32get(rsd->length),
		   l64get(rsd->xaddr), rsd->revision);

	if (rsd->revision >= 2) {
		cksum = sdtchecksum(rsd, 36);
		if (cksum != 0) {
			printk("acpi: bad RSD checksum %d, 64 bit parser aborted\n", cksum);
			return;
		}
		sdtpa = l64get(rsd->xaddr);
		asize = 8;
	} else {
		cksum = sdtchecksum(rsd, 20);
		if (cksum != 0) {
			printk("acpi: bad RSD checksum %d, 32 bit parser aborted\n", cksum);
			return;
		}
		sdtpa = l32get(rsd->raddr);
		asize = 4;
	}

	/*
	 * process the RSDT or XSDT table.
	 */
	xsdt = root->tbl;
	xsdt->p = sdtmap(sdtpa, &xsdt->len, 1);
	if (xsdt->p == NULL) {
		printk("acpi: sdtmap failed\n");
		return;
	}
	if ((xsdt->p[0] != 'R' && xsdt->p[0] != 'X')
		|| memcmp(xsdt->p + 1, "SDT", 3) != 0) {
		printd("acpi: xsdt sig: %c%c%c%c\n",
		       xsdt->p[0], xsdt->p[1], xsdt->p[2], xsdt->p[3]);
		xsdt = NULL;
		return;
	}
	xsdt->asize = asize;
	printd("acpi: XSDT %#p\n", xsdt);
	parsexsdt(root);
}

static int acpigen(struct chan *c, char *name, struct dirtab *tab, int ntab,
				   int i, struct dir *dp)
{
	struct Atable *a;
	int r;

	a = c->aux;
	assert(a != NULL);
	if (c->qid.path == Qroot) {
		if (i == DEVDOTDOT) {
			devdir(c, root->qid, devname(), 0, eve, 0555, dp);
			c->aux = a;
			return 1;
		}
		r = devgen(c, name, root->cdirs, root->nchildren + NQtypes, i, dp);
		if (0 <= i && i < (root->nchildren + NQtypes))
			c->aux = root->children[i];
		return r;
	}
	if ((c->qid.path % NQtypes) == 0 && i == DEVDOTDOT) {
		char *name = a->parent->name;
		if (a->parent == root)
			name = devname();
		devdir(c, a->parent->qid, name, 0, eve, 0555, dp);
		c->aux = a->parent;
		return 1;
	}
	r = devgen(c, name, a->cdirs, a->nchildren + NQtypes, i, dp);
	if (0 <= i && i < (a->nchildren + NQtypes))
		c->aux = a->children[i];
	return r;
}

/*
 * Print the contents of the XSDT.
 */
static void dumpxsdt()
{
	printk("xsdt: len = %lu, asize = %lu, p = %p\n",
	       xsdt->len, xsdt->asize, xsdt->p);
}

static char *dumpGas(char *start, char *end, char *prefix, struct Gas *g)
{
	start = seprintf(start, end, "%s", prefix);

	switch (g->spc) {
		case Rsysmem:
		case Rsysio:
		case Rembed:
		case Rsmbus:
		case Rcmos:
		case Rpcibar:
		case Ripmi:
			start = seprintf(start, end, "[%s ", regnames[g->spc]);
			break;
		case Rpcicfg:
			start = seprintf(start, end, "[pci ");
			start =
				seprintf(start, end, "dev %#p ",
						 (uint32_t)(g->addr >> 32) & 0xFFFF);
			start =
				seprintf(start, end, "fn %#p ",
						 (uint32_t)(g->addr & 0xFFFF0000) >> 16);
			start =
				seprintf(start, end, "adr %#p ", (uint32_t)(g->addr & 0xFFFF));
			break;
		case Rfixedhw:
			start = seprintf(start, end, "[hw ");
			break;
		default:
			start = seprintf(start, end, "[spc=%#p ", g->spc);
	}
	start = seprintf(start, end, "off %d len %d addr %#p sz%d]",
					 g->off, g->len, g->addr, g->accsz);
	start = seprintf(start, end, "\n");
	return start;
}

static unsigned int getbanked(uintptr_t ra, uintptr_t rb, int sz)
{
	unsigned int r;

	r = 0;
	switch (sz) {
		case 1:
			if (ra != 0)
				r |= inb(ra);
			if (rb != 0)
				r |= inb(rb);
			break;
		case 2:
			if (ra != 0)
				r |= inw(ra);
			if (rb != 0)
				r |= inw(rb);
			break;
		case 4:
			if (ra != 0)
				r |= inl(ra);
			if (rb != 0)
				r |= inl(rb);
			break;
		default:
			printd("getbanked: wrong size\n");
	}
	return r;
}

static unsigned int setbanked(uintptr_t ra, uintptr_t rb, int sz, int v)
{
	unsigned int r;

	r = -1;
	switch (sz) {
		case 1:
			if (ra != 0)
				outb(ra, v);
			if (rb != 0)
				outb(rb, v);
			break;
		case 2:
			if (ra != 0)
				outw(ra, v);
			if (rb != 0)
				outw(rb, v);
			break;
		case 4:
			if (ra != 0)
				outl(ra, v);
			if (rb != 0)
				outl(rb, v);
			break;
		default:
			printd("setbanked: wrong size\n");
	}
	return r;
}

static unsigned int getpm1ctl(void)
{
	assert(fadt != NULL);
	return getbanked(fadt->pm1acntblk, fadt->pm1bcntblk, fadt->pm1cntlen);
}

static void setpm1sts(unsigned int v)
{
	assert(fadt != NULL);
	setbanked(fadt->pm1aevtblk, fadt->pm1bevtblk, fadt->pm1evtlen / 2, v);
}

static unsigned int getpm1sts(void)
{
	assert(fadt != NULL);
	return getbanked(fadt->pm1aevtblk, fadt->pm1bevtblk, fadt->pm1evtlen / 2);
}

static unsigned int getpm1en(void)
{
	int sz;

	assert(fadt != NULL);
	sz = fadt->pm1evtlen / 2;
	return getbanked(fadt->pm1aevtblk + sz, fadt->pm1bevtblk + sz, sz);
}

static int getgpeen(int n)
{
	return inb(gpes[n].enio) & 1 << gpes[n].enbit;
}

static void setgpeen(int n, unsigned int v)
{
	int old;

	old = inb(gpes[n].enio);
	if (v)
		outb(gpes[n].enio, old | 1 << gpes[n].enbit);
	else
		outb(gpes[n].enio, old & ~(1 << gpes[n].enbit));
}

static void clrgpests(int n)
{
	outb(gpes[n].stsio, 1 << gpes[n].stsbit);
}

static unsigned int getgpests(int n)
{
	return inb(gpes[n].stsio) & 1 << gpes[n].stsbit;
}

#if 0
static void acpiintr(Ureg *, void *)
{
	int i;
	unsigned int sts, en;

	printd("acpi: intr\n");

	for (i = 0; i < ngpes; i++)
		if (getgpests(i)) {
			printd("gpe %d on\n", i);
			en = getgpeen(i);
			setgpeen(i, 0);
			clrgpests(i);
			if (en != 0)
				printd("acpiitr: calling gpe %d\n", i);
			//  queue gpe for calling gpe->ho in the
			//  aml process.
			//  enable it again when it returns.
		}
	sts = getpm1sts();
	en = getpm1en();
	printd("acpiitr: pm1sts %#p pm1en %#p\n", sts, en);
	if (sts & en)
		printd("have enabled events\n");
	if (sts & 1)
		printd("power button\n");
	// XXX serve other interrupts here.
	setpm1sts(sts);
}
#endif

static void initgpes(void)
{
	int i, n0, n1;

	assert(fadt != NULL);
	n0 = fadt->gpe0blklen / 2;
	n1 = fadt->gpe1blklen / 2;
	ngpes = n0 + n1;
	gpes = kzmalloc(sizeof(struct Gpe) * ngpes, 1);
	for (i = 0; i < n0; i++) {
		gpes[i].nb = i;
		gpes[i].stsbit = i & 7;
		gpes[i].stsio = fadt->gpe0blk + (i >> 3);
		gpes[i].enbit = (n0 + i) & 7;
		gpes[i].enio = fadt->gpe0blk + ((n0 + i) >> 3);
	}
	for (i = 0; i + n0 < ngpes; i++) {
		gpes[i + n0].nb = fadt->gp1base + i;
		gpes[i + n0].stsbit = i & 7;
		gpes[i + n0].stsio = fadt->gpe1blk + (i >> 3);
		gpes[i + n0].enbit = (n1 + i) & 7;
		gpes[i + n0].enio = fadt->gpe1blk + ((n1 + i) >> 3);
	}
	for (i = 0; i < ngpes; i++) {
		setgpeen(i, 0);
		clrgpests(i);
	}
}

static void acpiioalloc(unsigned int addr, int len)
{
	if (addr != 0) {
		printk("Just TAKING port %016lx to %016lx\n", addr, addr + len);
		//ioalloc(addr, len, 0, "acpi");
	}
}

int acpiinit(void)
{
	/* This implements 'run once' for now. */
	if (root == NULL) {
		parsersdptr();
		if (root == NULL) {
			return -1;
		}
		printk("ACPI initialized\n");
	}
	return 0;
}

static struct chan *acpiattach(char *spec)
{
	int i;
	struct chan *c;
	/*
	 * This was written for the stock kernel.
	 * This code must use 64 registers to be acpi ready in nix.
	 */
	if (acpiinit() < 0)
		error(ENOSYS, "no acpi");

	/*
	 * should use fadt->xpm* and fadt->xgpe* registers for 64 bits.
	 * We are not ready in this kernel for that.
	 */
	assert(fadt != NULL);
	acpiioalloc(fadt->smicmd, 1);
	acpiioalloc(fadt->pm1aevtblk, fadt->pm1evtlen);
	acpiioalloc(fadt->pm1bevtblk, fadt->pm1evtlen);
	acpiioalloc(fadt->pm1acntblk, fadt->pm1cntlen);
	acpiioalloc(fadt->pm1bcntblk, fadt->pm1cntlen);
	acpiioalloc(fadt->pm2cntblk, fadt->pm2cntlen);
	acpiioalloc(fadt->pmtmrblk, fadt->pmtmrlen);
	acpiioalloc(fadt->gpe0blk, fadt->gpe0blklen);
	acpiioalloc(fadt->gpe1blk, fadt->gpe1blklen);

	initgpes();
#ifdef CONFIG_WE_ARE_NOT_WORTHY
	/* this is frightening. SMI: just say no. Although we will almost
	 * certainly find that we have no choice.
	 *
	 * This starts ACPI, which may require we handle
	 * power mgmt events ourselves. Use with care.
	 */
	outb(fadt->smicmd, fadt->acpienable);
	for (i = 0; i < 10; i++)
		if (getpm1ctl() & Pm1SciEn)
			break;
	if (i == 10)
		error(EFAIL, "acpi: failed to enable\n");
	if(fadt->sciint != 0)
		intrenable(fadt->sciint, acpiintr, 0, BUSUNKNOWN, "acpi");
#endif
	c = devattach(devname(), spec);
	c->aux = root;
	assert(c->aux != NULL);
	printk("returning a chan with non-NULL c->aux = %p\n", c->aux);
	return c;
}

static struct walkqid *acpiwalk(struct chan *c, struct chan *nc, char **name,
								int nname)
{
	return devwalk(c, nc, name, nname, NULL, 0, acpigen);
}

static int acpistat(struct chan *c, uint8_t *dp, int n)
{
	return devstat(c, dp, n, NULL, 0, acpigen);
}

static struct chan *acpiopen(struct chan *c, int omode)
{
	return devopen(c, omode, NULL, 0, acpigen);
}

static void acpiclose(struct chan *unused)
{
}

static char *ttext;
static int tlen;

// Get the table from the qid.
// Read that one table using the pointers.
static long acpiread(struct chan *c, void *a, long n, int64_t off)
{
	long q;
	struct Atable *t;
	char *ns, *s, *e, *ntext;

	if (ttext == NULL) {
		tlen = 32768;
		ttext = kzmalloc(tlen, 0);
	}
	if (ttext == NULL)
		error(ENOMEM, "acpiread: no memory");
	q = c->qid.path % 3;
	switch (q) {
	case Qdir:
		printk("acpiread: 0x%x\n", c->qid.path);
		return devdirread(c, a, n, 0, 0, acpigen);
	case Qraw:
		return readmem(off, a, n, ttext, tlen);
		break;
	case Qtbl:
		s = ttext;
		e = ttext + tlen;
		strlcpy(s, "no tables\n", tlen);
		for (t = tfirst; t != NULL; t = t->next) {
			ns = seprinttable(s, e, t);
			while (ns == e - 1) {
				ntext = krealloc(ttext, tlen * 2, 0);
				if (ntext == NULL)
					panic("acpi: no memory\n");
				s = ntext + (ttext - s);
				ttext = ntext;
				tlen *= 2;
				e = ttext + tlen;
				ns = seprinttable(s, e, t);
			}
			s = ns;
		}
		return readstr(off, a, n, ttext);
	case Qpretty:
		s = ttext;
		e = ttext + tlen;
		s = dumpfadt(s, e, fadt);
		s = dumpmadt(s, e, apics);
		s = dumpslit(s, e, slit);
		s = dumpsrat(s, e, srat);
		s = dumpdmar(s, e, dmar);
		dumpmsct(s, e, msct);
		return readstr(off, a, n, ttext);
	default:
		error(EINVAL, "WHAT? %d\n", q);
	}
	error(EPERM, ERROR_FIXME);
	return -1;
}

static long acpiwrite(struct chan *c, void *a, long n, int64_t off)
{
	error(EFAIL, "acpiwrite: not until we can figure out what it's for");
#if 0
	ERRSTACK(2);
	struct cmdtab *ct;
	struct cmdbuf *cb;
	struct Reg *r;
	unsigned int rno, fun, dev, bus, i;

	if (c->qid.path == Qio) {
		if (reg == NULL)
			error(EFAIL, "region not configured");
		return regio(reg, a, n, off, 1);
	}
	if (c->qid.path != Qctl)
		error(EPERM, ERROR_FIXME);

	cb = parsecmd(a, n);
	if (waserror()) {
		kfree(cb);
		nexterror();
	}
	ct = lookupcmd(cb, ctls, ARRAY_SIZE(ctls));
	switch (ct->index) {
		case CMregion:
			/* TODO: this block is racy on reg (global) */
			r = reg;
			if (r == NULL) {
				r = kzmalloc(sizeof(struct Reg), 0);
				r->name = NULL;
			}
			kstrdup(&r->name, cb->f[1]);
			r->spc = acpiregid(cb->f[2]);
			if (r->spc < 0) {
				kfree(r);
				reg = NULL;
				error(EFAIL, "bad region type");
			}
			if (r->spc == Rpcicfg || r->spc == Rpcibar) {
				rno = r->base >> Rpciregshift & Rpciregmask;
				fun = r->base >> Rpcifunshift & Rpcifunmask;
				dev = r->base >> Rpcidevshift & Rpcidevmask;
				bus = r->base >> Rpcibusshift & Rpcibusmask;
				#ifdef CONFIG_X86
				r->tbdf = MKBUS(BusPCI, bus, dev, fun);
				#else
				r->tbdf = 0
				#endif
				r->base = rno;	/* register ~ our base addr */
			}
			r->base = strtoul(cb->f[3], NULL, 0);
			r->len = strtoul(cb->f[4], NULL, 0);
			r->accsz = strtoul(cb->f[5], NULL, 0);
			if (r->accsz < 1 || r->accsz > 4) {
				kfree(r);
				reg = NULL;
				error(EFAIL, "bad region access size");
			}
			reg = r;
			printd("region %s %s %p %p sz%d",
				   r->name, acpiregstr(r->spc), r->base, r->len, r->accsz);
			break;
		case CMgpe:
			i = strtoul(cb->f[1], NULL, 0);
			if (i >= ngpes)
				error(ERANGE, "gpe out of range");
			kstrdup(&gpes[i].obj, cb->f[2]);
			setgpeen(i, 1);
			break;
		default:
			panic("acpi: unknown ctl");
	}
	poperror();
	kfree(cb);
	return n;
#endif
}

struct {
	char *(*pretty)(struct Atable *atbl, char *start, char *end, void *arg);
} acpisw[NACPITBLS] = {
};

static char *pretty(struct Atable *atbl, char *start, char *end, void *arg)
{
	int type;

	type = atbl->type;
	if (type < 0 || NACPITBLS < type)
		return start;
	if (acpisw[type].pretty == NULL)
		return seprintf(start, end, "\"\"\n");
	return acpisw[type].pretty(atbl, start, end, arg);
}

static char *raw(struct Atable *atbl, char *start, char *end, void *unused_arg)
{
	size_t len = MIN(end - start, atbl->rawsize);
	memmove(start, atbl->raw, len);
	return start + len;
}

struct dev acpidevtab __devtab = {
	.name = "acpi",

	.reset = devreset,
	.init = devinit,
	.shutdown = devshutdown,
	.attach = acpiattach,
	.walk = acpiwalk,
	.stat = acpistat,
	.open = acpiopen,
	.create = devcreate,
	.close = acpiclose,
	.read = acpiread,
	.bread = devbread,
	.write = acpiwrite,
	.bwrite = devbwrite,
	.remove = devremove,
	.wstat = devwstat,
};
