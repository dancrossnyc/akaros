/* 
 * This file is part of the UCB release of Plan 9. It is subject to the license
 * terms in the LICENSE file found in the top-level directory of this
 * distribution and at http://akaros.cs.berkeley.edu/files/Plan9License. No
 * part of the UCB release of Plan 9, including this file, may be copied,
 * modified, propagated, or distributed except according to the terms contained
 * in the LICENSE file.
 */
#include <stdlib.h>

#include <stdio.h>
#include <parlib.h>
#include <unistd.h>
#include <signal.h>
#include <fcntl.h>
#include <iplib.h>
#include <dir.h>
#include <ndb.h>
#include <fcall.h>

static
uint8_t*
pstring(uint8_t *p, char *s)
{
	unsigned int n;

	if(s == NULL){
		PBIT16(p, 0);
		p += BIT16SZ;
		return p;
	}

	n = strlen(s);
	/*
	 * We are moving the string before the length,
	 * so you can S2M a struct into an existing message
	 */
	memmove(p + BIT16SZ, s, n);
	PBIT16(p, n);
	p += n + BIT16SZ;
	return p;
}

static
uint8_t*
pqid(uint8_t *p, struct qid *q)
{
	PBIT8(p, q->type);
	p += BIT8SZ;
	PBIT32(p, q->vers);
	p += BIT32SZ;
	PBIT64(p, q->path);
	p += BIT64SZ;
	return p;
}

static
unsigned int
stringsz(char *s)
{
	if(s == NULL)
		return BIT16SZ;

	return BIT16SZ+strlen(s);
}

unsigned int
sizeS2M(struct fcall *f)
{
	unsigned int n;
	int i;

	n = 0;
	n += BIT32SZ;	/* size */
	n += BIT8SZ;	/* type */
	n += BIT16SZ;	/* tag */

	switch(f->type)
	{
	default:
		return 0;

	case Tversion:
		n += BIT32SZ;
		n += stringsz(f->version);
		break;

	case Tflush:
		n += BIT16SZ;
		break;

	case Tauth:
		n += BIT32SZ;
		n += stringsz(f->uname);
		n += stringsz(f->aname);
		break;

	case Tattach:
		n += BIT32SZ;
		n += BIT32SZ;
		n += stringsz(f->uname);
		n += stringsz(f->aname);
		break;

	case Twalk:
		n += BIT32SZ;
		n += BIT32SZ;
		n += BIT16SZ;
		for(i=0; i<f->nwname; i++)
			n += stringsz(f->wname[i]);
		break;

	case Topen:
		n += BIT32SZ;
		n += BIT8SZ;
		break;

	case Tcreate:
		n += BIT32SZ;
		n += stringsz(f->name);
		n += BIT32SZ;
		n += BIT8SZ;
		break;

	case Tread:
		n += BIT32SZ;
		n += BIT64SZ;
		n += BIT32SZ;
		break;

	case Twrite:
		n += BIT32SZ;
		n += BIT64SZ;
		n += BIT32SZ;
		n += f->count;
		break;

	case Tclunk:
	case Tremove:
		n += BIT32SZ;
		break;

	case Tstat:
		n += BIT32SZ;
		break;

	case Twstat:
		n += BIT32SZ;
		n += BIT16SZ;
		n += f->nstat;
		break;
/*
 */

	case Rversion:
		n += BIT32SZ;
		n += stringsz(f->version);
		break;

	case Rerror:
		n += stringsz(f->ename);
		break;

	case Rflush:
		break;

	case Rauth:
		n += QIDSZ;
		break;

	case Rattach:
		n += QIDSZ;
		break;

	case Rwalk:
		n += BIT16SZ;
		n += f->nwqid*QIDSZ;
		break;

	case Ropen:
	case Rcreate:
		n += QIDSZ;
		n += BIT32SZ;
		break;

	case Rread:
		n += BIT32SZ;
		n += f->count;
		break;

	case Rwrite:
		n += BIT32SZ;
		break;

	case Rclunk:
		break;

	case Rremove:
		break;

	case Rstat:
		n += BIT16SZ;
		n += f->nstat;
		break;

	case Rwstat:
		break;
	}
	return n;
}

unsigned int
convS2M(struct fcall *f, uint8_t *ap, unsigned int nap)
{
	uint8_t *p;
	unsigned int i, size;

	size = sizeS2M(f);
	if(size == 0)
		return 0;
	if(size > nap)
		return 0;

	p = (uint8_t*)ap;

	PBIT32(p, size);
	p += BIT32SZ;
	PBIT8(p, f->type);
	p += BIT8SZ;
	PBIT16(p, f->tag);
	p += BIT16SZ;

	switch(f->type)
	{
	default:
		return 0;

	case Tversion:
		PBIT32(p, f->msize);
		p += BIT32SZ;
		p = pstring(p, f->version);
		break;

	case Tflush:
		PBIT16(p, f->oldtag);
		p += BIT16SZ;
		break;

	case Tauth:
		PBIT32(p, f->afid);
		p += BIT32SZ;
		p  = pstring(p, f->uname);
		p  = pstring(p, f->aname);
		break;

	case Tattach:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		PBIT32(p, f->afid);
		p += BIT32SZ;
		p  = pstring(p, f->uname);
		p  = pstring(p, f->aname);
		break;

	case Twalk:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		PBIT32(p, f->newfid);
		p += BIT32SZ;
		PBIT16(p, f->nwname);
		p += BIT16SZ;
		if(f->nwname > MAXWELEM)
			return 0;
		for(i=0; i<f->nwname; i++)
			p = pstring(p, f->wname[i]);
		break;

	case Topen:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		PBIT8(p, f->mode);
		p += BIT8SZ;
		break;

	case Tcreate:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		p = pstring(p, f->name);
		PBIT32(p, f->perm);
		p += BIT32SZ;
		PBIT8(p, f->mode);
		p += BIT8SZ;
		break;

	case Tread:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		PBIT64(p, f->offset);
		p += BIT64SZ;
		PBIT32(p, f->count);
		p += BIT32SZ;
		break;

	case Twrite:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		PBIT64(p, f->offset);
		p += BIT64SZ;
		PBIT32(p, f->count);
		p += BIT32SZ;
		memmove(p, f->data, f->count);
		p += f->count;
		break;

	case Tclunk:
	case Tremove:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		break;

	case Tstat:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		break;

	case Twstat:
		PBIT32(p, f->fid);
		p += BIT32SZ;
		PBIT16(p, f->nstat);
		p += BIT16SZ;
		memmove(p, f->stat, f->nstat);
		p += f->nstat;
		break;
/*
 */

	case Rversion:
		PBIT32(p, f->msize);
		p += BIT32SZ;
		p = pstring(p, f->version);
		break;

	case Rerror:
		p = pstring(p, f->ename);
		break;

	case Rflush:
		break;

	case Rauth:
		p = pqid(p, &f->aqid);
		break;

	case Rattach:
		p = pqid(p, &f->qid);
		break;

	case Rwalk:
		PBIT16(p, f->nwqid);
		p += BIT16SZ;
		if(f->nwqid > MAXWELEM)
			return 0;
		for(i=0; i<f->nwqid; i++)
			p = pqid(p, &f->wqid[i]);
		break;

	case Ropen:
	case Rcreate:
		p = pqid(p, &f->qid);
		PBIT32(p, f->iounit);
		p += BIT32SZ;
		break;

	case Rread:
		PBIT32(p, f->count);
		p += BIT32SZ;
		memmove(p, f->data, f->count);
		p += f->count;
		break;

	case Rwrite:
		PBIT32(p, f->count);
		p += BIT32SZ;
		break;

	case Rclunk:
		break;

	case Rremove:
		break;

	case Rstat:
		PBIT16(p, f->nstat);
		p += BIT16SZ;
		memmove(p, f->stat, f->nstat);
		p += f->nstat;
		break;

	case Rwstat:
		break;
	}
	if(size != p-ap)
		return 0;
	return size;
}