/* Define list of all signal numbers and their names.
   Copyright (C) 1997-2014 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */

#include <stddef.h>
#include <signal.h>
#include <libintl.h>
#include <shlib-compat.h>
#include <bits/wordsize.h>

const char *const __new_sys_siglist[NSIG] =
{
#define init_sig(sig, abbrev, desc)   [sig] = desc,
#include <siglist.h>
#undef init_sig
};
libc_hidden_ver (__new_sys_siglist, _sys_siglist)

const char *const __new_sys_sigabbrev[NSIG] =
{
#define init_sig(sig, abbrev, desc)   [sig] = abbrev,
#include <siglist.h>
#undef init_sig
};

strong_alias (__new_sys_siglist, _new_sys_siglist)
versioned_symbol (libc, __new_sys_siglist, _sys_siglist, GLIBC_2_1);
versioned_symbol (libc, _new_sys_siglist, sys_siglist, GLIBC_2_1);
versioned_symbol (libc, __new_sys_sigabbrev, sys_sigabbrev, GLIBC_2_1);
