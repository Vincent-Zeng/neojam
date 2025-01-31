/*
 * Copyright (C) 2003 Robert Lougher <rob@lougher.demon.co.uk>.
 *
 * This file is part of JamVM.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2,
 * or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

/*
 cmpxchgl r32, m32
  eax 和 m32 比较, 如果相等, ZF置位且r32被设置进m32. 如果不相等,ZF复位且m32被设置进eax.

 sete r8    取标志寄存器中ZF的值, 放到r8中
 */
#define COMPARE_AND_SWAP(addr, old_val, new_val)   \
({                                                 \
    char result;                                   \
    int read_val;                                  \
    __asm__ __volatile__ ("                        \
	lock;                                      \
	cmpxchgl %5, %1;                           \
	sete %0"                                   \
    : "=q" (result), "=m" (*addr), "=a" (read_val) \
    : "m" (*addr), "a" (old_val), "r" (new_val)    \
    : "memory");                                   \
    result;                                        \
})

