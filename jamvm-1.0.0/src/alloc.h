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

#define LOG_OBJECT_GRAIN	3
#define HEADER_SIZE		4
#define FLC_BIT			2

// zeng: 对象所在chunk的header的flc bit置0, 表示没有线程在等待轻量锁释放
#define clear_flc_bit(o) { \
	unsigned int *hdr = (unsigned int*)(((char*)o)-HEADER_SIZE); \
        *hdr  &= ~FLC_BIT; \
}

// zeng: 对象所在chunk的header的flc bit置1, 表示没有线程在等待轻量锁释放
#define set_flc_bit(o) { \
	unsigned int *hdr = (unsigned int*)(((char*)o)-HEADER_SIZE); \
        *hdr  |= FLC_BIT; \
}

// zeng: 是否有线程在等待轻量锁释放
#define test_flc_bit(o) *(unsigned int*)(((char*)o)-HEADER_SIZE) & FLC_BIT
