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
 * You should have received a copy of the GNU Gedummyneral Public License
 * along with this program; if not, write to the Free Software
 * Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

#define CREATE_TOP_FRAME(ee, class, mb, sp, ret)                \
{                                                               \
    Frame *last = ee->last_frame;                               \
                                                                \
    Frame *dummy = (Frame *)(last->ostack+last->mb->max_stack); \   // zeng: 上一个frame结构的ostack起始地址 + ostack操作数栈深度(每个操作数占u4,和指针大小一样,所以可以这样加), 即操作栈结束地址, 也即上一个栈帧结束地址 结束之后这里分配了一个名为dummy的frame结构体 TODO dummy有什么用
    Frame *new_frame;                                           \
                                                                \
    sp = (u4*)(dummy+1);				                    	\   // zeng: dummy结构提接下来是返回值地址的地址
    ret = sp;							                        \
    new_frame = (Frame *)(sp + mb->max_locals);                 \   // zeng: 返回值地址接下来是本地变量表地址 本地变量数组地址接下来就是新的栈帧地址
                                                                \
    dummy->mb = NULL;                                           \
    dummy->ostack = sp;                                         \   // zeng: dummy ostack地址在dummy结构体之后 TODO 有什么用
    dummy->prev = last;                                         \   // zeng: dummy frame结构体指向前一个stack frame结构体
                                                                \
    new_frame->mb = mb;                                         \   // zeng: 设置frame结构体中的mb指向方法的MethodBlock
    new_frame->lvars = sp;                                      \   // zeng: TODO 本地变量表地址 为何是 返回值地址的地址? 是因为本地变量数组可以暂时使用这个格子?
    new_frame->ostack = (u4 *)(new_frame + 1);                  \   // zeng: 新的frame结构体之后是新的ostack地址
                                                                \
    new_frame->prev = dummy;                                    \   // zeng: 新的frame结构体指向dummy结构体
    ee->last_frame = new_frame;                                 \   // zeng: 执行上下文的last_frame指向新的frame结构体
}

#define POP_TOP_FRAME(ee)                                       \
    ee->last_frame = ee->last_frame->prev->prev;    // zeng: 执行上下文的last_frame指向上一个方法的栈帧的frame结构体
