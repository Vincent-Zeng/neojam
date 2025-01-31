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

// zeng: 调用java方法 有两种方式, 第一种是通过executeMethodArgs executeMethodVaList executeMethodList 3个c方法来调用 第二种是执行java方法解释操作码时通过`goto invokeMethod`来调用
// zeng: 这里是通过c方法调用时 创建方法栈帧 所用 这个通过c方法调用的方法 我们称之为`top of this Java invocation` 因为`goto invokeMethod`这种调用只能在 `c方法调用的方法` 解释执行时发生
#define CREATE_TOP_FRAME(ee, class, mb, sp, ret)                \
{                                                               \
    Frame *last = ee->last_frame;                               \
                                                                \
    Frame *dummy = (Frame *)(last->ostack+last->mb->max_stack); \   // zeng: 上一个frame结构的ostack起始地址 + ostack操作数栈深度(每个操作数占u4,和指针大小一样,所以可以这样加), 即操作栈结束地址, 也即上一个栈帧结束地址 结束之后这里分配了一个名为dummy的frame结构体 用来判断方法是否`top of this Java invocation`
    Frame *new_frame;                                           \
                                                                \
    sp = (u4*)(dummy+1);				                    	\   // zeng: dummy结构体接下来是dummy栈帧的ostack(只有一个格子)的地址 这个地址也可以作为下一个栈帧的本地向量数组第一个格子
    ret = sp;							                        \   // zeng: 返回值存在ostack这个格子里
    new_frame = (Frame *)(sp + mb->max_locals);                 \   // zeng: 返回值地址接下来是本地变量表地址 本地变量数组地址接下来就是新的栈帧地址
                                                                \
    dummy->mb = NULL;                                           \
    dummy->ostack = sp;                                         \   // zeng: dummy ostack地址在dummy结构体之后
    dummy->prev = last;                                         \   // zeng: dummy frame结构体指向前一个stack frame结构体
                                                                \
    new_frame->mb = mb;                                         \   // zeng: 设置frame结构体中的mb指向方法的MethodBlock
    new_frame->lvars = sp;                                      \   // zeng: 本地变量数组 第一个格子是dummy栈帧的ostack的格子
    new_frame->ostack = (u4 *)(new_frame + 1);                  \   // zeng: 新的frame结构体之后是新的ostack地址
                                                                \
    new_frame->prev = dummy;                                    \   // zeng: 新的frame结构体指向dummy结构体
    ee->last_frame = new_frame;                                 \   // zeng: 执行上下文的last_frame指向新的frame结构体
}

#define POP_TOP_FRAME(ee)                                       \
    ee->last_frame = ee->last_frame->prev->prev;    // zeng: 执行上下文的last_frame指向上一个方法的栈帧的frame结构体
