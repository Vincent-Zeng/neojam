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

#include <stdio.h>
#include "../jam.h"
#include "../sig.h"

// zeng: 方法参数个数
int extraArgSpace(MethodBlock *mb) {
    // zeng: static要加2(用于 JNIEnv *env, jclass cls 两个参数) 非static要加1(用于JNIEnv *env一个参数,  jclass cls参数位存放放对象地址, 而对象地址已经计入args_count里了)
    return (mb->access_flags & ACC_STATIC ? mb->args_count + 1 : mb->args_count) + 1;
}

// zeng: 调用动态库中的jni方法
u4 *callJNIMethod(void *env, Class *class, char *sig, int extra, u4 *ostack, unsigned char *f) {
    u4 args[extra];
    u4 *opntr = ostack;
    u4 *apntr = &args[2];   // zeng: 因为 args[0] args[1]下面用到了

    args[0] = (u4) env;
    args[1] = class ? (u4) class : *opntr++; // zeng: 如果是静态方法就取class对象地址, 否则就取方法所在对象地址

    // zeng: ostack中的操作数复制到args
    SCAN_SIG(sig, *((u8 *) apntr)++ = *((u8 *) opntr)++, *apntr++ = *opntr++);

    // zeng: TODO 调用f()时, 怎么没把args作为参数传进去? 栈 还是 寄存器? 这里面 应该涉及到i386的abi协议 和 c语言到汇编的转换, 就不深究了
    switch (*sig) {  // zeng: 根据返回值类型选择分支
        case 'V':
            (*(void (*)()) f)();    // zeng: 把f cast成*(void (*)())类型的了,也就是无参无返回值的函数
            break;

        case 'D':
            *((double *) ostack)++ = (*(double (*)()) f)();    // zeng: 执行native方法, 返回值放入操作数栈(其实这里ostack地址也是ret地址, 所以其实这里是赋值给ret作为返回值)
            break;

        case 'F':
            *((float *) ostack)++ = (*(float (*)()) f)();
            break;

        case 'J':
            *((long long *) ostack)++ = (*(long long (*)()) f)();
            break;

        default:
            *ostack++ = (*(u4 (*)()) f)();
            break;
    }

    return ostack;
}
