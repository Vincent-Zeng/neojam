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
#include "jam.h"
#include "frame.h"

// zeng: 遍历 class对象数组, 构造符号
char *convertClassArray2Sig(Object *array) {
    int count = 0, len;
    char *sig, *pntr;
    u4 *data;

    /* Calculate size of signature first */

    // zeng: 符号长度
    for (data = INST_DATA(array), len = *data++; len > 0; len--) {
        ClassBlock *cb = CLASS_CB((Class *) *data++);
        int nlen = strlen(cb->name);
        count += cb->flags == CLASS_INTERNAL ? nlen : nlen + 2;
    }

    // zeng: 分配空间
    sig = pntr = (char *) malloc(count + 1);

    /* Loop through again, and construct signature - "normal"
       loaded class names need wrapping but internally
       created class names (arrays and prim classes) are
       already in signature form... */

    // zeng: 构造符号
    for (data = INST_DATA(array), len = *data++; len > 0; len--) {
        ClassBlock *cb = CLASS_CB((Class *) *data++);
        pntr += sprintf(pntr, cb->flags == CLASS_INTERNAL ? "%s" : "L%s;", cb->name);
    }

    *pntr == '\0';

    return sig;
}

// zeng: 创建Constructor对象
Object *createConstructor(Class *class, char *sig) {
    Object *constructor = NULL;
    MethodBlock *mb;

    // zeng: 类的<init>方法
    mb = findMethod(class, "<init>", sig);

    if (mb != NULL) {
        Class *con_class = findSystemClass("java/lang/reflect/Constructor");
        if (con_class != NULL) {
            // zeng: Constructor类的<init>方法
            MethodBlock *init = findMethod(con_class, "<init>", "(Ljava/lang/Class;I)V");
            // zeng: 分配Constructor对象
            constructor = allocObject(con_class);

            // zeng: 调用Constructor类的<init>方法, 传参为类的class的对象 和 类的<init>方法
            executeMethod(constructor, init, class, mb);
        }
    }

    return constructor;
}

// zeng: 获取类的<init>方法对应的Constructor对象
Object *getClassConstructor(Class *class, Object *arg_list) {
    Object *constructor;

    if (arg_list) {
        // zeng: 参数
        char *params = convertClassArray2Sig(arg_list);

        // zeng: 描述符长度
        char *sig = (char *) malloc(strlen(params) + 4);

        // zeng: 构造描述符
        sprintf(sig, "(%s)V", params);

        // zeng: 创建Constructor对象
        constructor = createConstructor(class, sig);

        free(sig);
        free(params);
    } else
        constructor = createConstructor(class, "()V");  // zeng: 创建Constructor对象

    return constructor;
}

// zeng: 调用方法
Object *invoke(Object *ob, Class *class, MethodBlock *mb, Object *arg_array) {
    // zeng: 参数数组内容体
    Object **args = (Object **) (INST_DATA(arg_array) + 1);
    // zeng: 方法描述符
    char *sig = mb->type;

    // zeng: 线程当前执行环境
    ExecEnv *ee = getExecEnv();

    void *ret;
    u4 *sp;

    // zeng: 创建 top栈帧
    CREATE_TOP_FRAME(ee, class, mb, sp, ret);

        // zeng: 对象地址 入栈
        if (ob) *sp++ = (u4) ob;

        // zeng: 调用参数入栈
        while (*++sig != ')')
            switch (*sig) {
                case 'J':
                case 'D': {
                    *((u8*)sp)++ = *(u8*)(INST_DATA(*args++));

                    break;
                }
                case 'Z':
                case 'B':
                case 'C':
                case 'I':
                case 'F':
                    *sp++ = *(INST_DATA(*args++));
                    break;

                default:
                    *sp++ = (u4) *args++;

                    if (*sig == '[')
                        while (*++sig == '[');
                    if (*sig == 'L')
                        while (*++sig != ';');
                    break;
            }

        // zeng: synchronized方法
        if (mb->access_flags & ACC_SYNCHRONIZED)
            objectLock(ob ? ob : (Object *) mb->class); // zeng: 上锁

        if (mb->access_flags & ACC_NATIVE)  // zeng: native方法
            (*(u4 *(*)(Class *, MethodBlock *, u4 *)) mb->native_invoker)(class, mb, ret);  // zeng: 调用native_invoker
        else
            executeJava();  // zeng: 解释执行

        // zeng: synchronized方法
        if (mb->access_flags & ACC_SYNCHRONIZED)
            objectUnlock(ob ? ob : (Object *) mb->class);   // zeng: 释放锁

        // zeng: top栈帧出栈
        POP_TOP_FRAME(ee);

        return ret;
    }
