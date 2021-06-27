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

extern char VM_initing;

Object *exceptionOccured() {
    return getExecEnv()->exception;
}

// zeng: 传入 异常类全限定名 和 异常字符串 , 会设置 异常类class地址 到 执行上下文的exception
void signalException(char *excep_name, char *message) {
    if (VM_initing) {
        fprintf(stderr, "Exception occurred while VM initialising.\n");
        if (message)
            fprintf(stderr, "%s: %s\n", excep_name, message);
        else
            fprintf(stderr, "%s\n", excep_name);
        exit(1);
    } else {
        Class *exception = findSystemClass(excep_name); // zeng: 根据全限定名 得到 异常类 class对象地址

        if (!exceptionOccured()) {
            Object *exp = allocObject(exception);   // zeng: 为异常对象分配内存
            // zeng: 准备初始化方法的参数
            Object *str = message == NULL ? NULL : Cstr2String(message);
            // zeng: 找到异常类初始化方法
            MethodBlock *init = lookupMethod(exception,
                                             "<init>", "(Ljava/lang/String;)V");
            if (exp && init) {
                // zeng: 初始化异常对象
                executeMethod(exp, init, str);
                // zeng: 将异常对象地址 写入 执行上下文的exception中
                getExecEnv()->exception = exp;
            }
        }
    }
}

void setException(Object *exp) {
    getExecEnv()->exception = exp;
}

// zeng: 运行上下文中exception设置为null
void clearException() {
    getExecEnv()->exception = NULL;
}

// zeng: 调用 ee -> exception 对象的printStackTrace方法
void printException() {
    ExecEnv *ee = getExecEnv();
    Object *exception = ee->exception;

    // zeng: 查找异常类的 void printStackTrace() 方法
    MethodBlock *mb = lookupMethod(exception->class, "printStackTrace", "()V");

    clearException();

    // zeng: 执行方法
    executeMethod(exception, mb);

    // zeng: 执行printStackTrace方法的时候也发生异常了
    /* If we're really low on memory we might have been able to throw
     * OutOfMemory, but then been unable to print any part of it!  In
     * this case the VM just seems to stop... */
    if (ee->exception) {
        fprintf(stderr, "Exception occured while printing exception...\n");

        fprintf(stderr, "Original exception was %s\n", CLASS_CB(exception->class)->name);
    }
}

// zeng: 方法中查找exception对应的catch block 返回handler块地址
unsigned char *findCatchBlockInMethod(MethodBlock *mb, Class *exception, unsigned char *pc_pntr) {
    // zeng: 获取exception_table数组地址
    ExceptionTableEntry *table = mb->exception_table;
    int size = mb->exception_table_size;

    // zeng: 当前pc 距离方法code开始地址 的偏移量
    int pc = pc_pntr - mb->code;
    int i;

    for (i = 0; i < size; i++)
        if ((pc >= table[i].start_pc) && (pc < table[i].end_pc)) {   // zeng: 偏移量是否在start_pc和end_pc之间

            /* If the catch_type is 0 it's a finally block, which matches
               any exception.  Otherwise, the thrown exception class must
               be an instance of the caught exception class to catch it */

            if (table[i].catch_type != 0) {  // zeng: 在catch的异常列表中查找该exception
                // zeng: catch_type中存放的是constant_pool index, 根据index获取class对象
                Class *caught_class = resolveClass(mb->class, table[i].catch_type, FALSE);
                if (caught_class == NULL) {
                    clearException();
                    continue;
                }
                if (!isInstanceOf(caught_class, exception))
                    continue;
            }

            return mb->code + table[i].handler_pc;  // zeng:找到就返回handler块代码地址
        }

    return NULL;
}

// zeng: 当前调用链中查找exception对应的catch block 返回handler块地址
unsigned char *findCatchBlock(Class *exception) {
    // zeng: 执行上下文中当前栈帧
    Frame *frame = getExecEnv()->last_frame;

    unsigned char *handler_pc = NULL;

    // zeng: 当前栈帧锁对应的方法中是否有该异常类class对象对应的catch block块
    while (((handler_pc = findCatchBlockInMethod(frame->mb, exception, frame->last_pc)) == NULL) &&
           (frame->prev->mb != NULL)) {

        if (frame->mb->access_flags & ACC_SYNCHRONIZED) {    // zeng: synchronized方法要上锁
            Object *sync_ob = frame->mb->access_flags & ACC_STATIC ?
                              (Object *) frame->mb->class : (Object *) frame->lvars[0];
            objectUnlock(sync_ob);
        }

        frame = frame->prev;    // zeng: 没有就沿着调用链往上寻找
    }

    getExecEnv()->last_frame = frame;   // zeng: 找到的catch block的方法栈帧作为当前栈帧

    return handler_pc;  // zeng: 返回
}

int mapPC2LineNo(MethodBlock *mb, unsigned char *pc_pntr) {
    int pc = pc_pntr - mb->code;
    int i;

    if (mb->line_no_table_size > 0) {
        for (i = mb->line_no_table_size - 1; i && pc < mb->line_no_table[i].start_pc; i--);
        return mb->line_no_table[i].line_no;
    }

    return -1;
}

// zeng: 将发生异常出往前的调用链信息写入异常对象中
void setStackTrace(Object *excep) {
    // zeng: 获取Throwable的class对象
    Class *throw_class = findSystemClass("java/lang/Throwable");
    // zeng: 获取backtrace字段
    FieldBlock *field = findField(throw_class, "backtrace", "Ljava/lang/Object;");

    Object *array;
    int *data;

    // zeng: 当前栈帧
    Frame *bottom, *last = getExecEnv()->last_frame;

    int depth = 0;

    // zeng: 栈帧对应方法所在类是否是throw_class或其子类, 直到找到 是 的栈帧
    for (; last->mb != NULL && isInstanceOf(throw_class, last->mb->class); last = last->prev);

    // zeng: 调用链深度
    bottom = last;
    do {
        for (; last->mb != NULL; last = last->prev, depth++);
    } while ((last = last->prev)->prev != NULL);

    // zeng: 分配数组空间
    array = allocTypeArray(T_INT, depth * 2);

    // zeng: 将调用链上的方法和最近pc 写入数组
    if (array) {
        data = INST_DATA(array);

        depth = 1;
        do {
            for (; bottom->mb != NULL; bottom = bottom->prev) {
                data[depth++] = (int) bottom->mb;
                data[depth++] = (int) bottom->last_pc;
            }
        } while ((bottom = bottom->prev)->prev != NULL);
    }

    // zeng: 将数组地址赋值给backtrace字段
    INST_DATA(excep)[field->offset] = (int) array;
}

// zeng: 将调用链信息用字符数组表示, 然后用字符参数作为参数调用writer对象的println方法
void printStackTrace(Object *excep, Object *writer) {
    // zeng: 获取Throwable的class对象
    Class *throw_class = findSystemClass("java/lang/Throwable");
    // zeng: 获取backtrace字段
    FieldBlock *field = findField(throw_class, "backtrace", "Ljava/lang/Object;");
    // zeng: 获取writer对象的void println(char[] arg1)方法
    MethodBlock *print = lookupMethod(writer->class, "println", "([C)V");
    // zeng: 获取backtrace字段值, 即表示调用链信息的数组的地址
    Object *array = (Object *) INST_DATA(excep)[field->offset];

    char buff[256];
    int *data, depth;
    int i = 0;

    if (array == NULL)
        return;

    // zeng: 数组内容地址(不包括数组长度)
    data = &(INST_DATA(array)[1]);
    // zeng: 数组长度
    depth = *INST_DATA(array);

    for (; i < depth;) {
        MethodBlock *mb = (MethodBlock *) data[i++];

        unsigned char *pc = (unsigned char *) data[i++];

        ClassBlock *cb = CLASS_CB(mb->class);

        unsigned char *dot_name = slash2dots(cb->name);

        char *spntr = buff;
        short *dpntr;
        int len;

        // zeng: 利用调用链信息 构造 buff字符数组
        if (mb->access_flags & ACC_NATIVE)
            len = sprintf(buff, "\tat %s.%s(Native method)", dot_name, mb->name);
        else if (cb->source_file_name == 0)
            len = sprintf(buff, "\tat %s.%s(Unknown source)", dot_name, mb->name);
        else
            len = sprintf(buff, "\tat %s.%s(%s:%d)", dot_name, mb->name,
                          cb->source_file_name, mapPC2LineNo(mb, pc));

        free(dot_name);

        // zeng: java数组
        if ((array = allocTypeArray(T_CHAR, len)) == NULL)
            return;

        dpntr = (short *) INST_DATA(array) + 2;

        // zeng: 字符数组 复制到 java数组内容体 中
        for (; len > 0; len--)
            *dpntr++ = *spntr++;

        // zeng: 执行writer对象的void println(char[] arg1)方法, 参数为上面构造的代表 调用链信息 的java数组
        executeMethod(writer, print, array);
    }
}
