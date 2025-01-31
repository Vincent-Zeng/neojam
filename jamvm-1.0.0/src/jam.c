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
#include <stdlib.h>
#include <stdarg.h>

#include "jam.h"

/* Setup default values for command line args */

static int noasyncgc = FALSE;
static int verbosegc = FALSE;
static int verboseclass = FALSE;

#define KB 1024
#define MB (KB*KB)
#define MIN_HEAP 4*KB
#define MIN_STACK 2*KB

static int java_stack = 64 * KB;
static int min_heap = 256 * KB;
static int max_heap = 16 * MB;

char VM_initing = TRUE;

void initVM() {
    Class *class;
    MethodBlock *mb;
    // zeng: 堆内存 相关
    initialiseAlloc(min_heap, max_heap, verbosegc);
    // zeng: 类加载 相关
    initialiseClass(verboseclass);
    // zeng: jni 相关
    initialiseDll();
    // zeng: utf8 字符串相关
    initialiseUtf8();
    // zeng: 用于线程同步的monitor 相关
    initialiseMonitor();
    // zeng: main thread 相关
    initialiseMainThread(java_stack);
    // zeng: String类 相关
    initialiseString();
    // zeng: 开启gc线程
    initialiseGC(noasyncgc);
    // zeng: 初始化用于jni的互斥量
    initialiseJNI();


    // zeng: 加载与初始化如下类
    /* No need to check for exception - if one occurs, signalException aborts VM */
    findSystemClass("java/lang/NoClassDefFoundError");
    findSystemClass("java/lang/ClassFormatError");
    findSystemClass("java/lang/NoSuchFieldError");
    findSystemClass("java/lang/NoSuchMethodError");

    /* nasty nasty hack needed with Sun's system classes */

    // zeng: 执行System.initializeSystemClass(用来设置标准io等)
    class = findSystemClass("java/lang/System");

    mb = findMethod(class, "initializeSystemClass", "()V");
    if (mb && (mb->access_flags & ACC_STATIC))
        executeStaticMethod(class, mb);

    VM_initing = FALSE;
}

void showUsage(char *name) {
    printf("Usage: %s [-options] class [arg1 arg2 ...]\n", name);
    printf("\nwhere options include:\n");
    printf("\t-help\t\tprint out this message\n");
    printf("\t-version\tprint out version number and copyright information\n");
    printf("\t-verbose\tprint out information about class loading, etc.\n");
    printf("\t-verbosegc\tprint out results of garbage collection\n");
    printf("\t-noasyncgc\tturn off asynchronous garbage collection\n");
    printf("\t-ms<number>\tset the initial size of the heap (default = %dK)\n", min_heap / KB);
    printf("\t-mx<number>\tset the maximum size of the heap (default = %dM)\n", max_heap / MB);
    printf("\t-ss<number>\tset the Java stack size for each thread (default = %dK)\n", java_stack / KB);
}

int parseMemValue(char *str) {
    char *end;
    long n = strtol(str, &end, 0);

    switch (end[0]) {
        case '\0':
            break;

        case 'M':
        case 'm':
            n *= MB;
            break;

        case 'K':
        case 'k':
            n *= KB;
            break;

        default:
            n = 0;
    }

    return n;
}

int parseCommandLine(int argc, char *argv[]) {
    int i;

    for (i = 1; i < argc; i++) {
        if (*argv[i] != '-') {
            if (min_heap > max_heap) {
                printf("Minimum heap size greater than max!\n");
                exit(0);
            }
            return i;
        }

        if (strcmp(argv[i], "-help") == 0)
            break;

        else if (strcmp(argv[i], "-version") == 0) {
            printf("JamVM version %s\n", VERSION);
            printf("Copyright (C) 2003 Robert Lougher <rob@lougher.demon.co.uk>\n\n");
            printf("This program is free software; you can redistribute it and/or\n");
            printf("modify it under the terms of the GNU General Public License\n");
            printf("as published by the Free Software Foundation; either version 2,\n");
            printf("or (at your option) any later version.\n\n");
            printf("This program is distributed in the hope that it will be useful,\n");
            printf("but WITHOUT ANY WARRANTY; without even the implied warranty of\n");
            printf("MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n");
            printf("GNU General Public License for more details.\n");
            exit(0);
        } else if (strcmp(argv[i], "-verbose") == 0)
            verboseclass = TRUE;

        else if (strcmp(argv[i], "-verbosegc") == 0)
            verbosegc = TRUE;

        else if (strcmp(argv[i], "-noasyncgc") == 0)
            noasyncgc = TRUE;

        else if (strncmp(argv[i], "-ms", 3) == 0) {
            min_heap = parseMemValue(argv[i] + 3);
            if (min_heap < MIN_HEAP) {
                printf("Invalid minimum heap size: %s (min %dK)\n", argv[i], MIN_HEAP / KB);
                exit(0);
            }
        } else if (strncmp(argv[i], "-mx", 3) == 0) {
            max_heap = parseMemValue(argv[i] + 3);
            if (max_heap < MIN_HEAP) {
                printf("Invalid maximum heap size: %s (min is %dK)\n", argv[i], MIN_HEAP / KB);
                exit(0);
            }
        } else if (strncmp(argv[i], "-ss", 3) == 0) {
            java_stack = parseMemValue(argv[i] + 3);
            if (java_stack < MIN_STACK) {
                printf("Invalid Java stack size: %s\n", argv[i]);
                exit(0);
            }
        } else {
            printf("Unrecognised command line option: %s\n", argv[i]);
            break;
        }
    }

    showUsage(argv[0]);
    exit(0);
}

int main(int argc, char *argv[]) {
    Class *class;
    MethodBlock *mb;
    Object *array;
    char *cpntr;
    u4 *args;
    int i;

    // zeng: 解析命令行参数,参数用来设置堆大小 栈大小的配置变量等, 返回参数数组中 class 的 index
    int class_arg = parseCommandLine(argc, argv);

    // zeng: 初始化
    initVM();

    // zeng: 将class全限定名中的.替换为/
    for (cpntr = argv[class_arg]; *cpntr; cpntr++)
        if (*cpntr == '.')
            *cpntr = '/';

    // zeng: 获取class
    class = findSystemClass(argv[class_arg]);

    // zeng: 打印异常 并 退出
    if (exceptionOccured()) {
        printException();
        exit(0);
    }

    // zeng: 获取main方法
    mb = lookupMethod(class, "main", "([Ljava/lang/String;)V");
    if (!mb || !(mb->access_flags & ACC_STATIC)) {
        printf("Static method \"main\" not found in %s\n", argv[class_arg]);
        exit(0);
    }

    /* Create the String array holding the command line args */

    // zeng: 组装给main方法的参数
    array = allocArray(findSystemClass("java/lang/String"), argc - class_arg - 1, 4);
    // zeng: 数组size指针 减去 class_arg 即args地址包括 命令行中 class 及 class之前的参数
    args = INST_DATA(array) - class_arg;

    // zeng: 只从 数组size 指针 接着的地址写入
    for (i = class_arg + 1; i < argc; i++)
        args[i] = (u4) Cstr2String(argv[i]);

    /* Call the main method */
    // zeng: 执行main方法
    executeStaticMethod(class, mb, array);

    // zeng:  打印异常
    if (exceptionOccured())
        printException();

    // zeng: 等待其他线程退出
    mainThreadWaitToExitVM();
}
