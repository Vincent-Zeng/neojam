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
#include <string.h>

#include "jam.h"

#ifndef NO_JNI
    #include <dlfcn.h>
    #include "hash.h"
    #include "jni.h"

    /* Trace library loading and method lookup */
    #ifdef TRACEDLL
        #define TRACE(x) printf x
    #else
        #define TRACE(x)
#endif

#define HASHTABSZE 1<<4
static HashTable hash_table;
void *lookupLoadedDlls(MethodBlock *mb);
#endif

// zeng: 将C++源程序标识符(original C++ source identifier)转换成C++ ABI标识符(C++ ABI identifier)的过程称为mangle；相反的过程称为demangle。
// zeng: 知道是字符串转换就行 不感兴趣 不看了
char *mangleString(unsigned char *utf8) {
    int len = utf8Len(utf8);
    unsigned short *unicode = (unsigned short*) malloc(len * 2);
    char *mangled, *mngldPtr;
    int i, mangledLen = 0;

    convertUtf8(utf8, unicode);

    /* Work out the length of the mangled string */

    for(i = 0; i < len; i++) {
        unsigned short c = unicode[i];
        if(c > 255)
            mangledLen += 6;
        else
            switch(c) {
                case '_':
                case ';':
                case '[':
                    mangledLen += 2;
                    break;

                default:
                    mangledLen++;
                    break;
            }
    }

    mangled = mngldPtr = (char*) malloc(mangledLen + 1);

    /* Construct the mangled string */

    for(i = 0; i < len; i++) {
        unsigned short c = unicode[i];
        if(c > 255)
            mngldPtr += sprintf(mngldPtr, "_0%04X", c);
        else
            switch(c) {
                case '_':
                    *mngldPtr++ = '_';
                    *mngldPtr++ = '1';
                    break;
                case ';':
                    *mngldPtr++ = '_';
                    *mngldPtr++ = '2';
                    break;
                case '[':
                    *mngldPtr++ = '_';
                    *mngldPtr++ = '3';
                    break;

                case '/':
                    *mngldPtr++ = '_';
                    break;

                default:
                    *mngldPtr++ = c;
                    break;
            }
    }

    *mngldPtr = '\0';

    free(unicode);
    return mangled;
}

char *mangleClassAndMethodName(MethodBlock *mb) {
    char *classname = CLASS_CB(mb->class)->name;    // zeng: 类名
    char *methodname = mb->name;    // zeng: 方法名
    char *nonMangled = (char*) malloc(strlen(classname) + strlen(methodname) + 7);  // zeng: 分配字符串空间
    char *mangled;

    sprintf(nonMangled, "Java/%s/%s", classname, methodname);   // zeng: Java/类名/方法名\0

    mangled = mangleString(nonMangled); // zeng: 转换成了 Java_类名_方法名\0, 这是jni约定的实现native方法的命名规则

    free(nonMangled);   // zeng: 释放空间

    return mangled;
}

// zeng: 方法描述符进行mangle处理
char *mangleSignature(MethodBlock *mb) {
    char *type = mb->type;
    char *nonMangled;
    char *mangled;
    int i;

    /* find ending ) */
    for(i = strlen(type) - 1; type[i] != ')'; i--);
    nonMangled = (char *) malloc(i);

    strncpy(nonMangled, type + 1, i - 1);

    nonMangled[i - 1] = '\0';
    
    mangled = mangleString(nonMangled);

    free(nonMangled);

    return mangled;
}

// zeng: 根据方法名称在native_methods中查找c方法
void *lookupInternal(MethodBlock *mb) {
    int i;

    TRACE(("<Dll: Looking up %s internally>\n", mb->name));

    // zeng: 根据方法名称在native_methods中查找
    for(i = 0; native_methods[i][0] && (strcmp(mb->name, native_methods[i][0]) != 0) ; i++);

    if(native_methods[i][0])    // zeng: 找到了
        return mb->native_invoker = (void*)native_methods[i][1];    // zeng: 将native_invoker设置为找到的本地方法地址
    else
        return NULL;
}

// zeng: 先从native_methods中查找c方法(jvm自身内置的c方法), 再从 加载的 动态链接库 中查找c方法 (通过jni定义的方法)
void *resolveNativeMethod(MethodBlock *mb) {
    // zeng: 先从native_methods中查找
    void *func = lookupInternal(mb);

#ifndef NO_JNI
    if(func == NULL)
        func = lookupLoadedDlls(mb);    // zeng: 从加载的 动态链接库 方法hash表 中查找native方法
#endif

    return func;
}

// zeng: 先找到本地方法的地址, 将mb -> native_invoker 替换成本地方法地址, 执行本地方法
u4 *resolveNativeWrapper(Class *class, MethodBlock *mb, u4 *ostack) {
    void *func = resolveNativeMethod(mb);

    if(func == NULL) {  // zeng: 找不到本地方法
        signalException("java/lang/UnsatisfiedLinkError", mb->name);
        return ostack;
    }

    // zeng: 执行本地方法 将结果返回
    return (*(u4 *(*)(Class*, MethodBlock*, u4*))func)(class, mb, ostack);
}

void initialiseDll() {
    // zeng: jni 哈希表 - 分配内存 初始化
#ifndef NO_JNI
    initHashTable(hash_table, HASHTABSZE);
#endif
}

#ifndef NO_JNI
typedef struct {
    char *name;
    void *handle;
} DllEntry;

// zeng: 取hash值
int dllNameHash(char *name) {
    int hash = 0;

    while(*name)
        hash = hash * 37 + *name++;

    return hash;
}

// zeng: 打开动态库, 并把handler放入hash表
int resolveDll(char *name) {
    DllEntry *dll;

    TRACE(("<Dll: Attempting to resolve library %s>\n", name));

#define HASH(ptr) dllNameHash(ptr)
#define COMPARE(ptr1, ptr2, hash1, hash2) \
                  ((hash1 == hash2) && (strcmp(ptr1, ptr2->name) == 0))
#define PREPARE(ptr) ptr
#define SCAVENGE(ptr) FALSE
#define FOUND(ptr)

    // zeng: hash 表是否已存在
    findHashEntry(hash_table, name, dll, FALSE, FALSE);

    if(dll == NULL) {
        DllEntry *dll2;

        // zeng: 打开动态库, 开启`延迟绑定`, 返回handler
        void *handle = dlopen(name, RTLD_LAZY);

        if(handle == NULL)
            return 0;

        TRACE(("<Dll: Successfully opened library %s>\n",name));

        // zeng: 分配DllEntry空间
        dll = (DllEntry*)malloc(sizeof(DllEntry));
        if(dll == NULL)
            return -1;

        // zeng: 设置DllEntry信息
        dll->name = strcpy((char*)malloc(strlen(name)+1), name);
        dll->handle = handle;

        #undef HASH
        #undef COMPARE
        #define HASH(ptr) dllNameHash(ptr->name)
        // zeng: 名称相同即同一个动态库
        #define COMPARE(ptr1, ptr2, hash1, hash2) \
                  ((hash1 == hash2) && (strcmp(ptr1->name, ptr2->name) == 0))

        // zeng: 加入hash表
        findHashEntry(hash_table, dll, dll2, TRUE, FALSE);
    }

    return 1;
}

char *getDllPath() {
    return getenv("LD_LIBRARY_PATH");
}

// zeng: 路径名 + 动态库名 拼成 动态库全限定名
char *getDllName(char *path, char *name) {
   static char buff[256];

   // zeng: 拼成全限定名
   sprintf(buff, "%s/lib%s.so", path, name);

   return buff;
}

// zeng: 从加载的 动态链接库 方法hash表 中查找native方法
void *lookupLoadedDlls0(char *name) {
    TRACE(("<Dll: Looking up %s in loaded DLL's>\n", name));

    #define ITERATE(ptr)                                   \
    {                                                      \
        void *sym = dlsym(((DllEntry*)ptr)->handle, name); \    // zeng: 从动态链接库中根据方法名查找符号 返回方法地址
        if(sym) return sym;                                \
    }

    // zeng: 遍历 加载的 动态链接库 hash表
    hashIterate(hash_table);
    return NULL;
}

extern int extraArgSpace(MethodBlock *mb);
extern u4 *callJNIMethod(void *env, Class *class, char *sig, int extra, u4 *ostack, unsigned char *f);
// zeng: 一些有用的函数集, 用结构体封装起来, 作为 jni c方法的第一个参数, c方法可以借助这个参数调用很多函数和jvm交互
extern struct _JNINativeInterface Jam_JNINativeInterface;
extern void initJNILrefs();

// zeng: 调用动态库中的jni方法
u4 *callJNIWrapper(Class *class, MethodBlock *mb, u4 *ostack) {
    void *env = &Jam_JNINativeInterface;
    u4 *ret;

    // zeng: 设置栈帧, 以配合jni方法的调用
    initJNILrefs();

    // zeng: 调用动态库中的jni方法
    return callJNIMethod(&env, (mb->access_flags & ACC_STATIC) ? class : NULL,
                         mb->type, mb->native_extra_args, ostack, mb->code);
}

// zeng: 从加载的 动态链接库 中查找native方法
void *lookupLoadedDlls(MethodBlock *mb) {
    char *mangled = mangleClassAndMethodName(mb);   // zeng: 字符串 Java_类名_方法名\0
    void *func = lookupLoadedDlls0(mangled);    // zeng: 从加载的 动态链接库 中查找

    if(func == NULL) {
        /* zeng:
             Dynamic linkers resolve entries based on their names. A native method name is concatenated from the following components:

            the prefix Java_
            a mangled fully-qualified class name
            an underscore (“_”) separator
            a mangled method name
            for overloaded native methods, two underscores (“__”) followed by the mangled argument signature

         */
        char *mangledSig = mangleSignature(mb);

        if(*mangledSig != '\0') {   // zeng: 如果有方法描述符
            char *fullyMangled = (char*)malloc(strlen(mangled)+strlen(mangledSig)+3);

            sprintf(fullyMangled, "%s__%s", mangled, mangledSig);   // zeng: java`方法重写` 的c方法命名

            func = lookupLoadedDlls0(fullyMangled);

            free(fullyMangled);
        }

        free(mangledSig);
    }

    free(mangled);

    if(func) {
        mb->code = (unsigned char *) func;  // zeng: 这东西不是java字节码指令吧, 为什么也设置为code下?  不是用来解释执行的, 具体使用见callJNIWrapper
	    mb->native_extra_args = extraArgSpace(mb); // zeng: 方法参数个数

        return mb->native_invoker = (void*) callJNIWrapper; // zeng: 找到的native方法还要代理一层, 再设为native_invoker
    }

    return NULL;
}
#endif
