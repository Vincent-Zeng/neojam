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

#ifdef NO_JNI
#error to use classpath, Jam must be compiled with JNI!
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <errno.h>

#include "jam.h"
#include "thread.h"
#include "lock.h"

/* java.lang.VMObject */

u4 *getClass(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *ob = (Object *) *ostack;    // zeng: 获得对象地址

    // zeng: ob -> class , 入栈
    *ostack++ = (u4) ob->class;

    return ostack;
}

u4 *jamClone(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *ob = (Object *) *ostack;
    *ostack++ = (u4) cloneObject(ob);
    return ostack;
}

/* static method wait(Ljava/lang/Object;JI)V */
u4 *wait(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *obj = (Object *) ostack[0];
    long long ms = *((long long *) &ostack[1]);
    int ns = ostack[3];

    objectWait(obj, ms, ns);
    return ostack;
}

/* static method notify(Ljava/lang/Object;)V */
u4 *notify(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *obj = (Object *) *ostack;
    objectNotify(obj);
    return ostack;
}

/* static method notifyAll(Ljava/lang/Object;)V */
u4 *notifyAll(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *obj = (Object *) *ostack;
    objectNotifyAll(obj);
    return ostack;
}

/* java.lang.VMSystem */

/* arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V */
// zeng: 复制数组内容 实现上大致就是使用memmove操作数组内容体
u4 *arraycopy(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *src = (Object *) ostack[0];
    int start1 = ostack[1];

    Object *dest = (Object *) ostack[2];
    int start2 = ostack[3];

    int length = ostack[4];


    if ((src == NULL) || (dest == NULL))
        signalException("java/lang/NullPointerException", NULL);
    else {
        ClassBlock *scb = CLASS_CB(src->class);
        ClassBlock *dcb = CLASS_CB(dest->class);
        int *sdata = INST_DATA(src);
        int *ddata = INST_DATA(dest);

        if ((scb->name[0] != '[') || (dcb->name[0] != '['))
            goto storeExcep;

        if ((start1 < 0) || (start2 < 0) || (length < 0)
            || ((start1 + length) > sdata[0]) || ((start2 + length) > ddata[0])) {
            signalException("java/lang/ArrayIndexOutOfBoundsException", NULL);
            return ostack;
        }

        if (isInstanceOf(dest->class, src->class)) {
            int size;

            switch (scb->name[1]) {
                case 'B':
                    size = 1;
                    break;
                case 'C':
                case 'S':
                    size = 2;
                    break;
                case 'I':
                case 'F':
                case 'L':
                case '[':
                    size = 4;
                    break;
                case 'J':
                case 'D':
                    size = 8;
                    break;
            }

            memmove(((char *) &ddata[1]) + start2 * size,
                    ((char *) &sdata[1]) + start1 * size,
                    length * size);
        } else {
            Object **sob, **dob;
            int i;

            if (!(((scb->name[1] == 'L') || (scb->name[1] == '[')) &&
                  ((dcb->name[1] == 'L') || (dcb->name[1] == '['))))
                goto storeExcep;

            /* Not compatible array types, but elements may be compatible...
               e.g. src = [Ljava/lang/Object, dest = [Ljava/lang/String, but all src = Strings -
               check one by one...
             */

            if (scb->dim != dcb->dim)
                goto storeExcep;

            sob = (Object **) &sdata[start1 + 1];
            dob = (Object **) &ddata[start2 + 1];

            if (scb->dim == 1)
                for (i = 0; i < length; i++) {
                    if (*sob && !isInstanceOf(dcb->element_class, (*sob)->class))
                        goto storeExcep;
                    *dob++ = *sob++;
                }
            else
                for (i = 0; i < length; i++) {
                    if (*sob && !isInstanceOf(dcb->element_class, CLASS_CB((*sob)->class)->element_class))
                        goto storeExcep;
                    *dob++ = *sob++;
                }
        }
    }
    return ostack;

    storeExcep:
    signalException("java/lang/ArrayStoreException", NULL);
    return ostack;
}

u4 *identityHashCode(Class *class, MethodBlock *mb, u4 *ostack) {
    return ++ostack;
}

/* java.lang.Runtime */

// zeng: 空闲heap大小 入栈
u4 *freeMemory(Class *class, MethodBlock *mb, u4 *ostack) {
    *((u8 *) ostack)++ = (u8) freeHeapMem();

    return ostack;
}

// zeng: heap大小 入栈
u4 *totalMemory(Class *class, MethodBlock *mb, u4 *ostack) {
    *((u8 *) ostack)++ = (u8) totalHeapMem();

    return ostack;
}

// zeng: heap上限 入栈
u4 *maxMemory(Class *class, MethodBlock *mb, u4 *ostack) {
    *((u8 *) ostack)++ = (u8) maxHeapMem();

    return ostack;
}

u4 *gc(Class *class, MethodBlock *mb, u4 *ostack) {
    gc1();  // zeng: 执行gc

    return ostack;
}

u4 *runFinalization(Class *class, MethodBlock *mb, u4 *ostack) {
    return ostack;
}

u4 *exitInternal(Class *class, MethodBlock *mb, u4 *ostack) {
    exit(0);
}

// zeng: 打开动态库, 并把handler放入hash表
u4 *nativeLoad(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 动态库 路径及名称
    char *name = String2Cstr((Object *) ostack[1]);

    // zeng: 打开动态库, 并把handler放入hash表. 返回值表示加载成功与否
    ostack[0] = resolveDll(name);

    free(name);

    return ostack + 1;
}

// zeng: 路径名 + 动态库名 拼成 动态库全限定名
u4 *nativeGetLibname(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 路径名
    char *path = String2Cstr((Object *) ostack[0]);
    // zeng: 动态库名
    char *name = String2Cstr((Object *) ostack[1]);
    // zeng: 拼成动态库全限定名, String对象地址入栈
    *ostack++ = (u4) Cstr2String(getDllName(path, name));

    return ostack;
}

void setProperty(Object *this, char *key, char *value) {
    // zeng: key
    Object *k = Cstr2String(key);
    // zeng: value
    Object *v = Cstr2String(value);

    // zeng: 获取类中的`Object put(Object arg1, Object arg2)`方法
    MethodBlock *mb = lookupMethod(this->class, "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

    // zeng: 执行方法, 参数为 key value
    executeMethod(this, mb, k, v);
}

// zeng: 把java属性设置进对象中
u4 *insertSystemProperties(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 栈中获取对象地址
    Object *this = (Object *) *ostack;

    setProperty(this, "java.version", "");
    setProperty(this, "java.vendor", "");
    setProperty(this, "java.vendor.url", "");
    setProperty(this, "java.home", "");
    setProperty(this, "java.vm.specification.version", "2");
    setProperty(this, "java.vm.specification.vendor", "");
    setProperty(this, "java.vm.specification.name", "");
    setProperty(this, "java.class.version", "");
    setProperty(this, "java.class.path", getClassPath());
    setProperty(this, "java.library.path", getDllPath());
    setProperty(this, "java.io.tmpdir", "");
    setProperty(this, "java.compiler", "");
    setProperty(this, "java.ext.dirs", "");
    setProperty(this, "os.name", "");
    setProperty(this, "os.arch", "");
    setProperty(this, "os.version", "");
    setProperty(this, "file.separator", "/");
    setProperty(this, "path.separator", ":");
    setProperty(this, "line.separator", "\n");
    setProperty(this, "user.name", getenv("USER"));
    setProperty(this, "user.home", getenv("HOME"));
    setProperty(this, "user.dir", getenv("HOME"));

    return ostack;
}

/* java.lang.Class */

/* forName0(Ljava/lang/String;IL/java/lang/ClassLoader)Ljava/lang/Class; */
// zeng: 查找 加载 链接 初始化 class
u4 *forName0(Class *clazz, MethodBlock *mb, u4 *ostack) {
    Object *string = (Object *) ostack[0];  // zeng: 类名
    int resolve = ostack[1];    //zeng: 是否初始化类
    Object *loader = (Object *) ostack[2];  // zeng: classloader地址
    char *cstr = String2Cstr(string);   // zeng: 转为c字符串
    Class *class;
    int i;

    // 替换 . 为 /
    for (i = 0; i < strlen(cstr); i++)
        if (cstr[i] == '.') cstr[i] = '/';

    // zeng: 查找 加载 链接 class
    class = findClassFromClassLoader(cstr, loader);

    // zeng: 释放c字符串空间
    free(cstr);

    if (class == NULL) {
        clearException();
        signalException("java/lang/ClassNotFoundException", NULL);
    } else if (resolve)
        initClass(class);   // zeng: 执行初始化方法

    *ostack++ = (u4) class; // zeng: class地址入栈

    return ostack;
}

u4 *isInstance(Class *class, MethodBlock *mb, u4 *ostack) {
    Class *clazz = (Class *) ostack[0]; // zeng: class对象地址
    Object *ob = (Object *) ostack[1];  // zeng: 对象地址

    // zeng: ob类是否class类或者class的子类, 结果入栈
    *ostack++ = ob == NULL ? FALSE : (u4) isInstanceOf(clazz, ob->class);

    return ostack;
}

// zeng: 类 是否 另一个类 或者是另一个类的子类
u4 *isAssignableFrom(Class *class, MethodBlock *mb, u4 *ostack) {
    Class *clazz = (Class *) ostack[0];
    Class *clazz2 = (Class *) ostack[1];

    if (clazz2 == NULL)
        signalException("java/lang/NullPointerException", NULL);
    else
        *ostack++ = (u4) isInstanceOf(clazz, clazz2);

    return ostack;
}

u4 *isInterface(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 栈中取得class对象地址, 进而取得ClassBlock
    ClassBlock *cb = CLASS_CB((Class *) ostack[0]);

    // zeng: 是否是接口类, 入栈
    *ostack++ = IS_INTERFACE(cb) ? TRUE : FALSE;

    return ostack;
}

u4 *isPrimitive(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 栈中取得class对象地址, 进而取得ClassBlock
    ClassBlock *cb = CLASS_CB((Class *) ostack[0]);

    // zeng: 是否是基本类型, 入栈
    *ostack++ = IS_PRIMITIVE(cb) ? TRUE : FALSE;

    return ostack;
}

u4 *getSuperclass(Class *class, MethodBlock *mb, u4 *ostack) {
    ClassBlock *cb = CLASS_CB((Class *) ostack[0]); // zeng: 从操组数栈中获取class地址, 进而取得ClassBlock

    *ostack++ = (u4) (IS_PRIMITIVE(cb) || IS_INTERFACE(cb) ? NULL : cb->super); // zeng: cb->super, 入栈

    return ostack;
}

u4 *newInstance(Class *clazz, MethodBlock *mb, u4 *ostack) {
    Class *class = (Class *) *ostack;  // zeng: class对象地址
    Object *ob = allocObject(class);    // zeng: 分配对象

    // zeng: 执行void <init>()方法
    MethodBlock *init = findMethod(class, "<init>", "()V");
    executeMethod(ob, init);

    *ostack++ = (u4) ob;    // zeng: 对象地址入栈

    return ostack;
}

u4 *getName(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: ostack中栈顶是对象地址 所以*ostack就是对象地址  这里取到该对象的类名
    unsigned char *dot_name = slash2dots(CLASS_CB(((Class *) *ostack))->name);
    Object *string = createString(dot_name);    // zeng: 创建String对象
    *ostack++ = (u4) string;    // zeng: 原来的对象地址出栈 string对象地址入栈(其实这里ostack地址也是ret地址, 所以其实这里是赋值给ret作为返回值)
    free(dot_name); // zeng: 释放空间

    return ostack;
}

// zeng: 获取类的<init>方法对应的Constructor对象 对象地址入栈
u4 *getConstructor(Class *class, MethodBlock *mb, u4 *ostack) {
    Class *clazz = (Class *) ostack[0]; // zeng: class对象地址
    Object *array = (Object *) ostack[1];   // zeng: 参数数组地址

    *ostack++ = (u4) getClassConstructor(clazz, array);

    return ostack;
}

// zeng: 获取加载指定类的classloader
u4 *getClassLoader0(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 类的class对象
    Class *clazz = (Class *) *ostack;
    // zeng: 获取classloader 入栈
    *ostack++ = (u4) CLASS_CB(clazz)->class_loader;
    return ostack;
}

/* java.lang.Throwable */

u4 *fillInStackTrace(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *this = (Object *) *ostack;

    setStackTrace(this);
    return ostack + 1;
}

u4 *printStackTrace0(Class *class, MethodBlock *m, u4 *ostack) {
    Object *this = (Object *) *ostack;
    Object *writer = (Object *) ostack[1];

    printStackTrace(this, writer);
    return ostack;
}

/* java.lang.VMSecurityManager */

u4 *currentClassLoader(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: NULL入栈
    *ostack++ = (u4) NULL;

    return ostack;
}

// zeng: 当前调用链上的所有class对象依次加入数组中, 数组对象地址入栈
u4 *getClassContext(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 数组类class对象
    Class *class_class = findArrayClass("[Ljava/lang/Class;");
    Object *array;
    int *data;

    // zeng: 当前栈帧
    Frame *bottom, *last = getExecEnv()->last_frame;
    int depth = 0;
/* 
    for(; last->mb != NULL && isInstanceOf(throw_class, last->mb->class);
          last = last->prev);
*/
    bottom = last;
    do {
        for (; last->mb != NULL; last = last->prev, depth++);
    } while ((last = last->prev)->prev != NULL);

    // zeng: 分配数组
    array = allocArray(class_class, depth, 4);

    if (array != NULL) {
        data = INST_DATA(array);

        depth = 1;
        do {
            for (; bottom->mb != NULL; bottom = bottom->prev)   // zeng: 遍历栈帧
                data[depth++] = (int) bottom->mb->class;    // zeng: 栈帧方法所在class对象进入数组
        } while ((bottom = bottom->prev)->prev != NULL);
    }

    // zeng: 数组对象入栈
    *ostack++ = (int) array;

    return ostack;
}

/* java.lang.VMClassLoader */

/* getPrimitiveClass(Ljava/lang/String;)Ljava/lang/Class; */
// zeng: 获取基本类型的class对象
u4 *getPrimitiveClass(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 类型名
    Object *string = (Object *) *ostack;
    char *cstr = String2Cstr(string);

    // zeng: 获取class对象 入栈
    *ostack++ = (u4) findPrimClass(cstr);

    free(cstr);

    return ostack;
}

// zeng: 解析与链接类
u4 *defineClass0(Class *clazz, MethodBlock *mb, u4 *ostack) {
    // zeng: 操作数栈中取调用参数

    Object *class_loader = (Object *) ostack[0] // zeng: classloader地址
    Object *string = (Object *) ostack[1];
    Object *array = (Object *) ostack[2];   // zeng: 字节码数据数组
    int offset = ostack[3]; // zeng: 从data + offset开始解析字节码数据
    int len = ostack[4];    // zeng: data字节数
    char *data = ((char *) INST_DATA(array)) + 4;   // zeng: 字节码数据数组内容体

    // zeng: 根据字节码数据构建Class对象
    Class *class = defineClass(data, offset, len, class_loader);

    // zeng: 链接
    if (class != NULL)
        linkClass(class);

    // zeng: 参数出栈, Class对象地址入栈
    *ostack++ = (int) class;

    return ostack;
}

// zeng: 主要就是执行类的初始化方法
u4 *resolveClass0(Class *class, MethodBlock *mb, u4 *ostack) {
    // zeng: 操作数栈中获取class对象地址
    Class *clazz = (Class *) *ostack++;

    // zeng: 执行类的初始化方法
    initClass(clazz);

    return ostack;
}

/* java.lang.reflect.Constructor */
// zeng: 调用方法
u4 *constructNative(Class *class, MethodBlock *mb2, u4 *ostack) {
    // zeng: 参数数组地址
    Object *array = (Object *) ostack[1];
    // zeng: 类的class对象地址
    Class *clazz = (Class *) ostack[2];
    // zeng: MethodBlock地址
    MethodBlock *mb = (MethodBlock *) ostack[3];
    // zeng: 给类分配一个对象
    Object *ob = allocObject(clazz);
    // zeng: 调用方法, 返回值入栈
    *ostack++ = *(u4 *) invoke(ob, clazz, mb, array);

    return ostack;
}

/* java.lang.VMString */

/* static method - intern(Ljava/lang/String;)Ljava/lang/String; */
u4 *intern(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *string = (Object *) ostack[0];  // zeng: String对象地址

    // zeng: 是否已经有内容中字符完全一致的String对象, 如果有返回旧对象, 如果没有将新对象加入hash表
    // zeng: 找到的String对象地址 替换 原String对象地址
    ostack[0] = (u4) findInternedString(string);

    return ostack + 1;
}

/* java.lang.Thread */

/* static method currentThread()Ljava/lang/Thread; */
u4 *currentThread(Class *class, MethodBlock *mb, u4 *ostack) {
    *ostack++ = (u4) getExecEnv()->thread;
    return ostack;
}

/* instance method nativeInit(J)V */
u4 *nativeInit(Class *class, MethodBlock *mb, u4 *ostack) {
    return ostack;
}

/* instance method start()V */
u4 *start(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *this = (Object *) *ostack;
    createJavaThread(this);
    return ostack;
}

/* static method sleep(JI)V */
u4 *jamSleep(Class *class, MethodBlock *mb, u4 *ostack) {
    long long ms = *((long long *) &ostack[0]);
    int ns = ostack[2];
    Thread *thread = threadSelf();

    threadSleep(thread, ms, ns);

    return ostack;
}

/* instance method interrupt()V */
u4 *interrupt(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *this = (Object *) *ostack;
    Thread *thread = threadSelf0(this);
    if (thread)
        threadInterrupt(thread);
    return ostack;
}

/* instance method isAlive()Z */
u4 *isAlive(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *this = (Object *) *ostack;
    Thread *thread = threadSelf0(this);
    *ostack++ = thread ? threadIsAlive(thread) : FALSE;
    return ostack;
}

/* static method yield()V */
u4 *yield(Class *class, MethodBlock *mb, u4 *ostack) {
    Thread *thread = threadSelf();
    threadYield(thread);
    return ostack;
}

/* instance method isInterrupted()Z */
u4 *isInterrupted(Class *class, MethodBlock *mb, u4 *ostack) {
    Object *this = (Object *) *ostack;
    Thread *thread = threadSelf0(this);
    *ostack++ = thread ? threadIsInterrupted(thread) : FALSE;
    return ostack;
}

/* static method interrupted()Z */
u4 *interrupted(Class *class, MethodBlock *mb, u4 *ostack) {
    Thread *thread = threadSelf();
    *ostack++ = threadInterrupted(thread);
    return ostack;
}

/* instance method nativeSetPriority()V */
u4 *nativeSetPriority(Class *class, MethodBlock *mb, u4 *ostack) {
    return ostack + 1;
}

// zeng: TODO
char *native_methods[][2] = {
        "arraycopy", (char *) arraycopy,
        "insertSystemProperties", (char *) insertSystemProperties,
        "getPrimitiveClass", (char *) getPrimitiveClass,
        "defineClass", (char *) defineClass0,
        "resolveClass", (char *) resolveClass0,
        "intern", (char *) intern,
        "forName0", (char *) forName0,
        "newInstance", (char *) newInstance,
        "isInstance", (char *) isInstance,
        "isAssignableFrom", (char *) isAssignableFrom,
        "isInterface", (char *) isInterface,
        "isPrimitive", (char *) isPrimitive,
        "getSuperclass", (char *) getSuperclass,
        "getName", (char *) getName,
        "getClass", (char *) getClass,
        "identityHashCode", (char *) identityHashCode,
        "clone", (char *) jamClone,
        "wait", (char *) wait,
        "notify", (char *) notify,
        "notifyAll", (char *) notifyAll,
        "gc", (char *) gc,
        "runFinalization", (char *) runFinalization,
        "exitInternal", (char *) exitInternal,
        "fillInStackTrace", (char *) fillInStackTrace,
        "printStackTrace0", (char *) printStackTrace0,
        "currentClassLoader", (char *) currentClassLoader,
        "getClassContext", (char *) getClassContext,
        "getConstructor", (char *) getConstructor,
        "getClassLoader0", (char *) getClassLoader0,
        "constructNative", (char *) constructNative,
        "nativeLoad", (char *) nativeLoad,
        "nativeGetLibname", (char *) nativeGetLibname,
        "freeMemory", (char *) freeMemory,
        "totalMemory", (char *) totalMemory,
        "maxMemory", (char *) maxMemory,
        "currentThread", (char *) currentThread,
        "nativeInit", (char *) nativeInit,
        "start", (char *) start,
        "sleep", (char *) jamSleep,
        "nativeInterrupt", (char *) interrupt,
        "isAlive", (char *) isAlive,
        "yield", (char *) yield,
        "isInterrupted", (char *) isInterrupted,
        "interrupted", (char *) interrupted,
        "nativeSetPriority", (char *) nativeSetPriority,
        NULL, NULL  // zeng: 用来标识结尾
};
