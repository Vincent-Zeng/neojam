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
#include "sig.h"
#include "thread.h"
#include "hash.h"

#include <ctype.h>

#define PREPARE(ptr) ptr
#define SCAVENGE(ptr) FALSE
#define FOUND(ptr)

static int verbose;
static char **classpath;

Class *java_lang_Class = NULL;

/* hash table containing loaded classes and internally
   created arrays */

#define INITSZE 1<<8
static HashTable loaded_classes;

/* Array large enough to hold all primitive classes -
 * access protected by loaded_classes hash table lock */
static Class *prim_classes[10];
static int num_prim = 0;

#define CP_TYPE(cp, i)            cp->type[i]
#define CP_INFO(cp, i)            cp->info[i]
#define CP_CLASS(cp, i)            (u2)cp->info[i]
#define CP_STRING(cp, i)            (u2)cp->info[i]
#define CP_METHOD_CLASS(cp, i)        (u2)cp->info[i]
#define CP_METHOD_NAME_TYPE(cp, i)    (u2)(cp->info[i]>>16)
#define CP_INTERFACE_CLASS(cp, i)    (u2)cp->info[i]
#define CP_INTERFACE_NAME_TYPE(cp, i)    (u2)(cp->info[i]>>16)
#define CP_FIELD_CLASS(cp, i)        (u2)cp->info[i]
#define CP_FIELD_NAME_TYPE(cp, i)    (u2)(cp->info[i]>>16)
#define CP_NAME_TYPE_NAME(cp, i)        (u2)cp->info[i]
#define CP_NAME_TYPE_TYPE(cp, i)        (u2)(cp->info[i]>>16)
#define CP_UTF8(cp, i)            (char *)(cp->info[i])

#define CP_INTEGER(cp, i)        (int)(cp->info[i])
#define CP_FLOAT(cp, i)            *(float *)&(cp->info[i])
#define CP_LONG(cp, i)            *(long long *)&(cp->info[i])
#define CP_DOUBLE(cp, i)            *(double *)&(cp->info[i])

#define READ_U1(v, p, l)    v = *p++
#define READ_U2(v, p, l)  v = (p[0]<<8)|p[1]; p+=2
#define READ_U4(v, p, l)    v = (p[0]<<24)|(p[1]<<16)|(p[2]<<8)|p[3]; p+=4
#define READ_U8(v, p, l)    v = ((u8)p[0]<<56)|((u8)p[1]<<48)|((u8)p[2]<<40) \
                            |((u8)p[3]<<32)|((u8)p[4]<<24)|((u8)p[5]<<16) \
                            |((u8)p[6]<<8)|(u8)p[7]; p+=8

#define    READ_INDEX(v, p, l)        READ_U2(v,p,l)
#define READ_TYPE_INDEX(v, cp, t, p, l)    READ_U2(v,p,l)


static Class *addClassToHash(Class *class) {
    Class *entry;

#define HASH(ptr) utf8Hash(CLASS_CB((Class *)ptr)->name)
    // zeng: 说明类的全限定名 和类的 classloader 一样 才是同一个class
#define COMPARE(ptr1, ptr2, hash1, hash2) (hash1 == hash2) && \
                     utf8Comp(CLASS_CB((Class *)ptr1)->name, CLASS_CB((Class *)ptr2)->name) && \
                     (CLASS_CB((Class*)ptr1)->class_loader == CLASS_CB((Class *)ptr2)->class_loader)

    findHashEntry(loaded_classes, class, entry, TRUE, FALSE);

    return entry;
}

Class *defineClass(char *data, int offset, int len, Object *class_loader) {
    unsigned char *ptr = (unsigned char *) data + offset;
    int cp_count, intf_count, i;
    u2 major_version, minor_version, this_idx, super_idx;
    u2 attr_count;
    u4 magic;

    ConstantPool *constant_pool;
    ClassBlock *classblock;
    Class *class, *found;
    Class **interfaces;

    // zeng: 从data读取4个字节并转为u4
    READ_U4(magic, ptr, len);

    // zeng: magic 必须为 cafebabe
    if (magic != 0xcafebabe) {
        signalException("java/lang/NoClassDefFoundError", "bad magic");
        return NULL;
    }

    // zeng: 读取major_version, minor_version. 但是似乎省略了版本校验?
    READ_U2(minor_version, ptr, len);
    READ_U2(major_version, ptr, len);

    // zeng: 分配一个Class + ClassBlock的空间 返回Class对象地址
    class = allocClass();
    if (class == NULL)
        return NULL;

    // zeng: Class之后就是ClassBlock, 所以可以方便找到
    classblock = CLASS_CB(class);
    // zeng: 解析并设置常量数
    READ_U2(cp_count = classblock->constant_pool_count, ptr, len);

    // zeng: 分配constant_pool的空间,constant_pool中包含type数组和info数组
    constant_pool = &classblock->constant_pool;
    constant_pool->type = (char *) malloc(cp_count);
    // zeng: 每个info才4个字节? 是的 大多只保存索引 utf8字符串也只保存地址而已
    constant_pool->info = (ConstantPoolEntry *)
            malloc(cp_count * sizeof(ConstantPoolEntry));

    // zeng: `解析并设置常量` i从1开始 也就是constant_pool第一项没有使用
    for (i = 1; i < cp_count; i++) {
        u1 tag;

        // zeng: 读取常量类型
        READ_U1(tag, ptr, len);
        // zeng: 设置常量类型
        CP_TYPE(constant_pool, i) = tag;

        switch (tag) {
            case CONSTANT_Class:
            case CONSTANT_String:
                // zeng: info为constant_pool数组的index
                READ_INDEX(CP_INFO(constant_pool, i), ptr, len);
                break;

            case CONSTANT_Fieldref:
            case CONSTANT_Methodref:
            case CONSTANT_NameAndType:
            case CONSTANT_InterfaceMethodref: {
                u2 idx1, idx2;

                // zeng:  info为constant_pool数组的两个index
                READ_INDEX(idx1, ptr, len);
                READ_INDEX(idx2, ptr, len);
                CP_INFO(constant_pool, i) = (idx2 << 16) + idx1;
                break;
            }

            case CONSTANT_Integer:
            case CONSTANT_Float:
                // zeng: info为int 或 float值
            READ_U4(CP_INFO(constant_pool, i), ptr, len);
                break;

            case CONSTANT_Long:
            case CONSTANT_Double:
                // zeng: Long Double在constant_pool中占两个位置, 字节码中cp_count的值已经考虑到了这点
            READ_U8(*(u8 *) &(CP_INFO(constant_pool, i)), ptr, len);
                i++;

                break;

            case CONSTANT_Utf8: {
                int length;
                unsigned char *buff, *utf8;
                // zeng: 读取字符串长度赋值为length
                READ_U2(length, ptr, len);
                // zeng: 字符串是malloc另外分配的
                buff = (unsigned char *) malloc(length + 1);
                // zeng: 复制字节码中的字符串到buff
                memcpy(buff, ptr, length);
                // zeng: buff以`\0`结尾,表示字符串
                buff[length] = '\0';
                ptr += length;

                // zeng: 该字符串是否在字符串hash表中已存在
                // CP_INFO(constant_pool,i) = (u4)utf8 = findUtf8String(buff);
                utf8 = findUtf8String(buff);
                // zeng: 将字符串地址赋值给info
                CP_INFO(constant_pool, i) = (u4) utf8;

                // zeng: 如果该字符串是从hash表中取得的,则不free
                if (utf8 != buff)
                    free(buff);

                break;
            }

            default:
                signalException("java/lang/NoClassDefFoundError", "bad constant pool tag");
                return NULL;
        }
    }

    // zeng: 读取访问标记, 这16个bit中记录了`这个Class是类还是接口、是否定义为public类型、是否定义为abstract类型等`
    READ_U2(classblock->access_flags, ptr, len);

    // zeng: 读取这个class文件中的类的CONSTANT_Class在constant_pool数组中的index
    READ_TYPE_INDEX(this_idx, constant_pool, CONSTANT_Class, ptr, len);
    // zeng: 通过CONSTANT_Class中的info得到类的全限定名, 赋值给name
    classblock->name = CP_UTF8(constant_pool, CP_CLASS(constant_pool, this_idx));

    if (strcmp(classblock->name, "java/lang/Object") == 0) { // zeng: 如果是Object类
        READ_U2(super_idx, ptr, len);
        // zeng: 读取到的index不为0
        if (super_idx) {
            signalException("java/lang/ClassFormatError", "Object has super");
            return NULL;
        }
        classblock->super_name = NULL;
    } else {
        // zeng: 读取这个class文件中的类所继承的类的CONSTANT_Class在constant_pool数组中的index
        READ_TYPE_INDEX(super_idx, constant_pool, CONSTANT_Class, ptr, len);
        // zeng: 通过CONSTANT_Class中的info得到类的全限定名, 赋值给super_name
        classblock->super_name = CP_UTF8(constant_pool, CP_CLASS(constant_pool, super_idx));
    }

    // zeng: 设置class_loader
    classblock->class_loader = class_loader;

    // zeng: implements的接口数量
    READ_U2(intf_count = classblock->interfaces_count, ptr, len);
    // zeng: 这里用的是`sizeof(Class *)` 即指针的大小 所以只用来保存Class的地址
    interfaces = classblock->interfaces =
            (Class **) malloc(intf_count * sizeof(Class *));

    for (i = 0; i < intf_count; i++) {
        u2 index;
        // zeng: 接口的CONSTANT_Class在constant_pool数组中的index
        READ_TYPE_INDEX(index, constant_pool, CONSTANT_Class, ptr, len);
        // zeng: 传入`当前类的class` 与 `接口的CONSTANT_Class在constant_pool数组中的index`, 返回新解析的类的Class地址
        interfaces[i] = resolveClass(class, index, FALSE);
        if (exceptionOccured())
            return NULL;
    }

    // zeng: 字段数
    READ_U2(classblock->fields_count, ptr, len);
    // zeng: 为FieldBlock数组分配空间
    classblock->fields = (FieldBlock *)
            malloc(classblock->fields_count * sizeof(FieldBlock));

    for (i = 0; i < classblock->fields_count; i++) {
        u2 name_idx, type_idx;

        // zeng: 读取并设置access_flags
        READ_U2(classblock->fields[i].access_flags, ptr, len);

        // zeng: 读取 字段名称`name` 和 字段描述符`type`
        READ_TYPE_INDEX(name_idx, constant_pool, CONSTANT_Utf8, ptr, len);
        READ_TYPE_INDEX(type_idx, constant_pool, CONSTANT_Utf8, ptr, len);
        classblock->fields[i].name = CP_UTF8(constant_pool, name_idx);
        classblock->fields[i].type = CP_UTF8(constant_pool, type_idx);

        // zeng: 读取 字段 属性数
        READ_U2(attr_count, ptr, len);
        for (; attr_count != 0; attr_count--) {
            u2 attr_name_idx;
            char *attr_name;
            u4 attr_length;

            // zeng: 属性名
            READ_TYPE_INDEX(attr_name_idx, constant_pool, CONSTANT_Utf8, ptr, len);
            attr_name = CP_UTF8(constant_pool, attr_name_idx);
            // zeng: 属性值长度
            READ_U4(attr_length, ptr, len);

            // zeng: 如果使用final和static同时修饰一个field字段，并且这个字段是基本类型或者String类型的，那么编译器在编译这个字段的时候，会在对应的field_info结构体中增加一个ConstantValue类型的结构体，在赋值的时候使用这个ConstantValue进行赋值；如果该field字段并没有被final修饰，或者不是基本类型或者String类型，那么将在类构造方法<cinit>()中赋值。
            if (strcmp(attr_name, "ConstantValue") == 0) {
                // constant 为该常量值 在constant_pool中的index
                READ_INDEX(classblock->fields[i].constant, ptr, len);
            } else // zeng: 似乎走不到这里? 为了容错?
                ptr += attr_length;
        }
    }

    // zeng: 方法数
    READ_U2(classblock->methods_count, ptr, len);

    // zeng: 分配MethodBlock数组
    classblock->methods = (MethodBlock *)
            malloc(classblock->methods_count * sizeof(MethodBlock));

    // zeng: 分配的内存置0
    memset(classblock->methods, 0, classblock->methods_count * sizeof(MethodBlock));

    for (i = 0; i < classblock->methods_count; i++) {
        MethodBlock *method = &classblock->methods[i];
        u2 name_idx, type_idx;

        // zeng: 读取并设置access_flags
        READ_U2(method->access_flags, ptr, len);

        // zeng: 读取并设置方法名称`name`和方法描述符`type`
        READ_TYPE_INDEX(name_idx, constant_pool, CONSTANT_Utf8, ptr, len);
        READ_TYPE_INDEX(type_idx, constant_pool, CONSTANT_Utf8, ptr, len);
        method->name = CP_UTF8(constant_pool, name_idx);
        method->type = CP_UTF8(constant_pool, type_idx);

        // zeng: 读取并设置属性数
        READ_U2(attr_count, ptr, len);

        // zeng: 属性表, 包括以下几种:
        // 这个方法的代码实现，即方法的可执行的机器指令
        // 这个方法声明的要抛出的异常信息
        // 这个方法是否被@deprecated注解表示
        // 这个方法是否是编译器自动生成的
        for (; attr_count != 0; attr_count--) {
            u2 attr_name_idx;
            char *attr_name;
            u4 attr_length;

            // zeng: 读取属性名 和 属性长度
            READ_TYPE_INDEX(attr_name_idx, constant_pool, CONSTANT_Utf8, ptr, len);
            READ_U4(attr_length, ptr, len);
            attr_name = CP_UTF8(constant_pool, attr_name_idx);

            if (strcmp(attr_name, "Code") == 0) {   // zeng: 属性是Code
                u4 code_length;
                u2 code_attr_cnt;
                int j;

                // zeng: 操作数栈大小
                READ_U2(method->max_stack, ptr, len);
                // zeng: 局部变量表大小
                READ_U2(method->max_locals, ptr, len);
                // zeng: 指令长度
                READ_U4(code_length, ptr, len);
                // zeng: 为指令分配空间
                method->code = (char *) malloc(code_length);
                // zeng: 读取并设置指令
                memcpy(method->code, ptr, code_length);
                ptr += code_length;

                // zeng: 方法中的try catch信息
                READ_U2(method->exception_table_size, ptr, len);
                // zeng: 为try catch信息数组分配空间
                method->exception_table = (ExceptionTableEntry *)
                        malloc(method->exception_table_size * sizeof(ExceptionTableEntry));


                for (j = 0; j < method->exception_table_size; j++) {
                    ExceptionTableEntry *entry = &method->exception_table[j];

                    // zeng: 如果字节码从第start_pc行到第end_pc行之间出现了catch_type所描述的异常类型，那么将跳转到handler_pc行继续处理
                    READ_U2(entry->start_pc, ptr, len);
                    READ_U2(entry->end_pc, ptr, len);
                    READ_U2(entry->handler_pc, ptr, len);
                    READ_U2(entry->catch_type, ptr, len);
                }

                // zeng: 指令属性长度
                READ_U2(code_attr_cnt, ptr, len);
                for (; code_attr_cnt != 0; code_attr_cnt--) {
                    u2 attr_name_idx;
                    u4 attr_length;

                    // zeng:属性名
                    READ_U2(attr_name_idx, ptr, len);
                    READ_U4(attr_length, ptr, len);
                    attr_name = CP_UTF8(constant_pool, attr_name_idx);

                    if (strcmp(attr_name, "LineNumberTable") == 0) {    // zeng: pc 和 源码行 的对应关系数组
                        // zeng: 关系数组长度
                        READ_U2(method->line_no_table_size, ptr, len);
                        // zeng: 分配关系数组空间
                        method->line_no_table = (LineNoTableEntry *)
                                malloc(method->line_no_table_size * sizeof(LineNoTableEntry));

                        for (j = 0; j < method->line_no_table_size; j++) {
                            LineNoTableEntry *entry = &method->line_no_table[j];

                            // zeng: pc
                            READ_U2(entry->start_pc, ptr, len);
                            // zeng: 源码行
                            READ_U2(entry->line_no, ptr, len);
                        }
                    } else
                        ptr += attr_length;
                }
            } else if (strcmp(attr_name, "Exceptions") == 0) {  // zeng: 属性是Exceptions
                int j;

                // zeng: 这个方法声明throws了几个exception
                READ_U2(method->throw_table_size, ptr, len);
                // zeng: 只有2个字节 因为存放异常类CONSTANT_Class在constant_pool中的index
                method->throw_table = (u2 *) malloc(method->throw_table_size * sizeof(u2));
                for (j = 0; j < method->throw_table_size; j++) {
                    // zeng: 读取并设置index
                    READ_U2(method->throw_table[j], ptr, len);
                }
            } else  // zeng: 走不到 容错?
                ptr += attr_length;
        }
    }

    // zeng: 本class的属性
    READ_U2(attr_count, ptr, len);
    for (; attr_count != 0; attr_count--) {
        u2 attr_name_idx;
        char *attr_name;
        u4 attr_length;

        // zeng: 属性名
        READ_U2(attr_name_idx, ptr, len);
        READ_U4(attr_length, ptr, len);
        attr_name = CP_UTF8(constant_pool, attr_name_idx);

        if (strcmp(attr_name, "SourceFile") == 0) { // zeng: 源码文件名
            u2 file_name_idx;
            READ_U2(file_name_idx, ptr, len);
            classblock->source_file_name = CP_UTF8(constant_pool, file_name_idx);
        } else
            ptr += attr_length;
    }

    // zeng: 类状态
    classblock->flags = CLASS_LOADED;

    // zeng: 放入class hash表
    found = addClassToHash(class);

    // zeng: 之前已经加载过了
    if (found != class)
        return found;

    // zeng: 加载super类并将super class的地址赋值给super
    classblock->super = super_idx ? resolveClass(class, super_idx, FALSE) : NULL;

    if (exceptionOccured())
        return NULL;

    // zeng: class -> class 为 java/lang/Class类 TODO Class类怎么用的?
    if (strcmp(classblock->name, "java/lang/Class") == 0)
        class->class = class;
    else {
        if (java_lang_Class == NULL)
            java_lang_Class = loadSystemClass("java/lang/Class");
        class->class = java_lang_Class;
    }

    return class;
}

// zeng: TODO
Class *
createArrayClass(char *classname, Object *class_loader) {
    Class *class;
    ClassBlock *classblock;
    int len = strlen(classname);

    if ((class = allocClass()) == NULL)
        return NULL;

    classblock = CLASS_CB(class);

    /* Set all fields to zero */
    memset(classblock, 0, sizeof(ClassBlock));

    classblock->name = strcpy((char *) malloc(len + 1), classname);
    classblock->super_name = "java/lang/Object";
    classblock->super = findSystemClass("java/lang/Object");
    classblock->method_table = CLASS_CB(classblock->super)->method_table;

    classblock->interfaces_count = 2;
    classblock->interfaces = (Class **) malloc(2 * sizeof(Class *));
    classblock->interfaces[0] = findSystemClass("java/lang/Cloneable");
    classblock->interfaces[1] = findSystemClass("java/io/Serializable");

    classblock->flags = CLASS_INTERNAL;

    // zeng: 如果不是基本类型
    if (classname[len - 1] == ';') {

        /* Element type is an object rather than a primitive type -
           find the element class and dimension and store in cb */

        char buff[256];
        char *ptr;
        int dim;

        /* Calculate dimension by counting the brackets */
        for (ptr = classname; *ptr == '['; ptr++);
        dim = ptr - classname;

        strcpy(buff, &classname[dim + 1]);
        buff[len - dim - 2] = '\0';

        classblock->element_class = findClassFromClassLoader(buff, class_loader);
        classblock->class_loader = CLASS_CB(classblock->element_class)->class_loader;
        classblock->dim = dim;
    }

    if (java_lang_Class == NULL)
        java_lang_Class = loadSystemClass("java/lang/Class");

    class->class = java_lang_Class;
    return addClassToHash(class);
}

// zeng: TODO
Class *
createPrimClass(char *classname) {
    Class *class;
    ClassBlock *classblock;
    int i;

    if ((class = allocClass()) == NULL)
        return NULL;

    classblock = CLASS_CB(class);
    classblock->name = strcpy((char *) malloc(strlen(classname) + 1), classname);
    classblock->methods_count = 0;
    classblock->fields_count = 0;
    classblock->interfaces_count = 0;

    classblock->flags = CLASS_INTERNAL;

    if (java_lang_Class == NULL)
        java_lang_Class = loadSystemClass("java/lang/Class");

    class->class = java_lang_Class;

    lockHashTable(loaded_classes);

    for (i = 0; (i < num_prim) && (strcmp(CLASS_CB(prim_classes[i])->name, classname) == 0); i++);
    if (i == num_prim)
        prim_classes[num_prim++] = class;
    else
        class = prim_classes[i];

    unlockHashTable(loaded_classes);
    return class;
}

// zeng: 链接祖先类的字段和方法
void linkClass(Class *class) {
    ClassBlock *cb = CLASS_CB(class);
    MethodBlock *mb = cb->methods;
    FieldBlock *fb = cb->fields;
    int spr_mthd_tbl_sze = 0;
    MethodBlock **spr_mthd_tbl;
    MethodBlock **method_table;
    MethodBlock *overridden;
    MethodBlock *finalizer = 0;
    int new_methods_count = 0;
    int offset = 0;
    int i;

    if (cb->flags >= CLASS_LINKED)
        return;

    if (verbose)
        printf("[Linking class %s]\n", cb->name);

    // zeng: 先link super class
    if (!(cb->access_flags & ACC_INTERFACE) && cb->super && (CLASS_CB(cb->super)->flags < CLASS_LINKED))
        linkClass(cb->super);

    // zeng: 父类信息
    if (cb->super) {
        offset = CLASS_CB(cb->super)->object_size;
        spr_mthd_tbl = CLASS_CB(cb->super)->method_table;
        spr_mthd_tbl_sze = CLASS_CB(cb->super)->method_table_size;
        // zeng: 父类的finalize方法作为备选
        finalizer = CLASS_CB(cb->super)->finalizer;
    }

    /* prepare fields */

    for (i = 0; i < cb->fields_count; i++, fb++) {
        if (fb->access_flags & ACC_STATIC) {    // zeng: static字段
            /* init to default value */
            if ((*fb->type == 'J') || (*fb->type == 'D'))   // zeng: 如果是Long或Double
                *(long long *) &fb->static_value = 0;   // zeng: 和类信息保存在一个空间
            else
                fb->static_value = 0;
        } else {
            /* calc field offset */
            fb->offset = offset;    // zeng: 为非static字段分配对象内容体空间中的offset
            if ((*fb->type == 'J') || (*fb->type == 'D'))
                offset += 2;
            else
                offset += 1;
        }
    }

    // zeng: 所有实例变量大小构成对象的大小(以u4为单位)
    cb->object_size = offset;

    /* prepare methods */

    for (i = 0; i < cb->methods_count; i++, mb++) {

        /* calculate argument count from signature */

        int count = 0;
        char *sig = mb->type;
        // zeng: 从描述符中统计参数数量 Double Long都算两个
        SCAN_SIG(sig, count += 2, count++);

        if (mb->access_flags & ACC_STATIC)
            mb->args_count = count;
        else    // zeng: 非static方法 参数多了一个this
            mb->args_count = count + 1;

        // zeng: method所属class
        mb->class = class;

        // zeng: native方法
        if (mb->access_flags & ACC_NATIVE) {

            /* set up native invoker to wrapper to resolve function
               on first invocation */

            // zeng: native_invoker设置为解析方法,这样第一次调用就是调用解析方法,解析方法中会找到实际方法,并设置native_invoker为实际方法
            mb->native_invoker = (void *) resolveNativeWrapper;

            /* native methods have no code attribute so these aren't filled
               in at load time - as these values are used when creating frame
               set to appropriate values */

            // zeng: TODO native方法也会用到本地变量表?
            mb->max_locals = mb->args_count;
            mb->max_stack = 0;
        }

        /* Static, private or init methods aren't dynamically invoked, so
      don't stick them in the table to save space */

        // zeng: static private init方法 不用放入method_table中
        if ((mb->access_flags & ACC_STATIC) || (mb->access_flags & ACC_PRIVATE) ||
            (mb->name[0] == '<'))
            continue;

        /* if it's overriding an inherited method, replace in method table */
        // zeng: 方法在method_table数组中的index
        if (cb->super &&
            (overridden = lookupMethod(cb->super, mb->name, mb->type)))
            mb->method_table_index = overridden->method_table_index;
        else
            mb->method_table_index = spr_mthd_tbl_sze + new_methods_count++;

        /* check for finalizer */
        // zeng: 方法是否是void finalize() 如果有 就不用父类的
        if (cb->super && strcmp(mb->name, "finalize") == 0 && strcmp(mb->type, "()V") == 0)
            finalizer = mb;
    }

    // zeng: finalize方法
    cb->finalizer = finalizer;

    /* construct method table */

    // zeng: method_table大小 为父类 method_table大小 加上本类 methods大小(不包括static private init方法)
    cb->method_table_size = spr_mthd_tbl_sze + new_methods_count;
    // zeng: 分配method_table数组空间
    method_table = cb->method_table =
            (MethodBlock **) malloc(cb->method_table_size * sizeof(MethodBlock *));

    // zeng: 复制父类method_table到本类method_table
    memcpy(method_table, spr_mthd_tbl, spr_mthd_tbl_sze * sizeof(MethodBlock *));

    /* fill in method table */

    // zeng: 将本类方法写进method_table
    mb = cb->methods;
    for (i = 0; i < cb->methods_count; i++, mb++) {
        if ((mb->access_flags & ACC_STATIC) || (mb->access_flags & ACC_PRIVATE) ||
            (mb->name[0] == '<'))
            continue;
        method_table[mb->method_table_index] = mb;
    }

    // zeng: 更新类状态
    cb->flags = CLASS_LINKED;
}

Class *initClass(Class *class) {
    ClassBlock *cb = CLASS_CB(class);
    FieldBlock *fb = cb->fields;
    ConstantPool *cp = &cb->constant_pool;
    MethodBlock *mb;
    Object *excep;
    int i;

    // zeng: 链接class
    linkClass(class);

    objectLock((Object *) class);

    while (cb->flags == CLASS_INITING)
        if (cb->initing_tid == threadSelf()->id)
            goto unlock;
        else
            objectWait((Object *) class);

    if (cb->flags == CLASS_INITED)
        goto unlock;

    if (cb->flags == CLASS_BAD) {
        objectUnlock((Object *) class);
        signalException("java/lang/NoClassDefFoundError", cb->name);
        return class;
    }

    // zeng: 更新类状态
    cb->flags = CLASS_INITING;

    // zeng: 初始化这个类的 java thread id
    cb->initing_tid = threadSelf()->id;

    objectUnlock((Object *) class);

    // zeng: 先初始化父类
    if (!(cb->access_flags & ACC_INTERFACE) && cb->super && (CLASS_CB(cb->super)->flags != CLASS_INITED)) {
        initClass(cb->super);

        if (exceptionOccured()) {
            objectLock((Object *) class);
            // zeng: 初始化失败
            cb->flags = CLASS_BAD;
            goto notify;
        }
    }

    // zeng: 执行 void <clinit>()
    if ((mb = findMethod(class, "<clinit>", "()V")) != NULL)
        executeStaticMethod(class, mb);

    if (excep = exceptionOccured()) {   // zeng: 有异常抛出
        Class *error, *eiie;
        Object *ob;

        clearException();

        /* Don't wrap exceptions of type java/lang/Error...  Sun VM
     * doesn't appear to do this, and it leads to errors such as
     * UnsatisfiedLinkError being reported as ExceptionInInit... */

        if ((error = findSystemClass0("java/lang/Error")) && !isInstanceOf(error, excep->class)
            && (eiie = findSystemClass("java/lang/ExceptionInInitializerError"))
            && (mb = findMethod(eiie, "<init>", "(Ljava/lang/Throwable;)V"))
            && (ob = allocObject(eiie))) {
            executeMethod(ob, mb, excep);
            setException(ob);
        } else
            setException(excep);

        objectLock((Object *) class);
        cb->flags = CLASS_BAD;
    } else {
        objectLock((Object *) class);
        // zeng: 初始化完成
        cb->flags = CLASS_INITED;
    }

    notify:
    objectNotifyAll((Object *) class);

    unlock:
    objectUnlock((Object *) class);
    return class;
}

Class *loadSystemClass(char *classname) {
    char filename[256] = "/";
    char buff[256];
    char *data;
    char **cp_ptr;
    FILE *cfd;
    int flen;
    Class *class;
    // zeng: 拼接class的filename
    strcat(strcat(filename, classname), ".class");
    // zeng: 遍历classpath数组,依次拼接class的绝对路径,如果文件存在则打开
    for (cp_ptr = classpath;
         *cp_ptr && !(cfd = fopen(strcat(strcpy(buff, *cp_ptr), filename), "r"));
         cp_ptr++);

    if (!*cp_ptr) {
        signalException("java/lang/NoClassDefFoundError", classname);
        return NULL;
    }

    // zeng: 获取文件大小
    fseek(cfd, 0L, SEEK_END);
    flen = ftell(cfd);
    fseek(cfd, 0L, SEEK_SET);

    // zeng: malloc开辟内存,从文件中读到内存
    data = (char *) malloc(flen);
    if (fread(data, sizeof(char), flen, cfd) != flen) {
        signalException("java/lang/NoClassDefFoundError", classname);
        return NULL;
    }

    // zeng: 读取字节码 解析成Class
    class = defineClass(data, 0, flen, NULL);

    // zeng: 释放读到的文件内存
    free(data);

    // zeng: 打印 绝对路径
    if (verbose)
        printf("[Loaded %s]\n", buff);

    return class;
}

Class *findHashedClass(char *classname, Object *class_loader) {
    Class *class;

#undef HASH
#undef COMPARE
#define HASH(ptr) utf8Hash(ptr)
#define COMPARE(ptr1, ptr2, hash1, hash2) (hash1 == hash2) && \
                         utf8Comp(ptr1, CLASS_CB((Class *)ptr2)->name) && \
                         (CLASS_CB((Class *)ptr2)->class_loader == class_loader)

    findHashEntry(loaded_classes, classname, class, FALSE, FALSE);

    return class;
}

Class *findSystemClass0(char *classname) {
    // zeng: 先从hash表找
    Class *class = findHashedClass(classname, NULL);

    // zeng: 加载class
    if (class == NULL)
        class = loadSystemClass(classname);

    // zeng: 链接class
    if (!exceptionOccured())
        linkClass(class);

    return class;
}

Class *findSystemClass(char *classname) {
    Class *class = findSystemClass0(classname);

    if (!exceptionOccured())
        // zeng: 初始化class
        initClass(class);

    return class;
}

// zeng: 根据classname 创建数组类 classname包括以基本类型为元素的数组`[B` `[C` 等
Class *findArrayClassFromClassLoader(char *classname, Object *class_loader) {
    Class *class = findHashedClass(classname, class_loader);

    if (class == NULL)
        // zeng: TODO 创建数组类
        class = createArrayClass(classname, class_loader);

    return class;
}

Class *findPrimClass(char *classname) {
    int i;
    Class *prim = NULL;

    lockHashTable(loaded_classes);
    for (i = 0; (i < num_prim) && (strcmp(CLASS_CB(prim_classes[i])->name, classname) == 0); i++);
    if (i < num_prim)
        prim = prim_classes[i];

    unlockHashTable(loaded_classes);
    return prim ? prim : createPrimClass(classname);
}

Class *findClassFromClassLoader(char *classname, Object *loader) {
    // zeng: 如果是数组
    if (*classname == '[')
        return findArrayClassFromClassLoader(classname, loader);

    // zeng: 如果classloader不为空
    if (loader != NULL) {
        Class *class;
        // zeng: 将全限行名中的/替换为.
        char *dot_name = slash2dots(classname);
        // zeng: 获取classloader.loadClass方法
        MethodBlock *mb = lookupMethod(loader->class,
                                       "loadClass", "(Ljava/lang/String;)Ljava/lang/Class;");
        // zeng: 创建String对象 因为方法参数类型是String的
        Object *string = createString(dot_name);

        free(dot_name);

        // zeng: 执行classloader.loadClass方法
        class = *(Class **) executeMethod(loader, mb, string);

        if (exceptionOccured())
            return NULL;

        return class;
    }

    // zeng: 如果classloader为空
    return findSystemClass0(classname);
}

/* gc support for marking classes */

#define ITERATE(ptr)  markClass(ptr)    // zeng: 遍历loaded_classes hash表时每个元素都调用markClass

extern void markClass(Class *ob);

// zeng 所有class对象都标记
void markClasses() {
    int i;

    hashIterate(loaded_classes);

    for (i = 0; i < num_prim; i++)
        markClass(prim_classes[i]);
}

int parseClassPath(char *cp_var) {
    char *cp, *pntr, *start;
    int i;

    cp = (char *) malloc(strlen(cp_var) + 1);
    strcpy(cp, cp_var);

    for (i = 0, start = pntr = cp; *pntr; pntr++) {
        if (*pntr == ':') {
            if (start != pntr)
                i++;
            start = pntr + 1;
        }
    }
    if (start != pntr)
        i++;

    classpath = (char **) malloc(sizeof(char *) * (i + 1));

    for (i = 0, start = pntr = cp; *pntr; pntr++) {
        if (*pntr == ':') {
            if (start != pntr) {
                *pntr = '\0';
                classpath[i++] = start;
            }
            start = pntr + 1;
        }
    }
    if (start != pntr)
        classpath[i++] = start;

    classpath[i] = NULL;
    return i;
}

char *getClassPath() {
    return getenv("CLASSPATH");
}

void initialiseClass(int verboseclass) {
    // zeng: 从环境变量获取 classpath
    char *cp = getClassPath();
    // zeng: 解析cp字符串, 写入到classpath字符串数组中
    if (!(cp && parseClassPath(cp))) {
        printf("Classpath variable is empty!\n");
        exit(1);
    }
    // zeng: 是否打类加载日志
    verbose = verboseclass;
    // zeng: 加载的class 哈希表
    initHashTable(loaded_classes, INITSZE);
}
