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

MethodBlock *findMethod(Class *class, char *methodname, char *type) {
    ClassBlock *cb = CLASS_CB(class);
    MethodBlock *mb = cb->methods;
    int i;

    for (i = 0; i < cb->methods_count; i++, mb++)
        // zeng: name 和 type 都相同
        if ((strcmp(mb->name, methodname) == 0) && (strcmp(mb->type, type) == 0))
            return mb;

    return NULL;
}

/* A class can't have two fields with the same name but different types - 
   so we give up if we find a field with the right name but wrong type...
*/
// zeng: 查找class中字段名为fieldname, 描述符为type的FieldBlock 返回FieldBlock地址
FieldBlock *findField(Class *class, char *fieldname, char *type) {
    ClassBlock *cb = CLASS_CB(class);
    FieldBlock *fb = cb->fields;
    int i;

    for (i = 0; i < cb->fields_count; i++, fb++)
        // zeng: name 和 type 都相同
        if (strcmp(fb->name, fieldname) == 0)
            if (strcmp(fb->type, type) == 0)
                return fb;
            else
                return NULL;

    return NULL;
}

// zeng: 查找class中 方法名为 methodname, 描述符为type的方法, 返回MethodBlock的地址
MethodBlock *lookupMethod(Class *class, char *methodname, char *type) {
    MethodBlock *mb;

    // zeng: cb -> methods中找
    if (mb = findMethod(class, methodname, type))
        return mb;

    // zeng: cb -> super -> methods中找
    if (CLASS_CB(class)->super)
        return lookupMethod(CLASS_CB(class)->super, methodname, type);

    return NULL;
}

// zeng: 在class对象查找 该 名称 和 描述符 对应的FieldBlock地址
FieldBlock *lookupField(Class *class, char *fieldname, char *type) {
    FieldBlock *fb;

    if (fb = findField(class, fieldname, type))
        return fb;

    // zeng: 如果本类找不到 那么在父类中查找
    if (CLASS_CB(class)->super)
        return lookupField(CLASS_CB(class)->super, fieldname, type);

    return NULL;
}

// zeng: 解析constant_pool中cp_index下的CONSTANT_Class  CONSTANT_Class -> utf8全限定名 -> 查询 加载 链接 初始化 , 然后将cp_index下的值替换成对象地址
Class *resolveClass(Class *class, int cp_index, int init) {
    // zeng: class中的constant_pool
    ConstantPool *cp = &(CLASS_CB(class)->constant_pool);
    Class *resolved_class;

    retry:
    switch (CP_TYPE(cp, cp_index)) {
        case CONSTANT_Locked:
            goto retry;

        case CONSTANT_Resolved:
            resolved_class = (Class *) CP_INFO(cp, cp_index);
            break;

        case CONSTANT_Class: {
            char *classname;
            // zeng: 获取全限定名在constant_pool中的index
            int name_idx = CP_CLASS(cp, cp_index);

            if (CP_TYPE(cp, cp_index) != CONSTANT_Class)
                goto retry;

            // zeng: 获取全限定名
            classname = CP_UTF8(cp, name_idx);

            // zeng: 通过class去加载另一个classname
            resolved_class = findClassFromClass(classname, class);

            /* If we can't find the class an exception will already have
               been thrown */

            if (resolved_class == NULL)
                return NULL;

            CP_TYPE(cp, cp_index) = CONSTANT_Locked;
            // zeng: info设置为class的地址
            CP_INFO(cp, cp_index) = (u4) resolved_class;
            // zeng: 设置type为20表示info已从符号引用替换成直接引用
            CP_TYPE(cp, cp_index) = CONSTANT_Resolved;

            break;
        }
    }

    if (init)
        initClass(resolved_class);

    return resolved_class;
}

// zeng: 解析constant_pool中cp_index下的CONSTANT_Fieldref  CONSTANT_Fieldref -> 类utf8限定名 -> 查询 加载 链接 初始化 , CONSTANT_Fieldref -> 方法名称utf8, 方法描述符utf8 -> MethodBlock地址, 然后将cp_index下的值替换成MethodBlock地址
MethodBlock *resolveMethod(Class *class, int cp_index) {
    ConstantPool *cp = &(CLASS_CB(class)->constant_pool);
    MethodBlock *mb;

    retry:
    switch (CP_TYPE(cp, cp_index)) {
        case CONSTANT_Locked:
            goto retry;

        case CONSTANT_Resolved:
            mb = (MethodBlock *) CP_INFO(cp, cp_index);
            break;

        case CONSTANT_Methodref: {
            Class *resolved_class;
            char *methodname, *methodtype;
            // zeng: constant_pool 下读取 类全限定名 index
            int cl_idx = CP_METHOD_CLASS(cp, cp_index);
            // zeng: constant_pool 下读取 方法名称和描述符 index
            int name_type_idx = CP_METHOD_NAME_TYPE(cp, cp_index);

            if (CP_TYPE(cp, cp_index) != CONSTANT_Methodref)
                goto retry;

            // zeng: 方法名称
            methodname = CP_UTF8(cp, CP_NAME_TYPE_NAME(cp, name_type_idx));
            // zeng: 方法描述符
            methodtype = CP_UTF8(cp, CP_NAME_TYPE_TYPE(cp, name_type_idx));

            // zeng: 获取index对应符号对应的class对象
            resolved_class = resolveClass(class, cl_idx, TRUE);

            if (exceptionOccured())
                return NULL;

            // zeng: 在class对象查找 该 名称 和 描述符 对应的MethodBlock地址
            mb = lookupMethod(resolved_class, methodname, methodtype);

            if (mb) {
                CP_TYPE(cp, cp_index) = CONSTANT_Locked;
                CP_INFO(cp, cp_index) = (u4) mb;    // zeng: 符号引用(index) 改为 直接引用(MethodBlock地址)
                CP_TYPE(cp, cp_index) = CONSTANT_Resolved;
            } else
                signalException("java/lang/NoSuchMethodError", methodname);

            break;
        }
    }

    return mb;
}

// zeng: 解析constant_pool中cp_index下的CONSTANT_Fieldref  CONSTANT_Fieldref -> 类utf8限定名 -> 查询 加载 链接 初始化 , CONSTANT_Fieldref -> 方法名称utf8, 方法描述符utf8 -> MethodBlock地址, 然后将cp_index下的值替换成MethodBlock地址
MethodBlock *resolveInterfaceMethod(Class *class, int cp_index) {
    ConstantPool *cp = &(CLASS_CB(class)->constant_pool);
    MethodBlock *mb;

    retry:
    switch (CP_TYPE(cp, cp_index)) {
        case CONSTANT_Locked:
            goto retry;

        case CONSTANT_Resolved:
            mb = (MethodBlock *) CP_INFO(cp, cp_index);
            break;

        case CONSTANT_InterfaceMethodref: {
            Class *resolved_class;
            char *methodname, *methodtype;

            // zeng: constant_pool 下读取 类全限定名 index
            int cl_idx = CP_METHOD_CLASS(cp, cp_index);
            // zeng: constant_pool 下读取 方法名称和描述符 index
            int name_type_idx = CP_METHOD_NAME_TYPE(cp, cp_index);

            if (CP_TYPE(cp, cp_index) != CONSTANT_InterfaceMethodref)
                goto retry;

            // zeng: 方法名称
            methodname = CP_UTF8(cp, CP_NAME_TYPE_NAME(cp, name_type_idx));
            // zeng: 方法描述符
            methodtype = CP_UTF8(cp, CP_NAME_TYPE_TYPE(cp, name_type_idx));

            // zeng: 获取index对应符号对应的class对象
            resolved_class = resolveClass(class, cl_idx, TRUE);

            if (exceptionOccured())
                return NULL;

            // zeng: 在class对象查找 该 名称 和 描述符 对应的MethodBlock地址
            mb = lookupMethod(resolved_class, methodname, methodtype);

            if (mb) {
                CP_TYPE(cp, cp_index) = CONSTANT_Locked;
                CP_INFO(cp, cp_index) = (u4) mb;     // zeng: 符号引用(index) 改为 直接引用(MethodBlock地址)
                CP_TYPE(cp, cp_index) = CONSTANT_Resolved;
            } else
                signalException("java/lang/NoSuchMethodError", methodname);

            break;
        }
    }

    return mb;
}

// zeng: 解析constant_pool中cp_index下的CONSTANT_Fieldref  CONSTANT_Fieldref -> 类utf8限定名 -> 查询 加载 链接 初始化 , CONSTANT_Fieldref -> 方法名称utf8, 方法描述符utf8 -> FieldBlock地址, 然后将cp_index下的值替换成FieldBlock地址
FieldBlock *resolveField(Class *class, int cp_index) {
    ConstantPool *cp = &(CLASS_CB(class)->constant_pool);
    FieldBlock *fb;

    retry:
    switch (CP_TYPE(cp, cp_index)) {
        case CONSTANT_Locked:
            goto retry;

        case CONSTANT_Resolved:
            fb = (FieldBlock *) CP_INFO(cp, cp_index);
            break;

        case CONSTANT_Fieldref: {
            Class *resolved_class;
            char *fieldname, *fieldtype;

            // zeng: 类全限定名 index
            int cl_idx = CP_FIELD_CLASS(cp, cp_index);
            // zeng: 方法名称和描述符 index
            int name_type_idx = CP_FIELD_NAME_TYPE(cp, cp_index);

            if (CP_TYPE(cp, cp_index) != CONSTANT_Fieldref)
                goto retry;

            // zeng: 字段名称
            fieldname = CP_UTF8(cp, CP_NAME_TYPE_NAME(cp, name_type_idx));
            // zeng: 字段描述符
            fieldtype = CP_UTF8(cp, CP_NAME_TYPE_TYPE(cp, name_type_idx));

            // zeng: 获取index对应符号对应的class对象
            resolved_class = resolveClass(class, cl_idx, TRUE);

            if (exceptionOccured())
                return NULL;

            // zeng: 在class对象查找 该 名称 和 描述符 对应的FieldBlock地址
            fb = lookupField(resolved_class, fieldname, fieldtype);

            if (fb) {
                CP_TYPE(cp, cp_index) = CONSTANT_Locked;
                CP_INFO(cp, cp_index) = (u4) fb;    // zeng: 符号引用(index) 改为 直接引用(FieldBlock地址)
                CP_TYPE(cp, cp_index) = CONSTANT_Resolved;
            } else
                signalException("java/lang/NoSuchFieldError", fieldname);

            break;
        }
    }

    return fb;
}

// zeng: 根据index从constant_pool中取值 这里会为utf8创建String对象 并把constant_pool中的utf8地址替换为String对象地址
u4 resolveSingleConstant(Class *class, int cp_index) {
    ConstantPool *cp = &(CLASS_CB(class)->constant_pool);

    retry:
    switch (CP_TYPE(cp, cp_index)) {
        case CONSTANT_Locked:
            goto retry;

        case CONSTANT_String: {
            Object *string;
            int idx = CP_STRING(cp, cp_index);  // zeng: 取utf8字符串的constant_pool index
            if (CP_TYPE(cp, cp_index) != CONSTANT_String)
                goto retry;

            string = createString(CP_UTF8(cp, idx));    // zeng: 取得ut8字符串, 创建string对象
            CP_TYPE(cp, cp_index) = CONSTANT_Locked;
            CP_INFO(cp, cp_index) = (u4) findInternedString(string);    // zeng: 如果string hash表已经有一个内容中字符完全一致的对象,就使用hash表中的对象就好了,让新的这个对象等待gc
            CP_TYPE(cp, cp_index) = CONSTANT_Resolved;  // zeng: 字符串 hash表中取得的字符串的地址 已变成 String对象的地址了, 这也算是 符号引号 -> 直接引用 吧(把`hash表中取得的字符串的地址`视为符号)
            break;
        }

        default:
            break;
    }

    return CP_INFO(cp, cp_index);
}
