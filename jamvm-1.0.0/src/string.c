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

#include <string.h>
#include "jam.h"
#include "hash.h"

#define HASHTABSZE 1<<10
#define HASH(ptr) stringHash(ptr)
#define COMPARE(ptr1, ptr2, hash1, hash2) (ptr1 == ptr2) || \
                  ((hash1 == hash2) && stringComp(ptr1, ptr2))
#define ITERATE(ptr)  markObject(ptr)   // zeng: 遍历hash表时每个元素都调用markObject对象
#define PREPARE(ptr) ptr
#define SCAVENGE(ptr) FALSE
#define FOUND(ptr)

extern void markObject(Object *ob);

static Class *string;
static int count_offset; 
static int value_offset;
static int offset_offset;

static HashTable hash_table;

static int inited = FALSE;

int stringHash(Object *ptr) {
    Object *array = (Object*)INST_DATA(ptr)[value_offset]; 
    int len = INST_DATA(ptr)[count_offset];
    int offset = INST_DATA(ptr)[offset_offset];
    short *dpntr = ((short*)INST_DATA(array))+offset+2;
    int hash = 0;

    for(; len > 0; len--)
        hash = hash * 37 + *dpntr++;

    return hash;
}

int stringComp(Object *ptr, Object *ptr2) {
    int len = INST_DATA(ptr)[count_offset];
    int len2 = INST_DATA(ptr2)[count_offset];

    if(len == len2) {
        Object *array = (Object*)INST_DATA(ptr)[value_offset];
        Object *array2 = (Object*)INST_DATA(ptr2)[value_offset];
        int offset = INST_DATA(ptr)[offset_offset];
        int offset2 = INST_DATA(ptr2)[offset_offset];
        short *src = ((short*)INST_DATA(array))+offset+2;
        short *dst = ((short*)INST_DATA(array2))+offset2+2;

        for(; (len > 0) && (*src++ == *dst++); len--);

        if(len == 0)
            return TRUE;
    }

    return FALSE;
}

// zeng: 创建String对象
Object *createString(unsigned char *utf8) {
    int len = utf8Len(utf8);
    Object *array;
    short *data;
    Object *ob;

    if(!inited)
        initialiseString();

    if((array = allocTypeArray(T_CHAR, len)) == NULL ||
       (ob = allocObject(string)) == NULL)
        return NULL;

    // zeng: utf8字符数组 复制到 array对象内容体中
    data = (short*)INST_DATA(array)+2;
    convertUtf8(utf8, data);

    // zeng: String对象内容体先是字符个数 然后是字符数组对象地址
    INST_DATA(ob)[count_offset] = len; 
    INST_DATA(ob)[value_offset] = (u4)array; 

    return ob;
}

// zeng: 是否已经有内容中字符完全一致的String对象, 如果有返回旧对象, 如果没有将新对象加入hash表
Object *findInternedString(Object *string) {
    Object *interned;

    findHashEntry(hash_table, string, interned, TRUE, FALSE);

    return interned;
}

// zeng: String对象hash表中所有对象(所有和constant_pool有关的String对象)都做标记
void markInternedStrings() {
    hashIterate(hash_table);
}


Object *Cstr2String(char *cstr) {
    // zeng: 分配一个String对象
    Object *ob = allocObject(string);

    Object *array;
    MethodBlock *mb;

    int len = strlen(cstr);

    char *spntr = cstr;
    short *apntr;

    // zeng: void <init>(char[]) 方法
    if((mb = findMethod(string, "<init>", "([C)V")) == NULL) {
        printf("No constructor");
        exit(0);
    }

    // zeng: 分配字符数组对象
    array = allocTypeArray(T_CHAR, len);

    /* copy string */

    // zeng: 取数组内容空间开始地址
    apntr = ((short *)INST_DATA(array)) + 2;

    // zeng: 将 c字符数组 写入 java字符数组
    for(; len > 0; len--)
        *apntr++ = *spntr++;

    // zeng: 执行 String类构造方法, 参数 为 java字符数组
    executeMethod(ob, mb, array);

    // zeng: 返回初始化过的String object
    return ob;
}


char *String2Cstr(Object *string) {
    Object *array =(Object *)(INST_DATA(string)[value_offset]);
    int len = INST_DATA(string)[count_offset];
    int offset = INST_DATA(string)[offset_offset];
    char *cstr = (char *)malloc(len + 1), *spntr;
    short *str = ((short*)INST_DATA(array))+offset+2;

    for(spntr = cstr; len > 0; len--)
        *spntr++ = *str++;

    *spntr = '\0';
    return cstr;
}

void initialiseString() {
    if(!inited) {
        FieldBlock *count, *value, *offset;

        /* As we're initialising, VM will abort if String can't be found */
        // zeng: 加载String类
        string = findSystemClass0("java/lang/String");

        // zeng; count value offset 字段
        count = findField(string, "count", "I");
        value = findField(string, "value", "[C");
        offset = findField(string, "offset", "I");

        /* findField doesn't throw an exception... */
        if((count == NULL) || (value == NULL) || (offset == NULL)) {
            printf("Error initialising VM (initialiseString)\n");
            exit(0);
        }

        // zeng: 字段在object空间中的offset
        count_offset = count->offset;
        value_offset = value->offset;
        offset_offset = offset->offset;

        // zeng: string hash表
        initHashTable(hash_table, HASHTABSZE);

        inited = TRUE;
    }
}

#ifndef NO_JNI
/* Functions used by JNI */

Object *createStringFromUnicode(short *unicode, int len) {
    Object *array = allocTypeArray(T_CHAR, len);
    short *data = (short*)INST_DATA(array)+2;
    Object *ob = allocObject(string);

    memcpy(data, unicode, len*sizeof(short));

    INST_DATA(ob)[count_offset] = len; 
    INST_DATA(ob)[value_offset] = (u4)array; 
    return ob;
}

Object *getStringCharsArray(Object *string) {
    return (Object*)INST_DATA(string)[value_offset];
}

short *getStringChars(Object *string) {
    Object *array = (Object*)INST_DATA(string)[value_offset];
    int offset = INST_DATA(string)[offset_offset];
    return ((short*)INST_DATA(array))+offset+2;
}

int getStringLen(Object *string) {
    return INST_DATA(string)[count_offset];
}

int getStringUtf8Len(Object *string) {
    return utf8CharLen(getStringChars(string), getStringLen(string));
}

char *String2Utf8(Object *string) {
    return unicode2Utf8(getStringChars(string), getStringLen(string));
}
#endif
