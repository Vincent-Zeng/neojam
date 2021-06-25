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

char implements(Class *class, Class *test) {
    ClassBlock *test_cb = CLASS_CB(test);
    int i;

    for(i = 0; i < test_cb->interfaces_count; i++)
        if((class == test_cb->interfaces[i]) ||
                      implements(class, test_cb->interfaces[i]))
            return TRUE;

    if(test_cb->super)
        return implements(class, test_cb->super);

    return FALSE;
}

// zeng: test是class的子类
char isSubClassOf(Class *class, Class *test) {
    for(; test != NULL && test != class; test = CLASS_CB(test)->super);

    return test != NULL;
}

char isInstOfArray(Class *class, Class *test) {
    if(isSubClassOf(class, test))
        return TRUE;
    else {
        ClassBlock *class_cb = CLASS_CB(class);
        ClassBlock *test_cb = CLASS_CB(test);

        if((class_cb->name[0] == '[') && (test_cb->element_class != NULL) && (class_cb->element_class != NULL) && (class_cb->dim == test_cb->dim))  // zeng: 都是数组 维数相同
            return isInstanceOf(class_cb->element_class, test_cb->element_class);   // zeng: test元素类型是class元素类型 的子类
        else
            return FALSE;
    }
}

// zeng: test是否是class或者是class的子类
char isInstanceOf(Class *class, Class *test) {
    if(class == test)
        return TRUE;

    if(CLASS_CB(class)->access_flags & ACC_INTERFACE)
        return implements(class, test);
    else
        if(CLASS_CB(test)->name[0] == '[')
            return isInstOfArray(class, test);       
        else
            return isSubClassOf(class, test); 
}
