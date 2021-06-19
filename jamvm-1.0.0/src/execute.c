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
#include "sig.h"
#include "frame.h"

#define VA_DOUBLE(args, sp)  *(u8*)sp = va_arg(args, u8); sp+=2
#define VA_SINGLE(args, sp)  *sp++ = va_arg(args, u4)

#define JA_DOUBLE(args, sp) *((u8*)sp)++ = *args++

#define JA_DOUBLE_new(args, sp)  \
  do{			     \
    u8 *temp = (u8 *)sp;     \
    *temp = *args++;	     \
    temp++;		     \
    sp = temp;		     \
  }while(0)

#define JA_SINGLE(args, sp)  *sp++ = *(u4*)args; args++

// zeng: TODO
void *executeMethodArgs(Object *ob, Class *class, MethodBlock *mb, ...) {
    va_list jargs;
    void *ret;

    // zeng: 初始化可变参数获取
    va_start(jargs, mb);
    ret = executeMethodVaList(ob, class, mb, jargs);
    // zeng: 结束可变参数获取
    va_end(jargs);

    return ret;
}

void *executeMethodVaList(Object *ob, Class *class, MethodBlock *mb, va_list jargs) {
    ClassBlock *cb = CLASS_CB(class);
    char *sig = mb->type;

    // zeng: 获取当前线程的执行上下文
    ExecEnv *ee = getExecEnv();

    void *ret;
    u4 *sp;

    // zeng: 分配新的栈帧 sp是新栈帧中的本地变量数组的地址 TODO 其实是返回值地址的地址?
    CREATE_TOP_FRAME(ee, class, mb, sp, ret);

    /* copy args onto stack */

    // zeng: 如果是调用实例方法 将实例对象地址作为第一个参数保存到本地变量数组中
    if(ob)
        *sp++ = (u4) ob; /* push receiver first */

    // zeng: 从方法描述符中读取参数类型 然后根据类型从可变参数中得到值并依次保存到本地变量数组中
    SCAN_SIG(sig, VA_DOUBLE(jargs, sp), VA_SINGLE(jargs, sp))

    // zeng: 如果是synchronized方法 则等待class锁
    if(mb->access_flags & ACC_SYNCHRONIZED)
        objectLock(ob ? ob : (Object*)mb->class);

    if(mb->access_flags & ACC_NATIVE)   // zeng: 如果是本地方法 则调用native_invoker TODO
        (*(u4 *(*)(Class*, MethodBlock*, u4*))mb->native_invoker)(class, mb, ret);
    else
        executeJava();  // zeng: 解释执行

    // zeng: 释放class锁
    if(mb->access_flags & ACC_SYNCHRONIZED)
        objectUnlock(ob ? ob : (Object*)mb->class);

    // zeng: 返回到上一个方法的栈帧
    POP_TOP_FRAME(ee);

    return ret;
}

void *executeMethodList(Object *ob, Class *class, MethodBlock *mb, u8 *jargs) {
    ClassBlock *cb = CLASS_CB(class);
    char *sig = mb->type;

    ExecEnv *ee = getExecEnv();
    void *ret;
    u4 *sp;

    CREATE_TOP_FRAME(ee, class, mb, sp, ret);

    /* copy args onto stack */

    if(ob)
        *sp++ = (u4) ob; /* push receiver first */

    //SCAN_SIG(sig, JA_DOUBLE(jargs, sp), JA_SINGLE(jargs, sp))
    sig++; 
    while(*sig != ')') { 
      if((*sig == 'J') || (*sig == 'D')) { 
	//*((u8*)sp)++ = *jargs++; 
	u8 *temp = (u8 *)sp;
	*temp = *jargs++;
	temp++;
	sp = temp;

	sig++; 
      } 
      else { 
	*sp++ = *(u4*)jargs; 
	jargs++; 
	if(*sig == '[') 
	  for(sig++; *sig == '['; sig++)
	    ; 
	if(*sig == 'L') 
	  while(*sig++ != ';')
	    ; 
	else 
	  sig++; 
      } 
    } 
    sig++;

    if(mb->access_flags & ACC_SYNCHRONIZED)
        objectLock(ob ? ob : (Object*)mb->class);

    if(mb->access_flags & ACC_NATIVE)
        (*(u4 *(*)(Class*, MethodBlock*, u4*))mb->native_invoker)(class, mb, ret);
    else
        executeJava();

    if(mb->access_flags & ACC_SYNCHRONIZED)
        objectUnlock(ob ? ob : (Object*)mb->class);

    POP_TOP_FRAME(ee);
    return ret;
}
