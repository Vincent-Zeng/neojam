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
#include <arpa/inet.h>
#include <math.h>

#include "jam.h"
#include "thread.h"
#include "lock.h"

#define CP_SINDEX(p)  p[1]
#define CP_DINDEX(p)  (p[1]<<8)|p[2]
#define BRANCH(p)     (((signed char)p[1])<<8)|p[2] // zeng: 读取2个字节为signed char值
#define BRANCH_W(p)   (((signed char)p[1])<<24)|(p[2]<<16)|(p[3]<<8)|p[4]
#define DSIGNED(p)    (((signed char)p[1])<<8)|p[2]

// zeng:抛出异常 异常类全限定名为excep_name 错误信息为message
#define THROW_EXCEPTION(excep_name, message)                          \
{                                                                     \
    frame->last_pc = (unsigned char*)pc;                              \
    signalException(excep_name, message);                             \
    goto throwException;                                              \
}

// zeng: 除数是否为0
#define ZERO_DIVISOR_CHECK(TYPE, ostack)                              \
    if(((TYPE*)ostack)[-1] == 0)                                      \
        THROW_EXCEPTION("java/lang/ArithmeticException",              \
                        "division by zero");

#define NULL_POINTER_CHECK(ref)                                       \
    if(!ref)                                                          \
        THROW_EXCEPTION("java/lang/NullPointerException", NULL);

#define ARRAY_BOUNDS_CHECK(array, i)                                  \
    if(i >= *INST_DATA(array))                                        \
        THROW_OUT_OF_BOUNDS_EXCEPTION(i);

#define THROW_OUT_OF_BOUNDS_EXCEPTION(index)                          \
{                                                                     \
    char buff[256];                                                   \
    sprintf(buff, "%d", index);                                       \
    THROW_EXCEPTION("java/lang/ArrayIndexOutOfBoundsException",       \
                                                           buff);     \
}

// zeng: 栈顶取负
#define UNARY_MINUS(TYPE, ostack, pc)                                 \
    ((TYPE*)ostack)[-1] = -((TYPE*)ostack)[-1];                       \
                                                                      \
    pc += 1;                                                          \
    DISPATCH(pc)

// zeng: 栈顶两个TYPE类型的元素出栈, 做OP操作, 结果入栈
#define BINARY_OP(TYPE, OP, ostack, pc)                               \
    ((TYPE*)ostack)[-2] = ((TYPE*)ostack)[-2] OP ((TYPE*)ostack)[-1]; \
    ostack -= sizeof(TYPE)/4;                                         \
                                                                      \
    pc += 1;                                                          \
    DISPATCH(pc)

#define SHIFT_OP(TYPE, OP, ostack, pc)                                \
{                                                                     \
    int s = *--ostack;                                                \
    ((TYPE*)ostack)[-1] = ((TYPE*)ostack)[-1] OP s;                   \
    pc += 1;                                                          \
    DISPATCH(pc)                                                      \
}

// zeng: 栈顶src_type元素 转为 dest_type元素
// SRC_TYPE v = *--(SRC_TYPE *)ostack;
// *((DEST_TYPE *)ostack)++ = (DEST_TYPE)v;                          
#define OPC_X2Y(SRC_TYPE, DEST_TYPE)                                  \
  {                                                                   \
    SRC_TYPE *p = ostack;                                             \
    p--;                                                              \
    SRC_TYPE v = *p;                                                  \
    ostack = p;                                                       \
                                                                      \
    DEST_TYPE *p2 = ostack;                                           \
    *p2 =  (DEST_TYPE)v;                                              \
    p2++;                                                             \
    ostack = p2;                                                      \
                                                                      \
    pc += 1;                                                          \
    DISPATCH(pc)                                                      \
}

#define ARRAY_LOAD(TYPE, ostack, pc)                                  \
{                                                                     \
    TYPE *element;                                                    \
    int i = ostack[-1];                              \  // zeng: 出栈, 值为index
    Object *array = (Object *)ostack[-2];                  \    //zeng: 出栈, 值为数组对象地址
    NULL_POINTER_CHECK(array);                                        \ // zeng: 没有数组对象地址
    ARRAY_BOUNDS_CHECK(array, i);                                     \ // zeng: index超出数组长度
    element = (TYPE *)(((char *)INST_DATA(array)) + (i * sizeof(TYPE)) + 4);                \   // zeng: 取得数组中index下的地址
    ostack[-2] = *element;                          \   // zeng: 取得index下的值 入栈
    ostack -= 1;                                  \     // zeng: 栈顶位置改变
                                                                      \
    pc += 1;                                      \
    DISPATCH(pc)                              \
}

#define ARRAY_LOAD_LONG(TYPE, ostack, pc)                             \
{                                                                     \
    u8 *element;                                                      \
    int i = ostack[-1];                              \
    Object *array = (Object *)ostack[-2];                  \
    NULL_POINTER_CHECK(array);                                        \
    ARRAY_BOUNDS_CHECK(array, i);                                     \
    element = (u8 *)(((char *)INST_DATA(array)) + (i << 3) + 4);      \
    ((u8*)ostack)[-1] = *element;                                     \
                                                                      \
    pc += 1;                                      \
    DISPATCH(pc)                              \
}

#define ARRAY_STORE(TYPE, ostack, pc)                                 \
{                                                                     \
    int v = ostack[-1];                              \  // zeng: 值
    int i = ostack[-2];                              \  // zeng: index
    Object *array = (Object *)ostack[-3];                  \    // zeng: 数组对象地址
    NULL_POINTER_CHECK(array);                                        \
    ARRAY_BOUNDS_CHECK(array, i);                                     \
    *(TYPE *)(((char *)INST_DATA(array))+(i * sizeof(TYPE)) + 4) = v; \ // zeng: 写入数组
    ostack -= 3;                                  \ // zeng: 更新栈顶位置
                                                            \
    pc += 1;                                      \
    DISPATCH(pc)                              \
}

#define ARRAY_STORE_LONG(TYPE, ostack, pc)                            \
{                                                                     \
    u8 v = ((u8*)ostack)[-1];                          \    // zeng: -1 -2 保存的都是value
    int i = ostack[-3];                              \
    Object *array = (Object *)ostack[-4];                  \
    NULL_POINTER_CHECK(array);                                        \
    ARRAY_BOUNDS_CHECK(array, i);                                     \
    *(u8 *)(((char *)INST_DATA(array)) + (i << 3) + 4) = v;           \
    ostack -= 4;                                  \
                                                    \
    pc += 1;                                      \
    DISPATCH(pc)                              \
}

// zeng: 栈顶两个元素出栈, 做COND操作, 结果为true时 pc 加上 code中接下来两个字节表示的偏移量, 为false时 pc 取下一条指令的地址
#define IF_ICMP(COND, ostack, pc)                                  \
{                                                  \
    int v1 = ostack[-2];                                      \
    int v2 = ostack[-1];                                           \
                                                                   \
    if(v1 COND v2) {                                          \
        pc += BRANCH(pc);                                      \
    } else                                              \
        pc += 3;                                          \
                                                                   \
    ostack -= 2;                                          \
                                                                   \
    DISPATCH(pc)                                      \
}

// zeng: 出栈, 值和0 做 COND 操作, 结果为true时 , pc 加上 code中接下来两个byte表示的偏移量(距离当前pc的偏移字节数), 为false则取下一条指令的地址
#define IF(COND, ostack, pc)                                      \
{                                                  \
    int v = *--ostack;                                          \
    if(v COND 0) {                                          \
        pc += BRANCH(pc);                                      \
    } else                                              \
        pc += 3;                                                  \
                                                                  \
    DISPATCH(pc)                                              \
}

// zeng: 栈顶两个元素出栈 比较大小 结果为 -1 0 1 中的一个 结果入栈
/* TYPE v2 = *--((TYPE *)ostack);                                    \ */
/* TYPE v1 = *--((TYPE *)ostack);                                    \ */
#define CMP(TYPE, ostack, pc)                                         \
{                                                                     \
  TYPE *p = ostack;                                                   \
                                                                      \
  p--;                                                                \
  TYPE v2 = *p;                                                       \
                                                                      \
  p--;                                                                \
  TYPE v1 = *p;                                                       \
                                                                      \
  ostack = p;                                                         \
                                                                      \
    if(v1 == v2)                                                      \
        *ostack++ = 0;                                                \
    else if(v1 < v2)                                                  \
            *ostack++ = -1;                                           \
        else                                                          \
            *ostack++ = 1;                                            \
                                                                      \
    pc += 1;                                                          \
    DISPATCH(pc)                                                      \
}

// zeng: 栈顶两个元素出栈 比较大小 结果为 -1 0 1 中的一个 结果入栈
/* TYPE v2 = *--((TYPE *)ostack);                                    \ */
/*    TYPE v1 = *--((TYPE *)ostack); */

#define FCMP(TYPE, ostack, pc, isNan)                                 \
{                                                                     \
  TYPE *p = ostack;                                                   \
                                                                      \
  p--;                                                                \
  TYPE v2 = *p;                                                       \
                                                                      \
  p--;                                                                \
  TYPE v1 = *p;                                                       \
                                                                      \
  ostack = p;                                                         \
                                                                      \
    if(v1 == v2)                                                      \
        *ostack++ = 0;                                                \
    else if(v1 < v2)                                                  \
        *ostack++ = -1;                                               \
    else if(v1 > v2)                                                  \
         *ostack++ = 1;                                               \
    else                                                              \
         *ostack++ = isNan;                                           \
                                                                      \
    pc += 1;                                                          \
    DISPATCH(pc)                                                      \
}

#define WITH_OPCODE_CHANGE_CP_DINDEX(pc, opcode, index)               \
    index = CP_DINDEX(pc);                                            \
    if(pc[0] != opcode)                                               \
        DISPATCH(pc)

#define OPCODE_REWRITE(pc, opcode)                                    \
    pc[0] = opcode

#define OPCODE_REWRITE_OPERAND1(pc, opcode, operand1)                 \
{                                                                     \
    pc[0] = OPC_LOCK;                                                 \
    pc[1] = operand1;                                                 \
    pc[0] = opcode;                                                   \
}

#define OPCODE_REWRITE_OPERAND2(pc, opcode, operand1, operand2)       \
{                                                                     \
    pc[0] = OPC_LOCK;                                                 \
    pc[1] = operand1;                                                 \
    pc[2] = operand2;                                                 \
    pc[0] = opcode;                                                   \
}

#ifdef THREADED // zeng: 串联式 分发策略 - 串联式避免每个指令都完整走一遍switch分支 而且对于cpu分支预测更有利
    /* Two levels of macros are needed to correctly produce the label
     * from the OPC_xxx macro passed into DEF_OPC as cpp doesn't
     * prescan when concatenating with ##...
     *
     * On gcc <= 2.95, we also get a space inserted before the :
     * e.g DEF_OPC(OPC_NULL) -> opc0 : - the ##: is a hack to fix
     * this, but this generates warnings on >= 2.96...
     */
    #if (__GNUC__ == 2) && (__GNUC_MINOR__ <= 95)
        #define label(x)         \
        opc##x##:
    #else
        #define label(x)         \
        opc##x:
    #endif

    // zeng: DEF_OPC(opcode) 得到 opc0: opc1: ...
    #define DEF_OPC(opcode)  \
        label(opcode)

    // zeng: 查询跳转表 并 跳转
    #define DISPATCH(pc)     \
        goto *handlers[*pc];    // zeng: pc 字节码地址 *pc 字节码

#else   // zeng: 基于switch的分发策略

    #define DEF_OPC(opcode)  \
        case opcode:

    #define DISPATCH(pc)     \
        break;

#endif

// zeng: 解释执行 指令
u4 *executeJava() {
    // zeng: 线程执行上下文
    ExecEnv *ee = getExecEnv();
    // zeng: 当前方法栈帧
    Frame *frame = ee->last_frame;
    // zeng: 取得栈帧对应MethodBlock
    MethodBlock *mb = frame->mb;
    // zeng: 栈帧中的本地向量数组
    u4 *lvars = frame->lvars;
    // zeng: 栈帧中的操作数栈
    u4 *ostack = frame->ostack;
    // zeng: 方法指令地址
    volatile unsigned char *pc = mb->code;
    // zeng: 方法所在类constant_pool
    ConstantPool *cp = &(CLASS_CB(mb->class)->constant_pool);

    // zeng: 取得方法所在对象  为何没有判断static? 因为static下面使用this时会判断? 是
    Object *this = (Object *) lvars[0];

    Class *new_class;
    MethodBlock *new_mb;
    u4 *arg1;
    u8 *neoU8;
    u8 *neoU82;
    float *neoFloat;
    double *neoDouble;


#ifdef THREADED // zeng: 如果是串联式 则建立一个 字节码 对应的 c代码(准确说是编译后的机器指令) 地址 的跳转表
    static void *handlers[] = {
        &&opc0, &&opc1, &&opc2, &&opc3, &&opc4, &&opc5, &&opc6, &&opc7, &&opc8, &&opc9, &&opc10,
        &&opc11, &&opc12, &&opc13, &&opc14, &&opc15, &&opc16, &&opc17, &&opc18, &&opc19, &&opc20,
        &&opc21, &&opc22, &&opc23, &&opc24, &&opc25, &&opc26, &&opc27, &&opc28, &&opc29, &&opc30,
        &&opc31, &&opc32, &&opc33, &&opc34, &&opc35, &&opc36, &&opc37, &&opc38, &&opc39, &&opc40,
        &&opc41, &&opc42, &&opc43, &&opc44, &&opc45, &&opc46, &&opc47, &&opc48, &&opc49, &&opc50,
        &&opc51, &&opc52, &&opc53, &&opc54, &&opc55, &&opc56, &&opc57, &&opc58, &&opc59, &&opc60,
        &&opc61, &&opc62, &&opc63, &&opc64, &&opc65, &&opc66, &&opc67, &&opc68, &&opc69, &&opc70,
        &&opc71, &&opc72, &&opc73, &&opc74, &&opc75, &&opc76, &&opc77, &&opc78, &&opc79, &&opc80,
        &&opc81, &&opc82, &&opc83, &&opc84, &&opc85, &&opc86, &&opc87, &&opc88, &&opc89, &&opc90,
        &&opc91, &&opc92, &&opc93, &&opc94, &&opc95, &&opc96, &&opc97, &&opc98, &&opc99, &&opc100,
        &&opc101, &&opc102, &&opc103, &&opc104, &&opc105, &&opc106, &&opc107, &&opc108, &&opc109,
        &&opc110, &&opc111, &&opc112, &&opc113, &&opc114, &&opc115, &&opc116, &&opc117, &&opc118,
        &&opc119, &&opc120, &&opc121, &&opc122, &&opc123, &&opc124, &&opc125, &&opc126, &&opc127,
        &&opc128, &&opc129, &&opc130, &&opc131, &&opc132, &&opc133, &&opc134, &&opc135, &&opc136,
        &&opc137, &&opc138, &&opc139, &&opc140, &&opc141, &&opc142, &&opc143, &&opc144, &&opc145,
        &&opc146, &&opc147, &&opc148, &&opc149, &&opc150, &&opc151, &&opc152, &&opc153, &&opc154,
        &&opc155, &&opc156, &&opc157, &&opc158, &&opc159, &&opc160, &&opc161, &&opc162, &&opc163,
        &&opc164, &&opc165, &&opc166, &&opc167, &&opc168, &&opc169, &&opc170, &&opc171, &&opc172,
        &&opc173, &&opc174, &&opc175, &&opc176, &&opc177, &&opc178, &&opc179, &&opc180, &&opc181,
        &&opc182, &&opc183, &&opc184, &&opc185, &&unused, &&opc187, &&opc188, &&opc189, &&opc190,
        &&opc191, &&opc192, &&opc193, &&opc194, &&opc195, &&opc196, &&opc197, &&opc198, &&opc199,
        &&opc200, &&opc201, &&unused, &&opc203, &&opc204, &&unused, &&opc206, &&opc207, &&opc208,
        &&opc209, &&opc210, &&opc211, &&opc212, &&opc213, &&opc214, &&opc215, &&opc216, &&unused,
        &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&opc226,
        &&opc227, &&opc228, &&opc229, &&opc230, &&opc231, &&opc232, &&unused, &&unused, &&unused,
        &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused,
        &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused, &&unused,
        &&unused, &&unused
    };

    // zeng: 从方法指令开始地址执行
    DISPATCH(pc)

#else
    // zeng: while switch从方法指令开始地址 处开始解释执行
    while (TRUE) {
        switch (*pc) {
            default:
#endif

            // zeng: 可以看到这里操作数栈ostack是当数组在用的 入栈地址从低到高

            unused:
                printf("Unrecognised opcode %d in: %s.%s\n", *pc, CLASS_CB(mb->class)->name, mb->name);
                exit(0);

            DEF_OPC(OPC_NOP)    // zeng: 什么都不做,直接跳转到下一个操作码
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ACONST_NULL)    // zeng: 0 入操作数栈
                *ostack++ = 0;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_M1)  // zeng: int -1入操作数栈
                *ostack++ = -1;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_0)   // zeng: int 0 入操作数栈
            DEF_OPC(OPC_FCONST_0)   // zeng: float 0 入操作数栈
                *ostack++ = 0;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_1)   //  zeng: int 1 入操作数栈
                *ostack++ = 1;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_2)
                *ostack++ = 2;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_3)
                *ostack++ = 3;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_4)
                *ostack++ = 4;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ICONST_5)
                *ostack++ = 5;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LCONST_0)   // zeng: long 0 入操作数栈
            DEF_OPC(OPC_DCONST_0)   // zeng: double 0 入操作数栈
                neoU8 = (u8 *) ostack;  // zeng: 占两个格子
                *neoU8 = 0;
                neoU8++;
                ostack = (u4 *) neoU8;

                // *((u8*)ostack)++ = 0;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_FCONST_1)   // zeng: float 1入栈
                //        *((float*)ostack)++ = (float) 1.0;
                neoFloat = (float *) ostack;
                *neoFloat = 1.0;
                neoFloat++;
                ostack = (u4 *) neoFloat;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_FCONST_2)
                //*((float*)ostack)++ = (float) 2.0;
                neoFloat = (float *) ostack;
                *neoFloat = 2.0;
                neoFloat++;
                ostack = (u4 *) neoFloat;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_DCONST_1)   // zeng: double 1入栈
                //        *((double*)ostack)++ = (double) 1.0;
                neoDouble = (double *) ostack;
                *neoDouble = (double) 1.0;
                neoDouble++;
                ostack = (u4 *) neoDouble;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LCONST_1)   // zeng: long 1入栈
                //        *((u8*)ostack)++ = 1;
                neoU8 = (u8 *) ostack;
                *neoU8 = 1;
                neoU8++;
                ostack = neoU8;
                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_SIPUSH) // zeng: 将一个signed short int 入栈
                *ostack++ = (signed short) ((pc[1] << 8) + pc[2]);  // zeng: 从code中读取signed short int, 入栈

                pc += 3;    // zeng: 操作码1个字节 signed short int 2个字节  共3个字节
                DISPATCH(pc)

            DEF_OPC(OPC_BIPUSH)
                *ostack++ = (signed char) pc[1];    // zeng: 取pc接下来的1个字节 写入操作数栈中

                pc += 2;    // zeng: 本条指令(操作码 + 操作数)共2个字节
                DISPATCH(pc)

            DEF_OPC(OPC_LDC) // zeng: 从constant_pool中取u4型数(int、float或String型常量值), 入栈
                *ostack++ = resolveSingleConstant(mb->class, CP_SINDEX(pc)); // zeng: code中操作数是constant_pool中的index 这里的index只有1个字节大小
                OPCODE_REWRITE(pc, OPC_LDC_QUICK);  // zeng: 更改code中的操作码,省去解析步骤

                pc += 2;
                DISPATCH(pc)

            DEF_OPC(OPC_LDC_QUICK)  // zeng: 从constant_pool中取u4型数, 入栈
                *ostack++ = CP_INFO(cp, CP_SINDEX(pc)); // 直接从constant_pool中取info

                pc += 2;
                DISPATCH(pc)

            DEF_OPC(OPC_LDC_W)  // zeng: 从constant_pool中取u4型数, 入栈
                *ostack++ = resolveSingleConstant(mb->class, CP_DINDEX(pc));    // zeng: index有2个字节大小
                OPCODE_REWRITE(pc, OPC_LDC_W_QUICK);

                pc += 3;
                DISPATCH(pc)

            DEF_OPC(OPC_LDC_W_QUICK)    // zeng: 从constant_pool中取u4型数, 入栈
                *ostack++ = CP_INFO(cp, CP_DINDEX(pc));
                pc += 3;
                DISPATCH(pc)

            DEF_OPC(OPC_LDC2_W)  // zeng: 从constant_pool中取u8型(long或double型常量值)数, 入栈
                //        *((u8*)ostack)++ = CP_LONG(cp, CP_DINDEX(pc));
                neoU8 = (u8 *) ostack;
                *neoU8 = CP_LONG(cp, CP_DINDEX(pc));
                neoU8++;
                ostack = (u4 *) neoU8;

                pc += 3;
                DISPATCH(pc)

            DEF_OPC(OPC_ILOAD)
            DEF_OPC(OPC_FLOAD)
            DEF_OPC(OPC_ALOAD)
                *ostack++ = lvars[CP_SINDEX(pc)];   // zeng: 字节中读取index,根据index从局部变量数组中取值, 入栈

                pc += 2;
                DISPATCH(pc)OPC_DSTORE

            DEF_OPC(OPC_LLOAD)
            DEF_OPC(OPC_DLOAD)
                *((u8*)ostack)++ = *(u8*)(&lvars[CP_SINDEX(pc)]);    // zeng: long double占局部变量数组两个格子

                pc += 2;
                DISPATCH(pc)

            DEF_OPC(OPC_ALOAD_0)    // zeng: 取本地变量数组中index为0的变量的值 该值是对象地址
                if (mb->access_flags & ACC_STATIC)  // zeng: static方法
                    OPCODE_REWRITE(pc, OPC_ILOAD_0);    // zeng: 更改code中的操作码
                else    // zeng: 实例方法 实例对象地址作为第一个参数保存到本地变量数组中 所以就是要加载this地址进操作数栈
                    OPCODE_REWRITE(pc, OPC_ALOAD_THIS); // zeng: 更改code中的操作码

                DISPATCH(pc)    // zeng; 解释刚更改的操作码

            DEF_OPC(OPC_ALOAD_THIS) // zeng: 如果加载this进操作数栈是为了取字段 那么 合并 成快捷操作
                if (pc[1] == OPC_GETFIELD_QUICK) {  // zeng: 如果下一个操作码是获取this下的字段 那么我们 将几个操作码的操作 合并成一个快捷操作 用 OPC_GETFIELD_THIS 操作码表示
                    OPCODE_REWRITE(pc, OPC_GETFIELD_THIS);

                    DISPATCH(pc)
                }
                // zeng: 这里没有dispatch, 继续往下执行, 相当于解释执行  OPC_ILOAD_0 有点丑陋

            DEF_OPC(OPC_ILOAD_0)
            DEF_OPC(OPC_FLOAD_0)
                *ostack++ = lvars[0];   // zeng: 取本地变量表index为0的变量 入栈

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ILOAD_1)
            DEF_OPC(OPC_FLOAD_1)
            DEF_OPC(OPC_ALOAD_1)
                *ostack++ = lvars[1];   // zeng: 取本地变量表index为1的变量 入栈

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ILOAD_2)
            DEF_OPC(OPC_FLOAD_2)
            DEF_OPC(OPC_ALOAD_2)
                *ostack++ = lvars[2];    // zeng: 取本地变量表index为2的变量 入栈

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ILOAD_3)
            DEF_OPC(OPC_FLOAD_3)
            DEF_OPC(OPC_ALOAD_3)
                *ostack++ = lvars[3];    // zeng: 取本地变量表index为3的变量 入栈

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LLOAD_0)
            DEF_OPC(OPC_DLOAD_0)
                //	*((u8*)ostack)++ = *(u8*)(&lvars[0]);
                neoU8 = (u8 *) ostack;
                *neoU8 = *(u8 *) (&lvars[0]);   // zeng: 取本地变量表index为0的变量(long double,连取两个格子) 入栈
                neoU8++;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LLOAD_1)
            DEF_OPC(OPC_DLOAD_1)
                //	*((u8*)ostack)++ = *(u8*)(&lvars[1]);
                neoU8 = ostack;
                *neoU8 = *(u8 *) (&lvars[1]);   // zeng: 取本地变量表index为1的变量(long double,连取两个格子) 入栈
                neoU8++;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LLOAD_2)
            DEF_OPC(OPC_DLOAD_2)
                //	*((u8*)ostack)++ = *(u8*)(&lvars[2]);
                neoU8 = ostack;
                *neoU8 = *(u8 *) (&lvars[2]);   // zeng: 取本地变量表index为2的变量(long double,连取两个格子) 入栈
                neoU8++;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LLOAD_3)
            DEF_OPC(OPC_DLOAD_3)
                //	*((u8*)ostack)++ = *(u8*)(&lvars[3]);
                neoU8 = ostack;
                *neoU8 = *(u8 *) (&lvars[3]);   // zeng: 取本地变量表index为3的变量(long double,连取两个格子) 入栈
                neoU8++;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_IALOAD)
            DEF_OPC(OPC_AALOAD)
            DEF_OPC(OPC_FALOAD) ARRAY_LOAD(int, ostack, pc);    // 	zeng: 指定的u4型元素数组的指定下标处的值进栈

            DEF_OPC(OPC_LALOAD) ARRAY_LOAD_LONG(long long, ostack, pc); // 	zeng: 指定的u8型元素数组的指定下标处的值进栈

            DEF_OPC(OPC_DALOAD) ARRAY_LOAD_LONG(long long, ostack, pc); // 	zeng: 指定的u8型元素数组的指定下标处的值进栈

            DEF_OPC(OPC_BALOAD) ARRAY_LOAD(signed char, ostack, pc);    // 	zeng: 指定的u1型元素数组的指定下标处的值进栈

            DEF_OPC(OPC_CALOAD)
            DEF_OPC(OPC_SALOAD) ARRAY_LOAD(short, ostack, pc);  // // 	zeng: 指定的u2型元素数组的指定下标处的值进栈

            DEF_OPC(OPC_LSTORE)
            DEF_OPC(OPC_DSTORE)
                // zeng: 出栈, 值写入本地变量数组中(从code字节中读取的index)

                *(u8*)(&lvars[CP_SINDEX(pc)]) = *--((u8*)ostack);

                pc += 2;
                DISPATCH(pc)

            DEF_OPC(OPC_ISTORE)
            DEF_OPC(OPC_FSTORE)
            DEF_OPC(OPC_ASTORE)
                // zeng: 出栈, 值写入本地变量数组中(从code字节中读取的index)
                lvars[CP_SINDEX(pc)] = *--ostack;

                pc += 2;
                DISPATCH(pc)

            DEF_OPC(OPC_ISTORE_0)
            DEF_OPC(OPC_ASTORE_0)
            DEF_OPC(OPC_FSTORE_0)
                // zeng: 出栈, 值写入本地变量数组中(index为0)
                lvars[0] = *--ostack;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ISTORE_1)
            DEF_OPC(OPC_ASTORE_1)
            DEF_OPC(OPC_FSTORE_1)
                // zeng: 出栈, 值写入本地变量数组中(index为1)
                lvars[1] = *--ostack;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ISTORE_2)
            DEF_OPC(OPC_ASTORE_2)
            DEF_OPC(OPC_FSTORE_2)
                // zeng: 出栈, 值写入本地变量数组中(index为2)
                lvars[2] = *--ostack;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_ISTORE_3)
            DEF_OPC(OPC_ASTORE_3)
            DEF_OPC(OPC_FSTORE_3)
                // zeng: 出栈, 值写入本地变量数组中(index为3)
                lvars[3] = *--ostack;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LSTORE_0)
            DEF_OPC(OPC_DSTORE_0)
                // zeng: 出栈, 值写入本地变量数组中(index为0)

                //        *(u8*)(&lvars[0]) = *--((u8*)ostack);
                neoU8 = ostack;
                neoU8--;
                *(u8 *) (&lvars[0]) = *neoU8;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LSTORE_1)
            DEF_OPC(OPC_DSTORE_1)
                // zeng: 出栈, 值写入本地变量数组中(index为1)

                // *(u8*)(&lvars[1]) = *--((u8*)ostack);
                neoU8 = ostack;
                neoU8--;
                *(u8 *) (&lvars[1]) = *neoU8;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LSTORE_2)
            DEF_OPC(OPC_DSTORE_2)
                // zeng: 出栈, 值写入本地变量数组中(index为2)
                // *(u8*)(&lvars[2]) = *--((u8*)ostack);
                neoU8 = ostack;
                neoU8--;
                *(u8 *) (&lvars[2]) = *neoU8;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_LSTORE_3)
            DEF_OPC(OPC_DSTORE_3)
                // zeng: 出栈, 值写入本地变量数组中(index为3)
                //        *(u8*)(&lvars[3]) = *--((u8*)ostack);
                neoU8 = ostack;
                neoU8--;
                *(u8 *) (&lvars[3]) = *neoU8;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_IASTORE)
            DEF_OPC(OPC_AASTORE)
            DEF_OPC(OPC_FASTORE) ARRAY_STORE(int, ostack, pc);  // 	zeng: 出栈, 值存入指定的u4型元素数组的指定下标处

            DEF_OPC(OPC_LASTORE)
            DEF_OPC(OPC_DASTORE) ARRAY_STORE_LONG(double, ostack, pc);  // 	zeng: 出栈, 值存入指定的u8型元素数组的指定下标处

            DEF_OPC(OPC_BASTORE) ARRAY_STORE(char, ostack, pc); // 	zeng: 出栈, 值存入指定的u1型元素数组的指定下标处

            DEF_OPC(OPC_CASTORE)
            DEF_OPC(OPC_SASTORE) ARRAY_STORE(short, ostack, pc);    // 	zeng: 出栈, 值存入指定的u2型元素数组的指定下标处

            DEF_OPC(OPC_POP)
                ostack--;   // zeng: 出栈

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_POP2)
                ostack -= 2;    // zeng: 两个格子出栈

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_DUP) {
                // zeng: 复制栈顶的u4值,将该值入栈

                u4 word1 = ostack[-1];
                *ostack++ = word1;
                // *ostack++ = ostack[-1];

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_DUP_X1) {
                // zenq: 将栈顶u4值 插入 栈顶u8值 之前

                u4 word1 = ostack[-1];
                u4 word2 = ostack[-2];
                ostack[-2] = word1;
                ostack[-1] = word2;

                *ostack++ = word1;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_DUP_X2) {
                // zenq: 将栈顶u4值 插入 栈顶u12值 之前

                u4 word1 = ostack[-1];
                u4 word2 = ostack[-2];
                u4 word3 = ostack[-3];
                ostack[-3] = word1;
                ostack[-2] = word3;
                ostack[-1] = word2;

                *ostack++ = word1;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_DUP2)
                // zeng: 复制栈顶的u8值,将该值入栈

                //    *((u8*)ostack)++ = ((u8*)ostack)[-1];
                neoU8 = ostack;
                *neoU8 = ((u8 *) ostack)[-1];
                neoU8++;
                ostack = neoU8;

                pc += 1;
                DISPATCH(pc)

            DEF_OPC(OPC_DUP2_X1) {
                // zenq: 将栈顶u8值 插入 栈顶u12值 之前
                u4 word1 = ostack[-1];
                u4 word2 = ostack[-2];
                u4 word3 = ostack[-3];
                ostack[-3] = word2;
                ostack[-2] = word1;
                ostack[-1] = word3;

                ostack[0] = word2;
                ostack[1] = word1;
                ostack += 2;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_DUP2_X2) {
                // zenq: 将栈顶u8值 插入 栈顶u16值 之前

                u4 word1 = ostack[-1];
                u4 word2 = ostack[-2];
                u4 word3 = ostack[-3];
                u4 word4 = ostack[-4];
                ostack[-4] = word2;
                ostack[-3] = word1;
                ostack[-2] = word4;
                ostack[-1] = word3;

                ostack[0] = word2;
                ostack[1] = word1;
                ostack += 2;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_SWAP) {
                // zeng: 栈顶两个u4值对换
                u4 word1 = ostack[-1];
                ostack[-1] = ostack[-2];
                ostack[-2] = word1;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_IADD)   // zeng: 加
            BINARY_OP(int, +, ostack, pc);

            DEF_OPC(OPC_LADD)
            BINARY_OP(long long, +, ostack, pc);

            DEF_OPC(OPC_FADD)
            BINARY_OP(float, +, ostack, pc);

            DEF_OPC(OPC_DADD)
            BINARY_OP(double, +, ostack, pc);

            DEF_OPC(OPC_ISUB)   // zeng: 减
            BINARY_OP(int, -, ostack, pc);

            DEF_OPC(OPC_LSUB)
            BINARY_OP(long long, -, ostack, pc);

            DEF_OPC(OPC_FSUB)
            BINARY_OP(float, -, ostack, pc);

            DEF_OPC(OPC_DSUB)
            BINARY_OP(double, -, ostack, pc);

            DEF_OPC(OPC_IMUL)   // zeng: 乘
            BINARY_OP(int, *, ostack, pc);

            DEF_OPC(OPC_LMUL)
            BINARY_OP(long long, *, ostack, pc);

            DEF_OPC(OPC_FMUL)
            BINARY_OP(float, *, ostack, pc);

            DEF_OPC(OPC_DMUL)
            BINARY_OP(double, *, ostack, pc);

            DEF_OPC(OPC_IDIV)   // zeng: 除
                ZERO_DIVISOR_CHECK(int, ostack);
                BINARY_OP(int, /, ostack, pc);

            DEF_OPC(OPC_LDIV)
                ZERO_DIVISOR_CHECK(long long, ostack);
                BINARY_OP(long long, /, ostack, pc);

            DEF_OPC(OPC_FDIV)
            BINARY_OP(float, /, ostack, pc);

            DEF_OPC(OPC_DDIV)
            BINARY_OP(double, /, ostack, pc);

            DEF_OPC(OPC_IREM)   // zeng: 取余
                ZERO_DIVISOR_CHECK(int, ostack);
                BINARY_OP(int, %, ostack, pc);

            DEF_OPC(OPC_LREM)
                ZERO_DIVISOR_CHECK(long long, ostack);
                BINARY_OP(long long, %, ostack, pc);

            DEF_OPC(OPC_FREM) { // zeng: 两个float操作数做取余操作
                //        float v2 = *--((float *)ostack);
                // float v1 = *--((float *)ostack);
                //      *((float *)ostack)++ = fmod(v1, v2);

                neoFloat = ostack;

                // zeng: 除数
                neoFloat--;
                float v2 = *neoFloat;

                // zeng: 被除数
                neoFloat--;
                float v1 = *neoFloat;

                // zeng: 调用math.h中的fmod函数
                *neoFloat = fmod(v1, v2);

                neoFloat++;
                ostack = neoFloat;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_DREM) { // zeng: 两个double操作数做取余操作
                /* double v2 = *--((double *)ostack); */
                /* double v1 = *--((double *)ostack); */

                /* *((double *)ostack)++ = fmod(v1, v2); */

                neoDouble = ostack;

                neoDouble--;
                double v2 = *neoDouble;

                neoDouble--;
                double v1 = *neoDouble;

                *neoDouble = fmod(v1, v2);

                neoDouble++;
                ostack = neoDouble;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_INEG)   // zeng: 取负
            UNARY_MINUS(int, ostack, pc);

            DEF_OPC(OPC_LNEG)
            UNARY_MINUS(long long, ostack, pc);

            DEF_OPC(OPC_FNEG)
            UNARY_MINUS(float, ostack, pc);

            DEF_OPC(OPC_DNEG)
            UNARY_MINUS(double, ostack, pc);

            DEF_OPC(OPC_ISHL)   // zeng: 位运算 左移
            BINARY_OP(int, <<, ostack, pc);

            DEF_OPC(OPC_LSHL) SHIFT_OP(long long, <<, ostack, pc);

            DEF_OPC(OPC_ISHR)   // zeng: 位运算 右移
            BINARY_OP(int, >>, ostack, pc);

            DEF_OPC(OPC_LSHR) SHIFT_OP(long long, >>, ostack, pc);

            DEF_OPC(OPC_IUSHR) SHIFT_OP(unsigned int, >>, ostack, pc);

            DEF_OPC(OPC_LUSHR) SHIFT_OP(unsigned long long, >>, ostack, pc);

            DEF_OPC(OPC_IAND)   // zeng: 位运算 与
            BINARY_OP(int, &, ostack, pc);

            DEF_OPC(OPC_LAND)
            BINARY_OP(long long, &, ostack, pc);

            DEF_OPC(OPC_IOR)    // zeng: 位运算 或
            BINARY_OP(int, |, ostack, pc);

            DEF_OPC(OPC_LOR)
            BINARY_OP(long long, |, ostack, pc);

            DEF_OPC(OPC_IXOR)   // zeng: 位运算 异或
            BINARY_OP(int, ^, ostack, pc);

            DEF_OPC(OPC_LXOR)
            BINARY_OP(long long, ^, ostack, pc);

            DEF_OPC(OPC_IINC)   // zeng: 本地变量表index下元素(code中读取) 加上 一个signed char的值(code中读取)
                lvars[CP_SINDEX(pc)] += (signed char) pc[2];

                pc += 3;
                DISPATCH(pc)

            DEF_OPC(OPC_I2L) OPC_X2Y(int, long long);   // zeng: int 转为 long long

            DEF_OPC(OPC_I2F) OPC_X2Y(int, float);

            DEF_OPC(OPC_I2D) OPC_X2Y(int, double);

            DEF_OPC(OPC_L2I) OPC_X2Y(long long, int);

            DEF_OPC(OPC_L2F) OPC_X2Y(long long, float);

            DEF_OPC(OPC_L2D) OPC_X2Y(long long, double);

            DEF_OPC(OPC_F2I) OPC_X2Y(float, int);

            DEF_OPC(OPC_F2L) OPC_X2Y(float, long long);

            DEF_OPC(OPC_F2D) OPC_X2Y(float, double);

            DEF_OPC(OPC_D2I) OPC_X2Y(double, int);

            DEF_OPC(OPC_D2L) OPC_X2Y(double, long long);

            DEF_OPC(OPC_D2F) OPC_X2Y(double, float);

            DEF_OPC(OPC_I2B) {  // zeng: int 强转 byte
                signed char v = ostack[-1] & 0xff; // zeng: 保留最低一个字节的位
                ostack[-1] = (int) v;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_I2C) {
                int v = ostack[-1] & 0xffff;
                ostack[-1] = v;

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_I2S) {
                signed short v = ostack[-1] & 0xffff;
                ostack[-1] = (int) v;
                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_LCMP) CMP(long long, ostack, pc);   // zeng: 比较long值大小

            DEF_OPC(OPC_DCMPG)
            DEF_OPC(OPC_DCMPL) FCMP(double, ostack, pc, (*pc == OPC_DCMPG ? 1 : -1));

            DEF_OPC(OPC_FCMPG)
            DEF_OPC(OPC_FCMPL) FCMP(float, ostack, pc, (*pc == OPC_FCMPG ? 1 : -1));

            DEF_OPC(OPC_IFEQ) IF(==, ostack, pc);   // zeng: if ==

            DEF_OPC(OPC_IFNE) IF(!=, ostack, pc);

            DEF_OPC(OPC_IFLT) IF(<, ostack, pc);

            DEF_OPC(OPC_IFGE) IF(>=, ostack, pc);

            DEF_OPC(OPC_IFGT) IF(>, ostack, pc);

            DEF_OPC(OPC_IFLE) IF(<=, ostack, pc);

            DEF_OPC(OPC_IF_ACMPEQ)
            DEF_OPC(OPC_IF_ICMPEQ) IF_ICMP(==, ostack, pc); // zeng: if ==

            DEF_OPC(OPC_IF_ACMPNE)
            DEF_OPC(OPC_IF_ICMPNE) IF_ICMP(!=, ostack, pc);

            DEF_OPC(OPC_IF_ICMPLT) IF_ICMP(<, ostack, pc);

            DEF_OPC(OPC_IF_ICMPGE) IF_ICMP(>=, ostack, pc);

            DEF_OPC(OPC_IF_ICMPGT) IF_ICMP(>, ostack, pc);

            DEF_OPC(OPC_IF_ICMPLE) IF_ICMP(<=, ostack, pc);

            DEF_OPC(OPC_GOTO)   // zeng: 从code中读取跳转偏移量, 跳转
                pc += BRANCH(pc);
                DISPATCH(pc)

            DEF_OPC(OPC_JSR)
                *ostack++ = (u4) pc + 3;    // zeng: 下一个指令地址入栈

                // zeng: 从code中读取跳转偏移量, 跳转
                pc += BRANCH(pc);
                DISPATCH(pc)

            DEF_OPC(OPC_RET)
                pc = (unsigned char *) lvars[CP_SINDEX(pc)];    // zeng: 下一个字节中读取本地变量数组中的index, 访问index下的值, 将该值作为指令地址跳转
                DISPATCH(pc)

            DEF_OPC(OPC_TABLESWITCH) {  // zeng: TODO 暂不感兴趣
                // zeng: 跳过用于对齐的字节
                int *aligned_pc = (int *) ((int) (pc + 4) & ~0x3);

                int deflt = ntohl(aligned_pc[0]);
                int low = ntohl(aligned_pc[1]);
                int high = ntohl(aligned_pc[2]);
                int index = *--ostack;

                if (index < low || index > high)
                    pc += deflt;
                else
                    pc += ntohl(aligned_pc[index - low + 3]);

                DISPATCH(pc)
            }

            DEF_OPC(OPC_LOOKUPSWITCH) { // zeng: TODO 暂不感兴趣
                int *aligned_pc = (int *) ((int) (pc + 4) & ~0x3);
                int deflt = ntohl(aligned_pc[0]);
                int npairs = ntohl(aligned_pc[1]);
                int key = *--ostack;
                int i;

                for (i = 2; (i < npairs * 2 + 2) && (key != ntohl(aligned_pc[i])); i += 2);

                if (i == npairs * 2 + 2)
                    pc += deflt;
                else
                    pc += ntohl(aligned_pc[i + 1]);

                DISPATCH(pc)
            }

            DEF_OPC(OPC_IRETURN)    // zeng: 返回int值
            DEF_OPC(OPC_ARETURN)    // zeng: 返回对象地址
            DEF_OPC(OPC_FRETURN)
                *lvars++ = *--ostack;   // zeng: 出栈, 写入本地变量数组index为0处
                goto methodReturn;  // zeng: 返回到调用本方法的方法

            DEF_OPC(OPC_LRETURN)
            DEF_OPC(OPC_DRETURN)
                *((u8*)lvars)++ = *(--(u8*)ostack); // zeng: 出栈u8值, 写入本地变量数组index为0,1处
                goto methodReturn;  // zeng: 返回到调用本方法的方法

            DEF_OPC(OPC_RETURN) // zeng: 返回void
                goto methodReturn;  // zeng: 返回到调用本方法的方法

            DEF_OPC(OPC_GETSTATIC) {    // zeng: 获取类变量
                FieldBlock *fb;

                // zeng: 栈帧中记录当前pc 在异常处理时有用 所以有可能抛出错误的操作码逻辑 都要记录当前pc
                frame->last_pc = (unsigned char *) pc;

                // zeng: 传入方法所在类class对象(用来获取classloader) 以及从code中两个字节对应的constant_pool中的index 返回FieldBlock地址
                fb = resolveField(mb->class, CP_DINDEX(pc));

                if (exceptionOccured0(ee))
                    goto throwException;

                // zeng: 替换操作码 下次就不用解析了
                if ((*fb->type == 'J') || (*fb->type == 'D'))   // zeng: Long Double
                    OPCODE_REWRITE(pc, OPC_GETSTATIC2_QUICK);
                else
                    OPCODE_REWRITE(pc, OPC_GETSTATIC_QUICK);

                DISPATCH(pc)    // zeng: 转发到刚替换的操作码
            }

            DEF_OPC(OPC_PUTSTATIC) {    // zeng: 设置类变量
                FieldBlock *fb;

                frame->last_pc = (unsigned char *) pc;

                // zeng: 取得FieldBlock地址
                fb = resolveField(mb->class, CP_DINDEX(pc));

                if (exceptionOccured0(ee))
                    goto throwException;

                // zeng: 替换操作码 下次就不用解析了
                if ((*fb->type == 'J') || (*fb->type == 'D'))
                    OPCODE_REWRITE(pc, OPC_PUTSTATIC2_QUICK);
                else
                    OPCODE_REWRITE(pc, OPC_PUTSTATIC_QUICK);

                DISPATCH(pc)
            }

            DEF_OPC(OPC_GETSTATIC_QUICK) {  // zeng: 获取类变量
                FieldBlock *fb = (FieldBlock *) CP_INFO(cp, CP_DINDEX(pc)); // zeng: 从constant_pool中index(Code中读取两个字节即index)下取得FieldBlock地址
                *ostack++ = fb->static_value;   // zeng: FieldBlock -> static_value 入栈

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_GETSTATIC2_QUICK) {
                FieldBlock *fb = (FieldBlock *) CP_INFO(cp, CP_DINDEX(pc));
                *(u8 *) ostack = *(u8 *) &fb->static_value;
                ostack += 2;

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_PUTSTATIC_QUICK) {  // zeng: 设置类变量
                FieldBlock *fb = (FieldBlock *) CP_INFO(cp, CP_DINDEX(pc)); // zeng: 从constant_pool中index(Code中读取两个字节即index)下取得FieldBlock地址
                fb->static_value = *--ostack;   // zeng: 出栈, 值赋给 FieldBlock -> static_value

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_PUTSTATIC2_QUICK) {
                FieldBlock *fb = (FieldBlock *) CP_INFO(cp, CP_DINDEX(pc));
                ostack -= 2;
                *(u8 *) &fb->static_value = *(u8 *) ostack;
                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_GETFIELD) { // zeng: 获取实例变量
                int idx;
                FieldBlock *fb;

                // zeng: 从code中两个字节获取的constant_pool下的index
                WITH_OPCODE_CHANGE_CP_DINDEX(pc, OPC_GETFIELD, idx);

                frame->last_pc = (unsigned char *) pc;

                // zeng: 获取FieldBlock地址
                fb = resolveField(mb->class, idx);

                if (exceptionOccured0(ee))
                    goto throwException;

                // zeng: 替换操作码 以便下次跳过解析环节
                if (fb->offset > 255)
                    OPCODE_REWRITE(pc, OPC_GETFIELD_QUICK_W);
                else    // zeng: 如果offset可以用1个字节表示 那么就直接用offset 替换 Code中表示FieldBlock地址的字节(这里地址有两个字节 为什么有限制offset为一个字节时才走这个分支?)
                    OPCODE_REWRITE_OPERAND1(pc, ((*fb->type == 'J') || (*fb->type == 'D') ? OPC_GETFIELD2_QUICK : OPC_GETFIELD_QUICK), fb->offset);

                // zeng: 解释执行替换的操作码
                DISPATCH(pc)
            }

            DEF_OPC(OPC_PUTFIELD) { // zeng: 设置实例变量
                int idx;
                FieldBlock *fb;

                // zeng: 从code中两个字节获取的constant_pool下的index
                WITH_OPCODE_CHANGE_CP_DINDEX(pc, OPC_PUTFIELD, idx);

                frame->last_pc = (unsigned char *) pc;

                // zeng: 获取FieldBlock地址
                fb = resolveField(mb->class, idx);

                if (exceptionOccured0(ee))
                    goto throwException;

                // zeng: 替换操作码 以便下次跳过解析环节
                if (fb->offset > 255)
                    OPCODE_REWRITE(pc, OPC_PUTFIELD_QUICK_W);
                else
                    OPCODE_REWRITE_OPERAND1(pc, ((*fb->type == 'J') || (*fb->type == 'D') ? OPC_PUTFIELD2_QUICK : OPC_PUTFIELD_QUICK), fb->offset);

                DISPATCH(pc)
            }

            DEF_OPC(OPC_GETFIELD_QUICK) {
                Object *o = (Object *) ostack[-1];  // zeng: 取对象地址
                NULL_POINTER_CHECK(o);

                ostack[-1] = INST_DATA(o)[pc[1]];   // zeng: 将 栈顶 替换为 对象内容体中 offset下的值(上面将pc[1]的字节设置为offset)

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_GETFIELD_THIS)  // zeng: OPC_ALOAD_0 + OPC_GETFIELD_QUICK 快捷操作
                *ostack++ = INST_DATA(this)[pc[2]]; // zeng: pc[2]为offset, this现成的, 从this对象内容体offset处取得字段值 入栈

                pc += 4;    // zeng: 加上 两条指令 的字节数
                DISPATCH(pc)

            DEF_OPC(OPC_GETFIELD2_QUICK) {
                Object *o = (Object *) *--ostack;   // zeng: 出栈 值为对象地址
                NULL_POINTER_CHECK(o);

                *((u8*)ostack)++ = *(u8*)(&(INST_DATA(o)[pc[1]]));  // zeng: 取对象内容体offset下的值, 入栈

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_GETFIELD_QUICK_W) {
                // zeng: 从code中两个字节获取的constant_pool下的index 通过index取得FieldBlock地址
                FieldBlock *fb = (FieldBlock *) CP_INFO(cp, CP_DINDEX(pc));

                // zeng: 出栈, 值为对象地址
                Object *o = (Object *) *--ostack;
                u4 *addr;

                NULL_POINTER_CHECK(o);

                // zeng: 对象内容体中该字段的地址
                addr = &(INST_DATA(o)[fb->offset]);

                // zeng: 取值, 入栈
                if ((*fb->type == 'J') || (*fb->type == 'D')) {
                    u8 v = *(u8 *) addr;

                    *(u8 *) ostack = v;
                    ostack += 2;
                } else {
                    u4 v = *addr;

                    *ostack++ = v;
                }

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_PUTFIELD_QUICK_W) {
                // zeng: 从Code的两个字节中获取index 通过index从constant_pool中取得FieldBlock地址
                FieldBlock *fb = (FieldBlock *) CP_INFO(cp, CP_DINDEX(pc));
                Object *o;

                if ((*fb->type == 'J') || (*fb->type == 'D')) {
                    u8 v, *addr;

                    // zeng: 出栈, 值为要赋给字段的值
                    ostack -= 2;
                    v = *(u8 *) ostack;

                    // zeng: 出栈, 值为对象地址
                    o = (Object *) *--ostack;
                    NULL_POINTER_CHECK(o);

                    // zeng: 对象内容体offset出地址
                    addr = (u8 *) &(INST_DATA(o)[fb->offset]);

                    // zeng: 写入
                    *addr = v;
                } else {
                    u4 *addr, v = *--ostack;

                    o = (Object *) *--ostack;

                    NULL_POINTER_CHECK(o);

                    addr = &(INST_DATA(o)[fb->offset]);

                    *addr = v;
                }

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_PUTFIELD_QUICK) {
                Object *o = (Object *) ostack[-2];  // zeng: 取得栈中的对象地址
                NULL_POINTER_CHECK(o);

                INST_DATA(o)[pc[1]] = ostack[-1];   // zeng: 取得栈顶的值, 写入对象内容体中offset处

                ostack -= 2;    // zeng: 更新栈顶位置

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_PUTFIELD2_QUICK) {
                Object *o = (Object *) ostack[-3];  // zeng: 取得栈中的对象地址
                NULL_POINTER_CHECK(o);

                *(u8 *) (&(INST_DATA(o)[pc[1]])) = *(u8 *) (&ostack[-2]);   // zeng: 取得栈顶u8型的值, 写入对象内容体中offset处

                ostack -= 3;    // zeng: 更新栈顶位置

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_INVOKEVIRTUAL) {    // zeng: 调用实例方法
                int idx;

                // zeng: Code两个字节 读取为index
                WITH_OPCODE_CHANGE_CP_DINDEX(pc, OPC_INVOKEVIRTUAL, idx);

                frame->last_pc = (unsigned char *) pc;

                // zeng: 传入方法所在类class对象(用来获取classloader) 以及从code中两个字节对应的constant_pool中的index 返回MethodBlock地址
                new_mb = resolveMethod(mb->class, idx);

                if (exceptionOccured0(ee))
                    goto throwException;

                if ((new_mb->args_count < 256) && (new_mb->method_table_index < 256)) { // zeng: 如果method_table_index和args_count都在一个字节数值范围内
                    // zeng: 直接用 method_table_index和args_count 替换 Code中表示FieldBlock地址的字节 替换操作码
                    OPCODE_REWRITE_OPERAND2(pc, OPC_INVOKEVIRTUAL_QUICK, new_mb->method_table_index,new_mb->args_count);
                } else
                    // zeng: 替换操作码
                    OPCODE_REWRITE(pc, OPC_INVOKEVIRTUAL_QUICK_W);

                DISPATCH(pc)
            }

            DEF_OPC(OPC_INVOKEVIRTUAL_QUICK_W)
                new_mb = (MethodBlock *) CP_INFO(cp, CP_DINDEX(pc));    // zeng: 从Code两个字节中取得MethodBlock地址在constant_pool中的index 进而取得MethodBlock地址
                arg1 = ostack - (new_mb->args_count);   // zeng: 第0个参数
                NULL_POINTER_CHECK(*arg1);

                new_class = (*(Object **) arg1)->class; // zeng: this对象对应的class对象
                new_mb = CLASS_CB(new_class)->method_table[new_mb->method_table_index]; // zeng: 根据index从class对象的method_table中获取MethodBlock地址

                goto invokeMethod;  // zeng: 跳转到方法调用逻辑

            DEF_OPC(OPC_INVOKESPECIAL) {    // zeng: 调用 超类构造方法、实例初始化方法、私有方法
                int idx;

                // zeng: Code中两个字节为 constant_pool index
                WITH_OPCODE_CHANGE_CP_DINDEX(pc, OPC_INVOKESPECIAL, idx);

                frame->last_pc = (unsigned char *) pc;

                // zeng: 获取MethodBlock地址
                new_mb = resolveMethod(mb->class, idx);

                if (exceptionOccured0(ee))
                    goto throwException;

                /* Check if invoking a super method... */
                if ((CLASS_CB(mb->class)->access_flags & ACC_SUPER) && ((new_mb->access_flags & ACC_PRIVATE) == 0) && (new_mb->name[0] != '<')) {   // zeng: 调用超类构造方法
                    // zeng: 将代表constant_pool index的两个字节直接替换为method_table_index  替换操作码
                    OPCODE_REWRITE_OPERAND2(pc, OPC_INVOKESUPER_QUICK,
                                            new_mb->method_table_index >> 8,
                                            new_mb->method_table_index & 0xff);
                } else
                    OPCODE_REWRITE(pc, OPC_INVOKENONVIRTUAL_QUICK); // zeng: 替换操作码

                DISPATCH(pc)    // zeng: 解释执行替换的操作码
            }

            DEF_OPC(OPC_INVOKESUPER_QUICK)
                new_mb = CLASS_CB(CLASS_CB(mb->class)->super)->method_table[CP_DINDEX(pc)]; // zeng: Code中两个字节为method_table_index 从 super -> method_table 中取得 MethodBlock地址
                arg1 = ostack - (new_mb->args_count);   // zeng: 定位到操作数栈中第0个参数

                NULL_POINTER_CHECK(*arg1);

                goto invokeMethod;

            DEF_OPC(OPC_INVOKENONVIRTUAL_QUICK)
                new_mb = (MethodBlock *) CP_INFO(cp, CP_DINDEX(pc));    // zeng: Code中两个字节为 MethodBlock 地址
                arg1 = ostack - (new_mb->args_count);   // zeng: 定位到操作数栈中第0个参数

                NULL_POINTER_CHECK(*arg1);
                goto invokeMethod;

            DEF_OPC(OPC_INVOKESTATIC)   // zeng: 调用static方法
                frame->last_pc = (unsigned char *) pc;

                new_mb = resolveMethod(mb->class, CP_DINDEX(pc));   // zeng: Code中两个字节取得constant_pool index, 进而取得MethodBlock地址

                if (exceptionOccured0(ee))
                    goto throwException;

                OPCODE_REWRITE(pc, OPC_INVOKESTATIC_QUICK); // zeng: 替换操作码 以便下次跳过解析过程

                DISPATCH(pc)    // zeng: 解释执行新操作码

            DEF_OPC(OPC_INVOKESTATIC_QUICK)
                new_mb = (MethodBlock *) CP_INFO(cp, CP_DINDEX(pc));    // zeng: Code中两个字节取得constant_pool index, 通过index直接取得MethodBlock地址

                arg1 = ostack - new_mb->args_count; // zeng: 定位操作数栈中第0个参数

                goto invokeMethod;

            DEF_OPC(OPC_INVOKEINTERFACE)    // zeng: 调用接口方法
                frame->last_pc = (unsigned char *) pc;

                new_mb = resolveInterfaceMethod(mb->class, CP_DINDEX(pc));  // zeng: 从code两个字节中读取constant_pool index, 进而获取MethodBlock地址

                if (exceptionOccured0(ee))
                    goto throwException;

                arg1 = ostack - (new_mb->args_count);
                NULL_POINTER_CHECK(*arg1);

                // zeng: 在this对应的class对象中查找 与接口方法 同方法名 同描述符 的 方法
                new_class = (*(Object **) arg1)->class;

                new_mb = lookupMethod(new_class, new_mb->name, new_mb->type);

                goto invokeMethod;

            DEF_OPC(OPC_ARRAYLENGTH) {  // zeng: 栈顶的数组引用出栈，该数组的长度进栈
                Object *array = (Object *) ostack[-1];  // zeng: 出栈, 值为数组地址
                NULL_POINTER_CHECK(array);

                ostack[-1] = *INST_DATA(array); // zeng: 数组内容体开头就是数组长度 进栈

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_ATHROW) {
                Object *ob = (Object *) ostack[-1]; // zeng: 出栈, 值为异常对象地址

                frame->last_pc = (unsigned char *) pc;
                NULL_POINTER_CHECK(ob);

                ee->exception = ob; // zeng: 设置运行上下文中的exception为该异常对象地址

                goto throwException;    // zeng: 跳转
            }

            DEF_OPC(OPC_NEW) {  // zeng: 创建一个对象,将对象地址入栈
                Class *class;
                Object *ob;

                frame->last_pc = (unsigned char *) pc;

                // zeng: 从code两个字节获取constant_pool index 进而获得class对象
                class = resolveClass(mb->class, CP_DINDEX(pc), TRUE);

                // zeng: 发生异常 跳转到异常处理
                if (exceptionOccured0(ee))
                    goto throwException;

                // zeng: 分配对象空间 返回对象地址
                if ((ob = allocObject(class)) == NULL)
                    goto throwException;

                *ostack++ = (u4) ob;    // zeng: 对象地址入栈

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_NEWARRAY) { // zeng: 创建一个基本类型数组，将地址入栈
                int type = pc[1];   // zeng: code下一个字节为基本类型
                int count = *--ostack;  // zeng: 出栈, 值为数组大小

                Object *ob;

                frame->last_pc = (unsigned char *) pc;

                // zeng: 分配数组对象空间
                if ((ob = allocTypeArray(type, count)) == NULL)
                    goto throwException;

                // zeng: 数组对象地址入栈
                *ostack++ = (u4) ob;

                pc += 2;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_ANEWARRAY) {    // zeng: 创建一个引用类型元素的数组, 将数组入栈
                Class *array_class;
                char ac_name[256];
                int count = ostack[-1];
                Class *class;
                Object *ob;

                frame->last_pc = (unsigned char *) pc;

                // zeng: code下2个字节为constant_pool index, 根据index得到class对象地址
                class = resolveClass(mb->class, CP_DINDEX(pc), FALSE);

                if (exceptionOccured0(ee))
                    goto throwException;

                if (CLASS_CB(class)->name[0] == '[')    // zeng: 如果元素也是数组
                    strcat(strcpy(ac_name, "["), CLASS_CB(class)->name);
                else
                    strcat(strcat(strcpy(ac_name, "[L"), CLASS_CB(class)->name), ";");

                // zeng: 根据 数组全限定名 获得 数组的class对象
                array_class = findArrayClass(ac_name);

                if (exceptionOccured0(ee))
                    goto throwException;

                // zeng:  分配数组空间 元素都只是对象地址 所以元素大小为4个字节
                if ((ob = allocArray(array_class, count, 4)) == NULL)
                    goto throwException;

                // zeng: 数组对象地址入栈
                ostack[-1] = (u4) ob;

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_CHECKCAST) {    // zeng: 类型转换检查
                Object *obj = (Object *) ostack[-1];    // zeng: 栈顶为要检查的对象地址 不出栈
                Class *class;

                frame->last_pc = (unsigned char *) pc;

                class = resolveClass(mb->class, CP_DINDEX(pc), TRUE);   // zeng:  code下2个字节为constant_pool index, 根据index取得类class对象

                if (exceptionOccured0(ee))
                    goto throwException;

                if ((obj != NULL) && !isInstanceOf(class, obj->class)) // zeng: 对象是否class类型
                    THROW_EXCEPTION("java/lang/ClassCastException",CLASS_CB(obj->class)->name); // zeng: 抛出异常

                pc += 3;

                DISPATCH(pc)
            }

            DEF_OPC(OPC_INSTANCEOF) {   // zeng: 检查对象是否是指定的类的实例。如果是，1进栈；否则，0进栈
                Object *obj = (Object *) ostack[-1];     // zeng: 栈顶为要检查的对象地址
                Class *class;

                frame->last_pc = (unsigned char *) pc;

                class = resolveClass(mb->class, CP_DINDEX(pc), FALSE);  // zeng:  code下2个字节为constant_pool index, 根据index取得类class对象

                if (exceptionOccured0(ee))
                    goto throwException;

                if (obj != NULL)
                    ostack[-1] = isInstanceOf(class, obj->class);    // zeng: 对象是否class类型 这里直接将比较结果覆盖栈顶的对象地址 相当于先出栈后入栈

                pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_MONITORENTER) { // zeng: 获得对象锁
                Object *ob = (Object *) *--ostack;  // zeng: 出栈 值为对象地址

                NULL_POINTER_CHECK(ob);

                objectLock(ob);

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_MONITOREXIT) {  // zeng: 释放对象锁
                Object *ob = (Object *) *--ostack;  // zeng: 出栈 值为对象地址

                NULL_POINTER_CHECK(ob);

                objectUnlock(ob);

                pc += 1;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_WIDE) { // zeng: 用于和下一个操作码配合 逻辑和使下一个操作码的逻辑相同 不同的地方是取constant pool时是从code下2个字节取 而不是下1个字节取
                int opcode = pc[1];
                switch (opcode) {
                    case OPC_ILOAD:
                    case OPC_FLOAD:
                    case OPC_ALOAD:
                        *ostack++ = lvars[CP_DINDEX((pc + 1))];
                        pc += 4;
                        break;

                    case OPC_LLOAD:
                    case OPC_DLOAD:
                        *((u8*)ostack)++ = *(u8*)(&lvars[CP_DINDEX((pc+1))]);

                        pc += 4;
                        break;

                    case OPC_ISTORE:
                    case OPC_FSTORE:
                    case OPC_ASTORE:
                        lvars[CP_DINDEX((pc + 1))] = *--ostack;
                        pc += 4;
                        break;

                    case OPC_LSTORE:
                    case OPC_DSTORE:
                        *(u8*)(&lvars[CP_DINDEX((pc+1))]) = *--((u8*)ostack);

                        pc += 4;
                        break;

                    case OPC_RET:
                        pc = (unsigned char *) lvars[CP_DINDEX((pc + 1))];
                        break;

                    case OPC_IINC:
                        lvars[CP_DINDEX((pc + 1))] += DSIGNED((pc + 3));
                        pc += 6;
                        break;
                }

                DISPATCH(pc)    // zeng: 跳转
            }

            DEF_OPC(OPC_MULTIANEWARRAY) {   // zeng: 创建多维数组
                Class *class;
                int dim = pc[3];    // zeng: code pc之后第3个字节为 数组维数
                Object *ob;

                frame->last_pc = (unsigned char *) pc;

                class = resolveClass(mb->class, CP_DINDEX(pc), FALSE);  // zeng: code pc下2个字节为constant_pool index, 通过index取得class对象地址

                if (exceptionOccured0(ee))
                    goto throwException;

                ostack -= dim;  // zeng: 每个维度下的size出栈

                // zeng: 创建多维数组 返回数组对象地址
                if ((ob = allocMultiArray(class, dim, ostack)) == NULL)
                    goto throwException;

                // zeng: 数组对象入栈
                *ostack++ = (u4) ob;

                pc += 4;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_IFNULL) {
                int v = *--ostack;
                if (v == 0) {
                    pc += BRANCH(pc);
                } else
                    pc += 3;
                DISPATCH(pc)
            }

            DEF_OPC(OPC_IFNONNULL) {
                int v = *--ostack;  // zeng: 出栈, 值存入v

                if (v != 0) {   // zeng: v不为0时 pc 加上 pc下2个字节表示的偏移量
                    pc += BRANCH(pc);
                } else  // zeng: 下一个指令
                    pc += 3;

                DISPATCH(pc)
            }

            DEF_OPC(OPC_GOTO_W)
                pc += BRANCH_W(pc); // zeng: pc 加上 pc下4个字节表示的偏移量

                DISPATCH(pc)

            DEF_OPC(OPC_JSR_W)
                *ostack++ = (u4) pc + 3;     // zeng: 下一个指令地址入栈

                pc += BRANCH_W(pc); // zeng: pc 加上 pc下4个字节表示的偏移量

                DISPATCH(pc)

            DEF_OPC(OPC_LOCK)   // zeng: 等待(循环跳转到当前pc)
                DISPATCH(pc)

            DEF_OPC(OPC_INVOKEVIRTUAL_QUICK)
                arg1 = ostack - pc[2];  // zeng: pc[2]为args_count 调用方法时 操作数栈已经入栈了所有参数 这里定位到第0个参数

                NULL_POINTER_CHECK(*arg1);

                new_class = (*(Object **) arg1)->class; // zeng: 第0个参数为this对象地址 这里取得this对象对应的class对象
                new_mb = CLASS_CB(new_class)->method_table[pc[1]];  // zeng: pc[1]为method_table_index 根据index从class对象的method_table中获取MethodBlock地址
                // zeng: DISPATCH 相当于 `goto invokeMethod` 丑陋

            invokeMethod:
            {
                /* Create new frame first.  This is also created for natives
                   so that they appear correctly in the stack trace */

                // zeng: 上一个方法的ostack中包含了所有参数 这里相当于该ostack所有调用参数出栈 然后从ostack之后的地址作为新栈帧的本地方法数组地址 并把出栈的数值复制到这个本地方法数组
                // zeng: 本地方法数组之后是Frame结构体
                Frame *new_frame = (Frame *) (arg1 + new_mb->max_locals);

                Object *sync_ob = NULL;

                // zeng: 检查 地址是否超出栈空间
                if ((char *) new_frame > ee->stack_end) {
                    ee->stack_end += 1024;
                    THROW_EXCEPTION("java/lang/StackOverflowError", NULL);
                }

                new_frame->mb = new_mb;
                new_frame->lvars = arg1;
                new_frame->ostack = (u4 *) (new_frame + 1); // zeng: Frame结构体后是ostack地址
                new_frame->prev = frame;
                frame->last_pc = (unsigned char *) pc;

                ee->last_frame = new_frame; // zeng: 最近的栈帧

                // zeng: synchronized方法 static方法在class对象上上锁 非static方法在this上上锁
                if (new_mb->access_flags & ACC_SYNCHRONIZED) {
                    sync_ob = new_mb->access_flags & ACC_STATIC ? (Object *) new_mb->class : (Object *) *arg1;
                    objectLock(sync_ob);
                }

                if (new_mb->access_flags & ACC_NATIVE) {    // zeng: 是否是native方法 TODO
                    ostack = (*(u4 *(*)(Class *, MethodBlock *, u4 *)) new_mb->native_invoker)(new_mb->class, new_mb, arg1);

                    if (sync_ob)
                        objectUnlock(sync_ob);

                    ee->last_frame = frame;

                    if (exceptionOccured0(ee))
                        goto throwException;

                    pc += *pc == OPC_INVOKEINTERFACE ? 5 : 3;
                } else {
                    // zeng: 更新当前栈帧, 当前方法, 当前本地变量数组, 当前操作数栈, 当前this, 当前consant_pool

                    frame = new_frame;
                    mb = new_mb;
                    lvars = new_frame->lvars;
                    this = (Object *) lvars[0];
                    ostack = new_frame->ostack;

                    // zeng: 更新pc到新方法的code地址
                    pc = mb->code;

                    cp = &(CLASS_CB(mb->class)->constant_pool);
                }

                // zeng: 跳转到新方法执行
                DISPATCH(pc)
            }

            methodReturn:
                /* Set interpreter state to previous frame */

                frame = frame->prev;    // zeng: 当前栈帧出栈

                if (frame->mb == NULL) {    // zeng: 如果是dummy栈帧 说明是c方法调用 直接返回
                    /* The previous frame is a dummy frame - this indicates
                       top of this Java invocation. */
                    return ostack;
                }

                // zeng: synchronized方法 释放锁
                if (mb->access_flags & ACC_SYNCHRONIZED) {
                    Object *sync_ob = mb->access_flags & ACC_STATIC ? (Object *) mb->class : this;

                    objectUnlock(sync_ob);
                }

                // zeng: 更新当前执行环境为调用链上前1个方法
                mb = frame->mb;
                ostack = lvars; // zeng: 上面和return有关的操作码逻辑中, 都将返回值写入本地变量数组index为0处 这里`ostack = lvars`效果就是调用前的ostack状态入栈了一个返回值
                lvars = frame->lvars;
                this = (Object *) lvars[0];
                pc = frame->last_pc;    // zeng: `调用`操作码的pc
                pc += *pc == OPC_INVOKEINTERFACE ? 5 : 3;    // zeng: invokeinterface指令共5个字节(后面两个字节好像没用到?) 其他指令为3个字节 这里就是取得`调用`指令的下一条指令的pc
                cp = &(CLASS_CB(mb->class)->constant_pool);

                /* Pop frame */
                ee->last_frame = frame; // zeng:  更新执行上下文中的当前栈帧

                DISPATCH(pc)

            throwException:
            {
                Object *excep = ee->exception;  // zeng: 从运行上下文中获取异常对象地址

                clearException();   // zeng: 运行上下文中exception设置为null

                // zeng: 查找catch block 返回handler块地址
                pc = findCatchBlock(excep->class);

                if (pc == NULL) {
                    ee->exception = excep;
                    return;
                }

                // zeng: 更新执行环境到catch block所在方法
                frame = ee->last_frame;
                mb = frame->mb;
                ostack = frame->ostack;
                lvars = frame->lvars;
                this = (Object *) lvars[0];
                cp = &(CLASS_CB(mb->class)->constant_pool);

                *ostack++ = (u4) excep; // zeng: 操作数栈中写入异常对象地址

                DISPATCH(pc)    // zeng: 跳转
            }
#ifndef THREADED
        }
    }
#endif
}
