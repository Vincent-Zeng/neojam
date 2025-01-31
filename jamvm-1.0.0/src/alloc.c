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
#include <unistd.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <errno.h>

#include "jam.h"
#include "alloc.h"
#include "thread.h"

/* Trace GC heap mark/sweep phases - useful for debugging heap
 * corruption */
#ifdef TRACEGC
#define TRACE_GC(x) printf x
#else
#define TRACE_GC(x)
#endif

/* Trace class, object and array allocation */
#ifdef TRACEALLOC   // zeng: 是否打印分配日志
#define TRACE_ALLOC(x) printf x
#else
#define TRACE_ALLOC(x)
#endif

/* Trace object finalization */
#ifdef TRACEFNLZ
#define TRACE_FNLZ(x) printf x
#else
#define TRACE_FNLZ(x)
#endif

#define OBJECT_GRAIN        8
#define    ALLOC_BIT        1

#define HEADER(ptr)        *((unsigned int*)ptr)
#define HDR_SIZE(hdr)        (hdr & ~(ALLOC_BIT|FLC_BIT))   // zeng: 标志位置0
#define HDR_ALLOCED(hdr)    (hdr & ALLOC_BIT)   // zeng: 是否已经分配出去

/* 1 word header format
  31                                       210
   -------------------------------------------
  |              block size               |   |
   -------------------------------------------
                                             ^ alloc bit
                                            ^ flc bit
*/

static int verbosegc;

typedef struct chunk {
    unsigned int header;    // zeng: 这个chunk总共的字节数
    struct chunk *next; // zeng: 下一个chunk
} Chunk;

static Chunk *freelist;
static Chunk **chunkpp = &freelist; // zeng: chunk 链表开始地址

static char *heapbase;
static char *heaplimit;
static char *heapmax;

static int heapfree;

static unsigned int *markBits;
static int markBitSize;

static Object **has_finaliser_list = NULL;
static int has_finaliser_count = 0;
static int has_finaliser_size = 0;

static Object **run_finaliser_list = NULL;
static int run_finaliser_start = 0;
static int run_finaliser_end = 0;
static int run_finaliser_size = 0;

static VMLock heap_lock;
static VMLock has_fnlzr_lock;
static VMWaitLock run_fnlzr_lock;

static Object *oom;

#define LIST_INCREMENT        1000

#define LOG_BYTESPERBIT        LOG_OBJECT_GRAIN /* 1 mark bit for every OBJECT_GRAIN bytes of heap */
#define LOG_MARKSIZEBITS    5
#define MARKSIZEBITS        32  // zeng: 用来记录mark

#define MARKENTRY(ptr)    ((((char*)ptr)-heapbase)>>(LOG_BYTESPERBIT+LOG_MARKSIZEBITS)) // zeng: u4型在markBits内的位置
#define MARKOFFSET(ptr)    (((((char*)ptr)-heapbase)>>LOG_BYTESPERBIT) & (MARKSIZEBITS-1)) // zeng: `& (MARKSIZEBITS-1)` 取u4型内的bit位置
#define MARK(ptr)    markBits[MARKENTRY(ptr)] |= 1 << MARKOFFSET(ptr)   // zeng: 使用该地址所在字节 找到 标记位图 中对应位 置为1
#define IS_MARKED(ptr)    (markBits[MARKENTRY(ptr)] & (1<<MARKOFFSET(ptr))) // zeng: 标记位图中对应位 是否为1

// zeng: 地址在java heap地址区间内, 而且是8字节对齐的,就是对象地址 TODO 不会有其他非地址操作数满足这个条件吗
#define IS_OBJECT(ptr)    (((char*)ptr) > heapbase) && \
                        (((char*)ptr) < heaplimit) && \
                        !(((unsigned int)ptr)&(OBJECT_GRAIN-1)) // zeng: 是8字节对齐的

// zeng: 分配标记位图
void allocMarkBits() {
    int no_of_bits = (heaplimit - heapbase) >> LOG_BYTESPERBIT; // zeng: 内存中每个bytes用1个bit标记
    markBitSize = (no_of_bits + MARKSIZEBITS - 1) >> LOG_MARKSIZEBITS;  // zeng: bit 折合多少个 u4型 数( `MARKSIZEBITS - 1` 用于向上取整)

    markBits = (unsigned int *) malloc(markBitSize * sizeof(*markBits));    // zeng: 分配 `markBitSize * 4Byte`用做标记位图 这里还用的是malloc 所以是在java heap外另外申请了一段内存 这内存也不小啊 是java heap的1/8了

    TRACE_GC(("Allocated mark bits - size is %d\n", markBitSize));
}

// zeng: 标记位图所有位置0
void clearMarkBits() {
    memset(markBits, 0, markBitSize * sizeof(*markBits));
}

void initialiseAlloc(int min, int max, int verbose) {

#ifdef USE_MALLOC
    /* Don't use mmap - malloc max heap size */
    // zeng: malloc申请内存
    char *mem = (char*)malloc(max);
    min = max;
#else
    char *mem = (char *) mmap(0, max, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
#endif

    if ((int) mem == 0) {
        printf("Couldn't allocate the heap.  Aborting.\n");
        exit(0);
    }

    // zeng: 堆起始地址
    /* Align heapbase so that start of heap + HEADER_SIZE is object aligned */
    heapbase = (char *) (((int) mem + HEADER_SIZE + OBJECT_GRAIN - 1) & ~(OBJECT_GRAIN - 1)) - HEADER_SIZE;

    // zeng: 堆当前结束地址
    /* Ensure size of heap is multiple of OBJECT_GRAIN */
    heaplimit = heapbase + ((min - (heapbase - mem)) & ~(OBJECT_GRAIN - 1));

    // zeng: 堆最大可分配的结束地址
    heapmax = heapbase + ((max - (heapbase - mem)) & ~(OBJECT_GRAIN - 1));

    // zeng: 堆开始地址处初始化一个chunk信息
    freelist = (Chunk *) heapbase;
    // zeng: 刚开始的这个chunk 基本等同于当前申请到的java heap大小
    freelist->header = heapfree = heaplimit - heapbase;
    // zeng: 没有其他chunk了
    freelist->next = NULL;

    // zeng: 打gc相关日志
    TRACE_GC(("Alloced heap size 0x%x\n", heaplimit - heapbase));
    // zeng: 根据堆大小来分配标记位图, gc用
    allocMarkBits();

    // zeng: 初始化互斥量用来操作堆
    initVMLock(heap_lock);
    // zeng: 初始化互斥量用来操作 `has finalize` 相关
    initVMLock(has_fnlzr_lock);
    // zeng: 初始化互斥量 条件变量 用来操作 `run finalize` 相关
    initVMWaitLock(run_fnlzr_lock);
    // zeng: 是否打gc日志
    verbosegc = verbose;
}

extern void markInternedStrings();

extern void markClasses();

extern void markJNIGlobalRefs();

extern void scanThreads();

void markChildren(Object *ob);

// zeng: 有用的对象做标记
static void doMark(Thread *self) {
    char *ptr;
    int i, j;

    // zeng: 标记位图所有位置0
    clearMarkBits();

    // zeng: OutOfMemoryError 对象肯定有用
    if (oom) MARK(oom);


    // zeng: 所有class对象都标记
    markClasses();
    // zeng: 所有和constant_pool有关的String对象 都做标记
    markInternedStrings();
    // zeng: jni global 引用, 需要做标记
    markJNIGlobalRefs();
    // zeng: 扫描 本地变量数组 和 操作数栈, 找到对象地址 就做标记
    scanThreads();

    /* Grab the run and has finalizer list locks - some thread may
       be inside a suspension-blocked region changing these lists.
       Grabbing ensures any thread has left - they'll self-suspend */

    // zeng: TODO
    lockVMLock(has_fnlzr_lock, self);
    unlockVMLock(has_fnlzr_lock, self);

    // zeng: run_finaliser_list操作 上锁
    lockVMWaitLock(run_fnlzr_lock, self);

    /* Mark any objects waiting to be finalized - they were found to
       be garbage on a previous gc but we haven't got round to finalizing
       them yet - we must mark them as they, and all objects they ref,
       cannot be deleted until the finalizer is ran... */

    // zeng: run_finaliser_end是上次gc确定的等待执行finalize但是还没执行finalize方法的对象 也暂时不能回收 所以这里加上标记
    if (run_finaliser_end > run_finaliser_start)    // zeng: 圆环上结束位置 大于 开始位置
        for (i = run_finaliser_start; i < run_finaliser_end; i++)
            MARK(run_finaliser_list[i]);
    else {  // zeng: 圆环上结束位置 小于等于 开始位置, 列表被原点(run_finaliser_size所在的位置)切成两块
        for (i = run_finaliser_start; i < run_finaliser_size; i++)
            MARK(run_finaliser_list[i]);

        for (i = 0; i < run_finaliser_end; i++)
            MARK(run_finaliser_list[i]);
    }

    /* All roots should now be marked.  Scan the heap and recursively
       mark all marked objects - once the heap has been scanned all
       reachable objects should be marked */

    // zeng: 上面标记的对象都是ROOTS, ROOTS中这些对象的字段中可能又会引用其他对象, 其他对象引用其他对象, 引用链条上的所有对象都是有用的, 都要标记
    for (ptr = heapbase; ptr < heaplimit;) {
        unsigned int hdr = HEADER(ptr);
        int size = HDR_SIZE(hdr);     // chunk -> header, 即chunk大小

#ifdef DEBUG
        printf("Block @0x%x size %d alloced %d\n", ptr, size, HDR_ALLOCED(hdr));
#endif

        if (HDR_ALLOCED(hdr)) { // zeng: 是否是个已经分配的chunk
            Object *ob = (Object *) (ptr + HEADER_SIZE);    // zeng: 对象地址

            if (IS_MARKED(ob))  // zeng: 标记过的对象 (ROOTS)
                markChildren(ob);   // zeng: 这些对象的引用也要标记
        }

        /* Skip to next block */
        ptr += size;    // zeng: 下个chunk
    }

    /* Now all reachable objects are marked.  All other objects are garbage.
       Any object with a finalizer which is unmarked, however, must have it's
       finalizer ran before collecting.  Scan the has_finaliser list and move
       all unmarked objects to the run_finaliser list.  This ensures that
       finalizers are ran only once, even if finalization resurrects the
       object, as objects are only added to the has_finaliser list on
       creation */

    // zeng: 有finalize方法的对象(has_finaliser list 中, 对象只在创建时才会判断要不要加入这个list, 所以对应地最多只能加入run_finaliser_list一次), 如果没有标记, 说明它没有被引用, 但是它还有一次执行finalize的机会, 所以会将其放入run_finaliser_list列表中, 并标记对象(递归标记)
    for (i = 0, j = 0; i < has_finaliser_count; i++) {
        Object *ob = has_finaliser_list[i]; // zeng: 在has_finaliser_list中

        if (!IS_MARKED(ob)) {   // zeng: ROOTS递归标记时没被标记

            markChildren(ob);   // zeng: 递归标记

            if (run_finaliser_start == run_finaliser_end) { // zeng: 圆环 开始位置 等于 结束位置 说明圆环上的文职分配完了
                run_finaliser_start = 0;    // zeng: 数组开始下标
                run_finaliser_end = run_finaliser_size; // zeng: 数组结束下标
                run_finaliser_size += LIST_INCREMENT;   // zeng: 每次多分配1000个元素的空间
                run_finaliser_list = (Object **) realloc(run_finaliser_list,run_finaliser_size * sizeof(Object *)); // zeng: 根据新的数组大小 realloc
            }

            run_finaliser_end = run_finaliser_end % run_finaliser_size; // zeng: 溢出数值范围从0开始再算
            run_finaliser_list[run_finaliser_end++] = ob;   // zeng: 对象地址存入run_finaliser_list中

        } else {
            has_finaliser_list[j++] = ob;   // zeng: 没有加入run_finaliser_end才会留在has_finaliser_list中
        }
    }

    /* After scanning, j holds how many finalizers are left */

    if (j != has_finaliser_count) {
        has_finaliser_count = j;    // zeng: 没有加入run_finaliser_end才会留在has_finaliser_list中

        /* Extra finalizers to be ran, so signal the finalizer thread
           in case it needs waking up.  It won't run until it's
           resumed */

        notifyVMWaitLock(run_fnlzr_lock, self); // zeng: TODO
    }

    // zeng: run_finaliser_list操作 解锁
    unlockVMWaitLock(run_fnlzr_lock, self);
}

// zeng: 回收与合并未标记对象对应chunk(chunk内容区域不置0, 只设置标志位, 分配对象的时候再置0)
static int doSweep(Thread *self) {
    char *ptr;
    Chunk newlist;

    Chunk *last = &newlist; // zeng: 新的freelist

    /* Will hold the size of the largest free chunk
       after scanning */
    int largest = 0;

    /* Variables used to store verbose gc info */
    int marked = 0, unmarked = 0, freed = 0;

    /* Amount of free heap is re-calculated during scan */
    heapfree = 0;

    /* Scan the heap and free all unmarked objects by reconstructing
       the freelist.  Add all free chunks and unmarked objects and
       merge adjacent free chunks into contiguous areas */

    for (ptr = heapbase; ptr < heaplimit;) {    // zeng: 遍历堆里所有对象
        unsigned int hdr = HEADER(ptr); // zeng: Chunk -> header
        int size = HDR_SIZE(hdr);   // zeng: chunk size

        if (HDR_ALLOCED(hdr)) { // zeng: 是分配出去的chunk
            Object *ob = (Object *) (ptr + HEADER_SIZE);    // zeng: 对象开始地址

            if (IS_MARKED(ob))  // zeng: 只回收没有标记的对象
                goto marked;    // zeng: 跳转

            if (ob->lock & 1) { // zeng: 对象是否上锁
                printf("freeing ob with fat lock...\n");
                exit(0);    // zeng: 上锁的对象没被标记是有问题的
            }

            freed += size;  // zeng:  被回收的字节
            unmarked++; // zeng: 没有标记的对象数

            TRACE_GC(("FREE: Freeing ob @ 0x%x class %s - start of block\n", ob,
                    ob->class ? CLASS_CB(ob->class)->name : "?"));
        } else
                TRACE_GC(("FREE: Unalloced block @ 0x%x size %d - start of block\n", ptr, size));

        // zeng: 是空闲的chunk 加入新的freelist中
        /* Add chunk onto the freelist */
        last->next = (Chunk *) ptr; // zeng: 说明last链表中第一个node不是个有效chunk next才是
        last = last->next;

        // zeng: chunk标志位 置0 表示这个chunk没有被分配, 但是并没有将内存每个bit都置0
        /* Clear the alloc and flc bits in the header */
        last->header &= ~(ALLOC_BIT | FLC_BIT);

        /* Scan the next chunks - while they are
           free, merge them onto the first free
           chunk */

        // zeng: 如果接下去的chunk也是可回收的 就把ta们和前一个chunk合并就行了
        for (;;) {
            ptr += size;

            if (ptr >= heaplimit)   // zeng: 遍历完heap区了
                goto out_last_free; // zeng: 跳转

            hdr = HEADER(ptr);
            size = HDR_SIZE(hdr);
            if (HDR_ALLOCED(hdr)) {
                Object *ob = (Object *) (ptr + HEADER_SIZE);

                if (IS_MARKED(ob))  // zeng: 有标记的对象
                    break;  // zeng: 退出循环

                if (ob->lock & 1) {
                    printf("freeing ob with fat lock...\n");
                    exit(0);
                }

                freed += size;
                unmarked++;

                TRACE_GC(("FREE: Freeing object @ 0x%x class %s - merging onto block @ 0x%x\n",
                        ob, ob->class ? CLASS_CB(ob->class)->name : "?", last));

            } else
                    TRACE_GC(("FREE: unalloced block @ 0x%x size %d - merging onto block @ 0x%x\n", ptr, size, last));

            last->header += size;   // zeng: 扩大上一个chunk的大小
        }

        /* Scanned to next marked object see if it's
           the largest so far */

        // zeng: 最大的chunk是多大
        if (last->header > largest)
            largest = last->header;

        /* Add onto total count of free chunks */
        // zeng: java heap空闲字节
        heapfree += last->header;

        marked:
        marked++;   // zeng: 标记的对象数

        /* Skip to next block */
        ptr += size;    // zeng: 下一个chunk

        if (ptr >= heaplimit)   // zeng: 遍历完heap了
            goto out_last_marked;
    }

    out_last_free:

    /* Last chunk is free - need to check if
       largest */
    // zeng: 最大的chunk是多大
    if (last->header > largest)
        largest = last->header;

    // zeng: java heap空闲字节
    heapfree += last->header;

    out_last_marked:

    /* We've now reconstructed the freelist, set freelist
       pointer to new list */
    last->next = NULL;  // zeng: 没有下一个chunk了
    freelist = newlist.next;    // zeng: 新的free list

    /* Reset next allocation block to beginning of list -
       this leads to a search - use largest instead? */
    chunkpp = &freelist;    // zeng: 下次查找空闲chunk时从新的freelist重新开始

#ifdef DEBUG
    {
        Chunk *c;
        for(c = freelist; c != NULL; c = c->next)
            printf("Chunk @0x%x size: %d\n", c, c->header);
    }
#endif

    // zeng: gc 日志
    if (verbosegc) {
        int size = heaplimit - heapbase;
        long long pcnt_used = ((long long) heapfree) * 100 / size;  // zeng:  空闲率
        printf("<GC: Allocated objects: %d>\n", marked);
        printf("<GC: Freed %d objects using %d bytes>\n", unmarked, freed);
        printf("<GC: Largest block is %d total free is %d out of %d (%lld%)>\n",
               largest, heapfree, size, pcnt_used);
    }

    /* Return the size of the largest free chunk in heap - this
       is the largest allocation request that can be satisfied */

    return largest;
}

/* Run all outstanding finalizers.  This is called synchronously
 * if we run out of memory and asyncronously by the finalizer
 * thread.  In both cases suspension is disabled, to reduce
 * back-to-back enable/disable... */

static Thread *runningFinalizers = NULL;

// zeng: 遍历run_fnlzr_lock执行
static int runFinalizers() {
    Thread *self = threadSelf();
    int ret = FALSE;

    // zeng: run_fnlzr_list 操作锁
    lockVMWaitLock(run_fnlzr_lock, self);

    // zeng: 只有一个线程在执行 有必要吗
    if (runningFinalizers == self)
        goto out;

    // zeng: 有必要吗
    while (runningFinalizers) {
        ret = TRUE;
        waitVMWaitLock(run_fnlzr_lock, self);
    }

    // zeng: run_finaliser_list里没有元素了
    if ((run_finaliser_start == run_finaliser_size) && (run_finaliser_end == 0))
        goto out;

    // zeng: 有必要吗
    runningFinalizers = self;

    TRACE_FNLZ(("run_finaliser_start %d\n", run_finaliser_start));
    TRACE_FNLZ(("run_finaliser_end %d\n", run_finaliser_end));
    TRACE_FNLZ(("run_finaliser_size %d\n", run_finaliser_size));

    if (verbosegc) {
        int diff = run_finaliser_end - run_finaliser_start;
        printf("<Running %d finalizers>\n", diff > 0 ? diff : diff + run_finaliser_size);
    }

    // zeng: 遍历run_finaliser_list执行finalize方法
    do {
        Object *ob;

        // zeng: 取run_finaliser_list中的对象
        run_finaliser_start %= run_finaliser_size;
        ob = run_finaliser_list[run_finaliser_start];

        // zeng: 释放锁
        unlockVMWaitLock(run_fnlzr_lock, self);
        // zeng: 允许被暂停
        enableSuspend(self);

        // zeng: 执行finalize方法
        /* Run the finalizer method */
        executeMethod(ob, CLASS_CB(ob->class)->finalizer);

        /* We entered with suspension off - nothing
         * else interesting on stack, so use previous
         * stack top. */

        // zeng: 不允许被暂停
        disableSuspend0(self, getStackTop(self));
        // zeng: 上锁
        lockVMWaitLock(run_fnlzr_lock, self);

        /* Clear any exceptions - exceptions thrown in finalizers are
           silently ignored */
        // zeng: finalize方法抛出的异常忽略
        clearException();
    } while (++run_finaliser_start != run_finaliser_end);

    // zeng: 遍历完重置圆环状态
    run_finaliser_start = run_finaliser_size;
    run_finaliser_end = 0;
    runningFinalizers = NULL;

    ret = TRUE;

    out:
    // zeng: TODO
    notifyVMWaitLock(run_fnlzr_lock, self);
    // zeng: 释放锁
    unlockVMWaitLock(run_fnlzr_lock, self);

    return ret;
}

static long getTime() {
    struct timeval tv;

    gettimeofday(&tv, 0);
    return tv.tv_usec;
}

static long endTime(long start) {
    long time = getTime() - start;

    return time < 0 ? 1000000 - time : time;
}

// zeng: 扫描回收无用对象的空间 很明显是 标记 - 清除算法
int gc0() {
    Thread *self = threadSelf();
    long start;
    float scan_time;
    float mark_time;
    int largest;

    // zeng: 暂停所有其他线程
    suspendAllThreads(self);

    start = getTime();
    doMark(self);   // zeng: 标记有用对象
    scan_time = endTime(start) / 1000000.0;

    start = getTime();
    largest = doSweep(self);    // zeng: 回收与合并未标记对象对应chunk
    mark_time = endTime(start) / 1000000.0;

    // zeng: 恢复所有其他线程
    resumeAllThreads(self);

    if (verbosegc)
        printf("<GC: Mark took %f seconds, scan took %f seconds>\n", scan_time, mark_time);

    return largest;
}

int gc1() {
    Thread *self;

    // zeng: 禁止被暂停
    disableSuspend(self = threadSelf());

    // zeng: heap操作 锁
    lockVMLock(heap_lock, self);

    // zeng: 扫描回收无用对象的空间
    gc0();

    // zeng: 释放锁
    unlockVMLock(heap_lock, self);

    // zeng: 允许被暂停
    enableSuspend(self);
}

// zeng: 扩充java heap大小
void expandHeap(int min) {  // zeng: min 最少需要扩大的字节数
    Chunk *chunk, *new;
    int delta;

    if (verbosegc)
        printf("<GC: Expanding heap - minimum needed is %d>\n", min);

    delta = (heaplimit - heapbase) / 2; // zeng: 之前java heap 的 1/2
    delta = delta < min ? min : delta;  // zeng: min(delta, min)

    if ((heaplimit + delta) > heapmax)  // zeng: 大于最大可分配的java heap字节数
        delta = heapmax - heaplimit;    // zeng: 扩大到 最大可分配的java heap字节数

    /* Ensure new region is multiple of object grain in size */
    // zeng: 对齐
    delta = (delta & ~(OBJECT_GRAIN - 1));

    if (verbosegc)
        printf("<GC: Expanding heap by %d bytes>\n", delta);

    /* The freelist is in address order - find the last
       free chunk and add the new area to the end.  */

    // zeng: freelist链表最后一个chunk
    for (chunk = freelist; chunk->next != NULL; chunk = chunk->next);

    // zeng: 新分配的空间当成一个chunk

    new = (Chunk *) heaplimit;  // zeng: chunk地址
    new->header = delta;    // zeng:  chunk大小
    new->next = 0;  // zeng: 这是最后一个chunk

    chunk->next = new;  // zeng: 原先最后一个chunk 变成倒数第2个chunk

    heaplimit += delta; // zeng: 更新当前heap大小
    heapfree += delta;  // zeng: 更新当前空闲heap大小

    /* The heap has increased in size - need to reallocate
       the mark bits to cover new area */
    // zeng: 重新分配标记位图
    free(markBits);
    allocMarkBits();
}

// zeng: 在java heap中申请len字节的内存 java heap是jvm自己管理的(管理有很多方式 都是在 分配效率 和 回收效率 做权衡, 这也意味 分配算法 和 回收算法之间 要搭配)
void *gcMalloc(int len) {
    static int state = 0; /* allocation failure action */

    // zeng: 本次申请消耗内存 = len + chunk结构体4字节 + 对齐
    int n = (len + HEADER_SIZE + OBJECT_GRAIN - 1) & ~(OBJECT_GRAIN - 1);

    Chunk *found;
    int largest;
    Thread *self;
#ifdef TRACEALLOC
    int tries;
#endif

    /* See comment below */
    char *ret_addr;

    // zeng: 不接收暂停信号
    disableSuspend(self = threadSelf());

    // zeng: 进行堆操作要上锁
    lockVMLock(heap_lock, self);

    /* Scan freelist looking for a chunk big enough to
       satisfy allocation request */

    for (;;) {
#ifdef TRACEALLOC
        tries = 0;
#endif
        while (*chunkpp) {
            int len = (*chunkpp)->header;   // zeng: 这个chunk有多少字节

            if (len == n) { // zeng: 刚好等于本次申请消耗内存
                found = *chunkpp;   // zeng: 就用chunk这段内存了
                *chunkpp = found->next; // zeng: 从 free chunk 链表 中移除这个chunk
                goto gotIt;
            }

            if (len > n) {  // zeng: chunk比`本次申请消耗内存`大
                Chunk *rem;
                found = *chunkpp;
                rem = (Chunk *) ((char *) found + n);   // zeng: chunk开头取n字节

                rem->header = len - n;  // zeng: 更新这个chunk的大小
                rem->next = found->next;    // zeng: 复制原chunk结构体的next
                *chunkpp = rem; // zeng: 更新这个chunk的开始地址
                goto gotIt;
            }

            // zeng: chunk比`本次申请消耗内存`小 找下一个chunk
            chunkpp = &(*chunkpp)->next;

#ifdef TRACEALLOC
            tries++;    // zeng: 遍历经过1个chunk 就+1
#endif
        }

        if (verbosegc)
            printf("<GC: Alloc attempt for %d bytes failed (state %d).>\n", n, state);

        switch (state) {    // zeng: 进行一次gc 看能不能有合适大小的chunk

            case 0: // zeng: 当前chunk list链表中分配不到需要的内存
                largest = gc0();    // zeng: 扫描回收无用对象的空间
                if (n <= largest)   // zeng: 回收之后最大的chunk大于等于n
                    break;  // zeng: 跳出switch 开始下次的for循环 遍历chunkpp查找合适的chunk分配

                // zeng: 回收之后最大的chunk还小于n
                state = 1;
                // zeng: 没有break 继续执行 case 1

            case 1: {   // zeng: 先执行run_finaliser_list 以使run_finaliser_list中的对象都不需要再被标记 再执行gc 看能不能有合适大小的chunk分配
                int res;

                unlockVMLock(heap_lock, self);  // zeng: 释放锁

                res = runFinalizers();  // zeng: 遍历run_finaliser_list执行

                lockVMLock(heap_lock, self);    // zeng: heap操作 锁

                if (state == 1) {
                    if (res) {  // zeng: 存在 finalize被执行的对象, 才有可能比上次gc回收更多的对象
                        largest = gc0();    // zeng: 再进行一次gc
                        if (n <= largest) { // zeng: 回收之后最大的chunk大于等于n
                            state = 0;
                            break;  // zeng: 跳出switch 开始下次的for循环 遍历chunkpp查找合适的chunk分配
                        }
                    }

                    // zeng: 回收之后最大的chunk还小于n
                    state = 2;
                }
                break;  // zeng: 跳出switch 开始下次的for循环 遍历chunkpp查找合适的chunk分配 如果还没找到合适的chunk 就执行case 2

                case 2: // zeng: 这里case 2 在 case 1程序块 里是为什么 , 和不在这个语句块好像也没什么分别 TODO
                    if (heaplimit < heapmax) {  // zeng: java heap 还允许扩大
                        expandHeap(n);  // zeng: 扩大java heap大小
                        state = 0;
                        break;   // zeng: 跳出switch 开始下次的for循环 遍历chunkpp查找合适的chunk分配(下次遍历时*chunkpp为NULL, 还是分配不到, 所以还要先经过一次gc0来使得chunkpp从freelist第一个node重新开始)
                    } else {
                        if (verbosegc)
                            printf("<GC: Stack at maximum already - completely out of heap space>\n");

                        state = 3;
                        /* Reset next allocation block * to beginning of list */
                        chunkpp = &freelist; // zeng: 下一次查找空闲chunk从freelist重新开始.  每次gcMalloc没有重置chunkpp 所以每次查找不是都找整个freelist? 是的,但是gc0中有重置, 所以gc后会查找整个freelist

                        // zeng: 允许被暂停
                        enableSuspend(self);

                        // zeng:释放锁
                        unlockVMLock(heap_lock, self);

                        // zeng: 抛出oom异常
                        signalException("java/lang/OutOfMemoryError", NULL);

                        return NULL;
                    }
                break;
            }

            case 3:
                /* Already throwing an OutOfMemoryError in some thread.  In both
                 * cases, throw an already prepared OOM (no stacktrace).  Could have a
                 * per-thread flag, so we try to throw a new OOM in each thread, but
                 * if we're this low on memory I doubt it'll make much difference.
                 */

                state = 0;
                // zeng: 允许被暂停
                enableSuspend(self);
                // zeng: 释放锁
                unlockVMLock(heap_lock, self);
                // zeng: 这个线程执行上下文也抛出oom TODO 线程?
                setException(oom);

                return NULL;

                break;
        }
    }

    gotIt:
#ifdef TRACEALLOC
    printf("<ALLOC: took %d tries to find block.>\n", tries);
#endif

    // zeng: java heap 还剩多少内存
    heapfree -= n;

    // zeng: header最右边1位 置为 1, 表示这个 chunk 已经分配出去了
    // zeng: 因为n已经使用`粒度对齐`来保证n的大小是8的倍数,也就是最右3位都为0, 所以这里可以使用最右3位来作为标志位记录其他信息
    /* Mark found chunk as allocated */
    found->header = n | ALLOC_BIT;

    /* Found is a block pointer - if we unlock now, small window
     * where new object ref is not held and will therefore be gc'ed.
     * Setup ret_addr before unlocking to prevent this.
     */

    // zeng: 逃过chunk结构体 才是申请到的内存的开始地址
    ret_addr = ((char *) found) + HEADER_SIZE;

    // zeng: 内存每个bit都设为0
    memset(ret_addr, 0, n - HEADER_SIZE);

    // zeng: 允许被暂停
    enableSuspend(self);
    // zeng: 释放锁
    unlockVMLock(heap_lock, self);

    return ret_addr;
}

/* Object roots :-
	classes
	class statics
	interned strings
	thread Java stacks
        thread C stacks
	thread registers (put onto C stack)
        JNI refs
	    - locals (scanned as part of JavaStack)
	    - globals
*/

// zeng: Class 中 FieldBlock -> static_value 可能为 对象引用, 也要标记
void markClassStatics(Class *class) {
    ClassBlock *cb = CLASS_CB(class);
    FieldBlock *fb = cb->fields;
    int i;

    TRACE_GC(("Marking static fields for class %s\n", cb->name));

    for (i = 0; i < cb->fields_count; i++, fb++)
        if ((fb->access_flags & ACC_STATIC) && ((*fb->type == 'L') || (*fb->type == '['))) {

            Object *ob = (Object *) fb->static_value;
            TRACE_GC(("Field %s %s\n", fb->name, fb->type));
            TRACE_GC(("Object @0x%x is valid %d\n", ob, IS_OBJECT(ob)));
            if (IS_OBJECT(ob) && !IS_MARKED(ob))
                markChildren(ob);   // zeng: 递归标记

        }
}

// zeng: 所有线程下 所有 栈帧 的 本地变量数组 和 操作数栈 中 持有 对象地址, 说明这个对象有用, 要标记
void scanThread(Thread *thread) {
    ExecEnv *ee = thread->ee;   // zeng: 这个线程的执行上下文
    Frame *frame = ee->last_frame;  // zeng: 这个线程的当前栈帧

    u4 *end, *slot;

    TRACE_GC(("Scanning stacks for thread 0x%x\n", thread));

    MARK(ee->thread);

    // zeng: TODO
    slot = (u4 *) getStackTop(thread);
    // zeng: TODO
    end = (u4 *) getStackBase(thread);

    // zeng: TODO
    for (; slot < end; slot++)
        if (IS_OBJECT(*slot)) {
            Object *ob = (Object *) *slot;
            TRACE_GC(("Found C stack ref @0x%x object ref is 0x%x\n", slot, ob));
            MARK(ob);
        }

    // zeng: ostack结束地址
    slot = frame->ostack + frame->mb->max_stack;

    while (frame->prev != NULL) {   // zeng: 不是最顶层栈帧时
        if (frame->mb != NULL) {
            TRACE_GC(("Scanning %s.%s\n", CLASS_CB(frame->mb->class)->name, frame->mb->name));
            TRACE_GC(("lvars @0x%x ostack @0x%x\n", frame->lvars, frame->ostack));
        }

        // zeng: ostack开始地址
        end = frame->ostack;

        // zeng: 操作数栈中存在的对象地址 做标记
        for (; slot >= end; slot--)
            if (IS_OBJECT(*slot)) {
                Object *ob = (Object *) *slot;
                TRACE_GC(("Found Java stack ref @0x%x object ref is 0x%x\n", slot, ob));
                MARK(ob);   // zeng: 标记对象   对象中字段引用的对象没标记? 这里只用来标记ROOTS, 后面会遍历ROOTS, 找到每条引用链, 标记链上的所有对象
            }

        // zeng: 得到本栈帧的本地变量表结束地址 也就是下一次循环 [end, slot] 区间包括 本栈帧 的本地向量数组 和 前一个栈帧的 操作数栈
        slot -= sizeof(Frame) / 4;

        // zeng: 前一个栈帧
        frame = frame->prev;
    }
}

// zeng: 标记class对象
void markClass(Class *class) {
    MARK(class);
}

void markObject(Object *object) {
    MARK(object);
}

// zeng: 递归标记引用对象
void markChildren(Object *ob) {

    MARK(ob);   // zeng: 标记自身

    if (ob->class == NULL)  // zeng: 说明不是个对象
        return;

    if (IS_CLASS(ob)) { // zeng: 是Class对象
        TRACE_GC(("Found class object @0x%x name is %s\n", ob, CLASS_CB(ob)->name));
        markClassStatics((Class *) ob);
    } else {    // zeng: 非Class对象
        Class *class = ob->class;
        ClassBlock *cb = CLASS_CB(class);
        u4 *body = INST_DATA(ob);   // zeng: 对象内容体

        if (cb->name[0] == '[') {   // zeng: 是数组对象

            if ((cb->name[1] == 'L') || (cb->name[1] == '[')) { // zeng: 元素是 对象 或者 数组
                int len = body[0];  // zeng:数组长度
                int i;
                TRACE_GC(("Scanning Array object @0x%x class is %s len is %d\n", ob, cb->name, len));

                for (i = 1; i <= len; i++) {
                    Object *ob = (Object *) body[i];    // zeng: 元素 为 对象地址

                    TRACE_GC(("Object at index %d is @0x%x is valid %d\n", i - 1, ob, IS_OBJECT(ob)));

                    if (IS_OBJECT(ob) && !IS_MARKED(ob))    // zeng: 是对象 且 还没 标记 过
                        markChildren(ob);   // zeng: 递归标记
                }

            } else {
                TRACE_GC(("Array object @0x%x class is %s  - Not Scanning...\n", ob, cb->name));
            }

        } else {    // zeng: 非数组对象

            FieldBlock *fb;
            int i;

            TRACE_GC(("Scanning object @0x%x class is %s\n", ob, cb->name));

            /* Scan fieldblocks in current class and all super-classes
               and mark all object refs */

            for (;;) {
                // zeng: 本类的所有字段
                fb = cb->fields;

                TRACE_GC(("scanning fields of class %s\n", cb->name));

                for (i = 0; i < cb->fields_count; i++, fb++)
                    if (!(fb->access_flags & ACC_STATIC) && ((*fb->type == 'L') || (*fb->type == '['))) {   // zeng: 非static字段(static字段在前面判断为class对象时遍历) 且字段为对象引用或者数组引用时
                        Object *ob = (Object *) body[fb->offset];   // zeng: 字段的值
                        TRACE_GC(("Field %s %s is an Object ref\n", fb->name, fb->type));
                        TRACE_GC(("Object @0x%x is valid %d\n", ob, IS_OBJECT(ob)));

                        if (IS_OBJECT(ob) && !IS_MARKED(ob))    // zeng: 值为对象引用 且为 标记
                            markChildren(ob);   // zeng: 递归标记
                    }

                // zeng: 祖先类的字段也要遍历
                class = cb->super;

                if (class == NULL)
                    break;

                // zeng: 超类的ClassBlock
                cb = CLASS_CB(class);
            }

        }
    }
}


/* Routines to retrieve snapshot of heap status */

int freeHeapMem() {
    return heapfree;
}

int totalHeapMem() {
    return heaplimit - heapbase;
}

int maxHeapMem() {
    return heapmax - heapbase;
}

/* The async gc loop.  It sleeps for 1 second and
 * calls gc if the system's idle and the heap's
 * changed */

// zeng: 循环进行 gc 操作, 每次间隔 1s
void asyncGCThreadLoop(Thread *self) {
    for (;;) {
        threadSleep(self, 1000, 0);

        if (systemIdle(self))
            gc1();
    }
}

/* The finalizer thread waits for notification
 * of new finalizers (by the thread doing gc)
 * and then runs them */

// zeng: 遍历run_fnlzr_lock执行 无限循环
void finalizerThreadLoop(Thread *self) {
    // zeng:不允许被暂停
    disableSuspend0(self, &self);

    for (;;) {
        // zeng: TODO
        lockVMWaitLock(run_fnlzr_lock, self);
        waitVMWaitLock(run_fnlzr_lock, self);
        unlockVMWaitLock(run_fnlzr_lock, self);

        // zeng: 遍历run_fnlzr_lock执行
        runFinalizers();
    }
}

// zeng: 初始化gc
void initialiseGC(int noasyncgc) {
    /* Pre-allocate an OutOfMemoryError exception object - we throw it
     * when we're really low on heap space, and can create FA... */

    MethodBlock *init;
    // zeng: 加载 初始化OutOfMemoryError类
    Class *oom_clazz = findSystemClass("java/lang/OutOfMemoryError");
    if (exceptionOccured()) {
        printException();
        exit(1);
    }

    // zeng:分配OutOfMemoryError对象 并调用初始化方法
    init = lookupMethod(oom_clazz, "<init>", "(Ljava/lang/String;)V");
    oom = allocObject(oom_clazz);
    executeMethod(oom, init, NULL);

    // zeng: 启动一个线程执行finalize列表
    /* Create and start VM threads for the async gc and finalizer */
    createVMThread("Finalizer", finalizerThreadLoop);

    // zeng: noasyncgc: 不开启异步gc
    if (!noasyncgc)
        createVMThread("Async GC", asyncGCThreadLoop);  // zeng: 启动一个线程进行周期gc
}

/* Object allocation routines */
// zeng: 将对象加入has_fnlzr_list
#define ADD_FINALIZED_OBJECT(ob)                                                   \
{                                                                                  \
    Thread *self;                                                                  \
    disableSuspend(self = threadSelf());                                           \    // zeng: 不允许被暂停
    lockVMLock(has_fnlzr_lock, self);                                              \    // zeng: has_fnlzr_list 操作锁
    TRACE_FNLZ(("Object @0x%x type %s has a finalize method...\n",              \
                                      ob, CLASS_CB(ob->class)->name));             \
    if(has_finaliser_count == has_finaliser_size) {                                \    // zeng: has_finaliser_list 数组满了
        has_finaliser_size += LIST_INCREMENT;                                      \    // zeng: 每次多分配1000
        has_finaliser_list = (Object**)realloc(has_finaliser_list,                 \    // zeng: realloc
                                   has_finaliser_size*sizeof(Object*));\
    }                                                                              \
                                                                                   \
    has_finaliser_list[has_finaliser_count++] = ob;                                \    // zeng: 加入数组
    unlockVMLock(has_fnlzr_lock, self);                                            \    // zeng: 释放锁
    enableSuspend(self);                                                           \    // zeng: 允许被暂停
}

// zeng: 分配 对象 空间
Object *allocObject(Class *class) {
    ClassBlock *cb = CLASS_CB(class);
    // zeng: 对象内容字节数
    int size = cb->object_size * 4;

    // zeng: 对象内容字节数 + Object数据结构大小
    Object *ob = (Object *) gcMalloc(size + sizeof(Object));

    if (ob != NULL) {
        // zeng: object数据结构的class 指向 对象 对应的类
        ob->class = class;

        // zeng: 如果类中(包括祖先类)有finalize方法
        if (cb->finalizer != NULL) ADD_FINALIZED_OBJECT(ob);

        // zeng: 打印分配日志
        TRACE_ALLOC(("<ALLOC: allocated %s object @ 0x%x>\n", cb->name, ob));
    }

    return ob;
}

// zeng: 分配数组对象(元素为对象)空间
Object *allocArray(Class *class, int size, int el_size) {
    Object *ob;

    if (size < 0) {
        signalException("java/lang/NegativeArraySizeException", NULL);
        return NULL;
    }

    // zeng: 分配数组对象空间 返回对象地址 (元素所占字节 + 长度数值所占字节 + Object结构体所占字节)
    ob = (Object *) gcMalloc(size * el_size + 4 + sizeof(Object));

    if (ob != NULL) {
        // zeng: 对象体刚开始是数组长度
        *INST_DATA(ob) = size;

        // zeng: 数组object -> class 为 数组的class
        ob->class = class;

        // zeng: 打印分配日志
        TRACE_ALLOC(("<ALLOC: allocated %s array object @ 0x%x>\n", CLASS_CB(class)->name, ob));
    }

    return ob;
}

// zeng: 分配数组对象(元素为基本类型)空间
Object *allocTypeArray(int type, int size) {
    Class *class;
    int el_size;

    // zeng: 找到基本类型对应的class
    switch (type) {
        case T_BYTE:
        case T_BOOLEAN:
            class = findArrayClass("[B");
            el_size = 1;
            break;

        case T_CHAR:
            class = findArrayClass("[C");
            el_size = 2;
            break;

        case T_SHORT:
            class = findArrayClass("[S");
            el_size = 2;
            break;

        case T_INT:
            class = findArrayClass("[I");
            el_size = 4;
            break;

        case T_FLOAT:
            class = findArrayClass("[F");
            el_size = 4;
            break;

        case T_DOUBLE:
            class = findArrayClass("[D");
            el_size = 8;
            break;

        case T_LONG:
            class = findArrayClass("[J");
            el_size = 8;
            break;

        default:
            printf("Invalid array type %d - aborting VM...\n", type);
            exit(0);
    }

    // zeng: 分配数组对象(元素为对象)空间
    return allocArray(class, size, el_size);
}

// zeng: 分配多维数组
Object *allocMultiArray(Class *array_class, int dim, int *count) {

    int i;
    Object *array;

    if (dim > 1) {
        Class *aclass = findArrayClassFromClass(CLASS_CB(array_class)->name + 1,
                                                array_class);    // zeng: 第1个维度下元素类型class对象

        array = allocArray(array_class, *count, 4);

        if (array == NULL)
            return NULL;

        for (i = 1; i <= *count; i++)    // zeng: 第1个维度下遍历元素, 由于元素类型也是数组, 所以递归调用
            INST_DATA(array)[i] = (u4) allocMultiArray(aclass, dim - 1,
                                                       count + 1);  // zeng: 返回值是数组对象地址 所以每个格子保存的都是数组对象地址

    } else {    // zeng: 递归出口
        int el_size;

        // zeng: 根据类型分配元素字节数
        switch (CLASS_CB(array_class)->name[1]) {
            case 'B':
            case 'Z':
                el_size = 1;
                break;

            case 'C':
            case 'S':
                el_size = 2;
                break;

            case 'I':
            case 'F':
            case 'L':   // zeng: 对象地址
                el_size = 4;
                break;

            default:    // zeng: Double Long
                el_size = 8;
                break;
        }

        // zeng: 分配数组对象空间 返回数组对象地址
        array = allocArray(array_class, *count, el_size);
    }

    return array;
}

Class *allocClass() {
    // zeng: 从java heap中分配一个 Class + ClassBlock的空间 也就是Class后紧接着就是ClassBlock
    Class *class = (Class *) gcMalloc(sizeof(ClassBlock) + sizeof(Class));

    // zeng: 打印分配日志
    TRACE_ALLOC(("<ALLOC: allocated class object @ 0x%x>\n", class));

    return class;
}

// zeng: 复制对象, 返回复制的对象地址
Object *cloneObject(Object *ob) {
    // zeng: 对象所在的chunk结构体地址
    unsigned int hdr = HEADER((((char *) ob) - HEADER_SIZE));
    // zeng: chunk的大小减去chunk结构体大小 为对象大小
    int size = HDR_SIZE(hdr) - HEADER_SIZE;

    // zeng: gcMalloc分配一个新的chunk
    Object *clone = (Object *) gcMalloc(size);

    if (clone != NULL) {
        // zeng: memcpy复制对象内容
        memcpy(clone, ob, size);
        // zeng: 无锁
        clone->lock = 0;

        // zeng: 如果对象有finalize方法,  将对象加入has_fnlzr_list
        if (CLASS_CB(clone->class)->finalizer != NULL) ADD_FINALIZED_OBJECT(clone);

        TRACE_ALLOC(("<ALLOC: cloned object @ 0x%x clone @ 0x:%x>\n", ob, clone));
    }

    return clone;
}
