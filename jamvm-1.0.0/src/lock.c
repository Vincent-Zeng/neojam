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
#include <errno.h>
#include <sys/time.h>

#include "jam.h"
#include "thread.h"
#include "hash.h"
#include "alloc.h"

#include "lock_md.h"

/* Trace lock operations and inflation/deflation */
#ifdef TRACELOCK
#define TRACE(x) printf x
#else
#define TRACE(x)
#endif

#define HASHTABSZE 1<<5
#define HASH(obj) ((int) obj >> LOG_OBJECT_GRAIN)
#define COMPARE(obj, mon, hash1, hash2) hash1 == hash2
// zeng: 分配一个monitor结构体
#define PREPARE(obj) allocMonitor(obj)
// zeng: in_use设为TRUE 表示该monitor结构体在使用中
#define FOUND(ptr) ptr->in_use = TRUE

// zeng: 轻量锁shape bit为0, 高位为thread id
// zeng: 重量锁shape bit为1, 高位为monitor对象地址
/* lockword format in "thin" mode
  31                                         0
   -------------------------------------------
  |              thread ID          | count |0|
   -------------------------------------------
                                             ^ shape bit

  lockword format in "fat" mode
  31                                         0
   -------------------------------------------
  |                 Monitor*                |1|
   -------------------------------------------
                                             ^ shape bit
*/

#define SHAPE_BIT   0x1
#define COUNT_SIZE  8
#define COUNT_SHIFT 1
#define COUNT_MASK  (((1<<COUNT_SIZE)-1)<<COUNT_SHIFT)

#define TID_SHIFT   (COUNT_SIZE+COUNT_SHIFT)
#define TID_SIZE    32-TID_SHIFT
#define TID_MASK    (((1<<TID_SIZE)-1)<<TID_SHIFT)

// zeng: 扫描hash表, 将in_use为FALSE的monitor结构体加入mon_free_list队列中
#define SCAVENGE(ptr)                            \
({                                               \
    Monitor *mon = (Monitor *)ptr;               \
    char res = !mon->in_use;                     \
    if(res) {                                    \
        mon->next = mon_free_list;               \
        mon_free_list = mon;                     \
        mon->in_use = TRUE;                      \
    }                                            \
    res;                                         \
})

static Monitor *mon_free_list = NULL;
static HashTable mon_cache;

// zeng: 初始化monitor
void monitorInit(Monitor *mon) {
    pthread_mutex_init(&mon->lock, NULL);
    pthread_cond_init(&mon->cv, NULL);
    mon->owner = 0;
    mon->count = 0;
    mon->waiting = 0;
    mon->notifying = 0;
    mon->interrupting = 0;
    mon->entering = 0;
}

// zeng: 线程 竞争成为 monitor对象的持有者
void monitorLock(Monitor *mon, Thread *self) {
    if (mon->owner == self) // zeng: 如果monitor对象的持有者是本线程
        mon->count++;   // zeng: 重入次数+1
    else {
        mon->entering++;    // zeng: 进入enter等待队列的线程数+1
        disableSuspend(self);   // zeng: 不允许被暂停

        self->state = WAITING;  // zeng: 本线程状态改为WAITING

        pthread_mutex_lock(&mon->lock); // zeng: 争取monitor互斥锁

        // zeng: 执行到这里争取到了monitor互斥锁

        self->state = RUNNING;  // zeng: 本线程状态改为RUNNING

        // zeng: 允许被暂停
        enableSuspend(self);

        mon->entering--;    // zeng: 进入enter等待队列的线程-1

        // zeng: 争取到了monitor互斥锁, monitor的持有者设为本线程
        mon->owner = self;
    }
}

// zeng: 尝试持有monitor, 持有失败线程不进入WAIT状态, 而是直接返回失败
int monitorTryLock(Monitor *mon, Thread *self) {
    if (mon->owner == self)
        mon->count++;   // zeng: 重入次数+1
    else {
        if (pthread_mutex_trylock(&mon->lock))
            return FALSE;
        mon->owner = self;  // zeng: 持有者为当前线程
    }

    return TRUE;
}

// zeng: 退出持有 monitor结构体
void monitorUnlock(Monitor *mon, Thread *self) {
    if (mon->owner == self)
        if (mon->count == 0) {  // zeng: 如果没有重入
            mon->owner = 0; // zeng: owner置0
            pthread_mutex_unlock(&mon->lock);   // zeng: 释放互斥锁
        } else
            mon->count--;   // zeng: 重入数-1
}

// zeng: 线程进行wait等待队列, 直到条件满足被唤醒或者被interrupt
int monitorWait(Monitor *mon, Thread *self, long long ms, int ns) {
    char interrupted = 0;
    int old_count;

    // zeng: 有超时时间
    char timed = (ms != 0) || (ns != 0);

    struct timespec ts;

    // zeng: 当前线程是monitor的持有者
    if (mon->owner != self)
        return FALSE;

    /* We own the monitor */

    disableSuspend(self);

    old_count = mon->count;

    // zeng: 不再持有该monitor结构体
    mon->count = 0;
    mon->owner = NULL;

    // zeng: 等待waiting等待队列的线程数
    mon->waiting++;

    if (timed) {
        struct timeval tv;

        gettimeofday(&tv, 0);

        ts.tv_sec = tv.tv_sec + ms / 1000;
        ts.tv_nsec = (tv.tv_usec + ((ms % 1000) * 1000)) * 1000 + ns;

        if (ts.tv_nsec > 999999999L) {
            ts.tv_sec++;
            ts.tv_nsec -= 1000000000L;
        }
    }

    // zeng: 当前线程在等待哪个monitor
    self->wait_mon = mon;

    // zeng: 当前线程state设置为WAITING
    self->state = WAITING;

    if (self->interrupted)  // zeng: 如果本线程被interrupt了
        interrupted = TRUE;
    else {

        wait_loop:
        if (timed) {
            if (pthread_cond_timedwait(&mon->cv, &mon->lock, &ts) == ETIMEDOUT) // zeng: 条件变量未触发,但是超时了线程恢复运行(也会获得互斥锁)
                goto out;
        } else
            pthread_cond_wait(&mon->cv, &mon->lock);    // zeng: 等待条件满足被唤醒

        /* see why we were signalled... */

        if (self->interrupting) {   // zeng: 线程是因为被interrupt被唤醒的
            interrupted = TRUE;

            self->interrupting = FALSE;

            mon->interrupting--;    // zeng: 还未处理interrupt的线程数-1
        } else if (mon->notifying)  // zeng:线程是因为条件满足被唤醒的
            mon->notifying--;   // zeng: 还未处理notify的线程数-1
        else
            goto wait_loop;
    }
    out:

    // zeng: 线程状态设为RUNNING
    self->state = RUNNING;
    // zeng: 当前线程在等待哪个monitor
    self->wait_mon = 0;

    // zeng: 当前线程持有该monitor结构体
    mon->owner = self;
    // zeng: 恢复wait之前的重入数
    mon->count = old_count;
    // zeng: waiting等待队列线程数-1
    mon->waiting--;

    // zeng: 允许被暂停
    enableSuspend(self);

    // zeng: 线程被interrupt了
    if (interrupted) {
        self->interrupted = FALSE;

        // zeng: 抛出异常
        signalException("java/lang/InterruptedException", NULL);
    }

    return TRUE;
}

// zeng: 唤醒在wait等待队列上的一个线程
int monitorNotify(Monitor *mon, Thread *self) {
    // zeng: 不是monitor的持有者, 不能发起notify
    if (mon->owner != self)
        return FALSE;

    if ((mon->notifying + mon->interrupting) < mon->waiting) {
        mon->notifying++;   // zeng:  还未处理notify的线程数+1
        pthread_cond_signal(&mon->cv);  // zeng: 唤醒条件变量等待队列上的一个线程
    }

    return TRUE;
}

// zeng: 唤醒在wait等待队列上的所有线程
int monitorNotifyAll(Monitor *mon, Thread *self) {
    // zeng: 不是monitor的持有者, 不能发起notify
    if (mon->owner != self)
        return FALSE;

    // zeng: 还未处理notify的线程数
    mon->notifying = mon->waiting - mon->interrupting;
    // zeng: 唤醒条件变量等待队列上的所有线程
    pthread_cond_broadcast(&mon->cv);

    return TRUE;
}

Monitor *allocMonitor(Object *obj) {
    Monitor *mon;

    if (mon_free_list != NULL) {    // zeng: 从mon_free_list队列头部摘下一个
        mon = mon_free_list;
        mon_free_list = mon->next;
    } else {
        // zeng: 分配monitor结构体空间
        mon = (Monitor *) malloc(sizeof(Monitor));
        // zeng: 初始化monitor
        monitorInit(mon);
        // zeng: 表示该monitor结构体在使用中
        mon->in_use = TRUE;
    }

    return mon;
}

Monitor *findMonitor(Object *obj) {
    // zeng: lockword
    int lockword = obj->lock;

    if (lockword & SHAPE_BIT)   // zeng: lockword已经是重量锁
        return (Monitor *) (lockword & ~SHAPE_BIT); // zeng: monitor对象地址
    else {  // zeng: 如果lockword不是重量锁, 那么查找(如果没有就创建一个)monitor对象返回
        Monitor *mon;
        // zeng: 通过obj来查找monitor对象(找不到就创建一个)
        findHashEntry(mon_cache, obj, mon, TRUE, TRUE);
        return mon;
    }
}

// zeng: 锁膨胀, 即设置对象的锁为重量锁
void inflate(Object *obj, Monitor *mon, Thread *self) {
    TRACE(("Inflating obj 0x%x...\n", obj));

    // zeng: 对象的锁已经设为重量锁了, 也就没有线程在等待轻量锁释放
    clear_flc_bit(obj);

    // zeng: 唤醒在wait等待队列上的所有线程
    monitorNotifyAll(mon, self);

    // zeng:  lockword设置为fat mode format
    obj->lock = (int) mon | SHAPE_BIT;
}

// zeng: 竞争 obj对象 的锁
void objectLock(Object *obj) {
    Thread *self = threadSelf();
    // zeng: thread id 左移TID_SHIFT 位 作为 thin lock 的lockword
    unsigned int thin_locked = self->id << TID_SHIFT;
    Monitor *mon;

    TRACE(("Lock on obj 0x%x...\n", obj));

    // zeng: 如果obj->lock原来的值为0, 表示没有人持有这个对象的锁, 那么将obj->lock置为thin_locked, 表示上锁
    if (COMPARE_AND_SWAP(&obj->lock, 0, thin_locked))
        return; // zeng: 上轻量锁成功 直接返回

    // zeng: 如果之前轻量锁已经被本线程持有
    if ((obj->lock & (TID_MASK | SHAPE_BIT)) == thin_locked) {
        // zeng: 重入次数
        int count = obj->lock & COUNT_MASK;

        if (count < (((1 << COUNT_SIZE) - 1) << COUNT_SHIFT))   // zeng: 重入次数小于255
            obj->lock += 1 << COUNT_SHIFT;  // zeng: 重入次数+1
        else {  // zeng: 重入次数大于等于255, 升级为重量锁
            // zeng: monitor对象
            mon = findMonitor(obj);
            // zeng: 本线程竞争成为monitor对象的持有者
            monitorLock(mon, self);
            // zeng: 即设置对象的锁为重量锁mon
            inflate(obj, mon, self);
            // zeng: 重入次数设为256
            mon->count = 1 << COUNT_SIZE;
        }

        return;
    }

    // zeng: 如果有其他线程持有轻量锁

    mon = findMonitor(obj);
    // zeng: 竞争monitor对象
    monitorLock(mon, self);

    while ((obj->lock & SHAPE_BIT) == 0) {  // zeng: 如果是轻量锁
        // zeng: 有线程在等待轻量锁释放
        set_flc_bit(obj);

        // zeng: 如果当前锁类型是轻量锁, 持有monitor对象并不能表示持有锁, 只是表示这个线程从争抢锁的等待队列中出列, 尝试看当前能否获取锁(等到轻量锁释放这个尝试才能成功)

        if (COMPARE_AND_SWAP(&obj->lock, 0, self))  // zeng: 没有其他线程持有轻量锁, 先获取轻量锁
            // zeng: 替换对象的锁为重量锁mon
            inflate(obj, mon, self);
        else
            // zeng: 线程进行wait等待队列, 直到条件满足被唤醒
            monitorWait(mon, self, 0, 0);
    }
}

// zeng: 释放 obj对象 的锁
void objectUnlock(Object *obj) {
    Thread *self = threadSelf();

    // zeng: thin mode format lorkword
    unsigned int thin_locked = self->id << TID_SHIFT;

    TRACE(("Unlock on obj 0x%x...\n", obj));

    if (obj->lock == thin_locked) { // zeng: 如果是轻量锁且没有重入
        obj->lock = 0;  // zeng: lock置为0

        retry:
        if (test_flc_bit(obj)) {    // zeng: 有线程在等待轻量锁释放
            Monitor *mon = findMonitor(obj);

            // zeng: 竞争monitor
            if (!monitorTryLock(mon, self)) {
                // zeng: 当前线程放弃cpu, 重新进入调度队列
                pthread_yield();
                goto retry;
            }

            if (test_flc_bit(obj))
                monitorNotify(mon, self);   // zeng: 唤醒等待的线程

            // zeng: 释放monitor
            monitorUnlock(mon, self);
        }
    } else {
        if ((obj->lock & (TID_MASK | SHAPE_BIT)) == thin_locked)    // zeng: 如果是轻量锁
            obj->lock -= 1 << COUNT_SHIFT;  // zeng: 重入次数-1
        else if ((obj->lock & SHAPE_BIT) != 0) {    // zeng: 重量锁
            // zeng: monitor结构体
            Monitor *mon = (Monitor *) (obj->lock & ~SHAPE_BIT);

            // zeng: 如果重入次数为0, 且enter等待队列 waiting等待队列 都没有线程在等待
            if ((mon->count == 0) && (mon->entering == 0) && (mon->waiting == 0)) {
                TRACE(("Deflating obj 0x%x...\n", obj));

                // zeng: lock置0
                obj->lock = 0;
                // zeng: 该monitor结构体不在使用中
                mon->in_use = FALSE;
            }

            // zeng: 退出持有 monitor结构体
            monitorUnlock(mon, self);
        }
    }
}

// zeng: 线程进行wait等待队列, 直到条件满足被唤醒或者被interrupt
void objectWait(Object *obj, long long ms, int ns) {
    Thread *self = threadSelf();
    // zeng: lockword
    int lockword = obj->lock;

    Monitor *mon;

    TRACE(("Wait on obj 0x%x...\n", obj));

    if ((lockword & SHAPE_BIT) == 0) {  // zeng: 轻量锁
        // zeng: thread id
        int tid = (lockword & TID_MASK) >> TID_SHIFT;

        if (tid == self->id) {  // zeng: 当前线程持有轻量锁
            // zeng: 升级为重量锁

            mon = findMonitor(obj);
            monitorLock(mon, self);
            inflate(obj, mon, self);
            mon->count = (lockword & COUNT_MASK) >> COUNT_SHIFT;
        } else
            goto not_owner;
    } else
        // zeng: 获取monitor结构体
        mon = (Monitor *) (lockword & ~SHAPE_BIT);

    // zeng: 线程进行wait等待队列, 直到条件满足被唤醒或者被interrupt
    if (monitorWait(mon, self, ms, ns))
        return;

    not_owner:
    // zeng: 抛出异常
    signalException("java/lang/IllegalMonitorStateException", "thread not owner");
}

// zeng: 唤醒在wait等待队列上的一个线程
void objectNotify(Object *obj) {
    Thread *self = threadSelf();
    int lockword = obj->lock;

    TRACE(("Notify on obj 0x%x...\n", obj));

    if ((lockword & SHAPE_BIT) == 0) {  // zeng: 如果是轻量锁, 不存在等待, 也就不存在唤醒
        int tid = (lockword & TID_MASK) >> TID_SHIFT;
        if (tid == self->id)
            return;
    } else {
        Monitor *mon = (Monitor *) (lockword & ~SHAPE_BIT);

        // zeng: 唤醒在wait等待队列上的一个线程
        if (monitorNotify(mon, self))
            return;
    }

    // zeng: 抛出异常
    signalException("java/lang/IllegalMonitorStateException", "thread not owner");
}

// zeng: 唤醒在wait等待队列上的所有线程
void objectNotifyAll(Object *obj) {
    Thread *self = threadSelf();

    // zeng: lockword
    int lockword = obj->lock;

    TRACE(("NotifyAll on obj 0x%x...\n", obj));

    if ((lockword & SHAPE_BIT) == 0) {  // zeng: 如果是轻量锁, 不存在等待, 也就不存在唤醒
        int tid = (lockword & TID_MASK) >> TID_SHIFT;
        if (tid == self->id)
            return;
    } else {
        Monitor *mon = (Monitor *) (lockword & ~SHAPE_BIT);

        // zeng: 唤醒在wait等待队列上的所有线程
        if (monitorNotifyAll(mon, self))
            return;
    }

    // zeng: 抛出异常
    signalException("java/lang/IllegalMonitorStateException", "thread not owner");
}

void initialiseMonitor() {
    // zeng: monitor 哈希表
    initHashTable(mon_cache, HASHTABSZE);
}

