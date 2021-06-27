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
#include <signal.h>

#include "jam.h"
#include "thread.h"
#include "lock.h"

#ifdef TRACETHREAD
#define TRACE(x) printf x
#else
#define TRACE(x)
#endif

static int java_stack_size;

/* Thread create/destroy lock and condvar */
static pthread_mutex_t lock;
static pthread_cond_t cv;

/* lock and condvar used by main thread to wait for
 * all non-daemon threads to die */
static pthread_mutex_t exit_lock;
static pthread_cond_t exit_cv;

/* Monitor for sleeping threads to do a timed-wait against */
static Monitor sleep_mon;

/* Thread specific key holding thread's Thread pntr */
static pthread_key_t threadKey;

/* Attributes for spawned threads */
static pthread_attr_t attributes;

/* The main thread info - head of the thread list */
static Thread main, dead_thread;

/* Main thread ExecEnv */
static ExecEnv main_ee;

/* Various field offsets into java.lang.Thread -
 * cached at startup and used in thread creation */
static int vmData_offset;
static int daemon_offset;
static int group_offset;
static int priority_offset;
static int name_offset;

/* Method table indexes of Thread.run method and
 * ThreadGroup.removeThread - cached at startup */
static int run_mtbl_idx;
static int rmveThrd_mtbl_idx;

/* Cached java.lang.Thread class */
static Class *thread_class;

/* Count of non-daemon threads still running in VM */
static int non_daemon_thrds = 0;

/* Bitmap - used for generating unique thread ID's */
#define MAP_INC 32
static unsigned int *tidBitmap;
static int tidBitmapSize = 0;

/* Mark a threadID value as no longer used */
#define freeThreadID(n) tidBitmap[n>>5] &= ~(1<<(n&0x1f))

/* Generate a new thread ID - assumes the thread queue
 * lock is held */

// zeng: 产生jvm内唯一id 作为java线程的id
static int genThreadID() {
    int i = 0;

    retry:
    for (; i < tidBitmapSize; i++) {
        if (tidBitmap[i] != 0xffffffff) {
            int n = ffs(~tidBitmap[i]);
            tidBitmap[i] |= 1 << (n - 1);
            return (i << 5) + n;
        }
    }

    tidBitmap = (unsigned int *) realloc(tidBitmap, (tidBitmapSize + MAP_INC) * sizeof(unsigned int));
    memset(tidBitmap + tidBitmapSize, 0, MAP_INC * sizeof(unsigned int));
    tidBitmapSize += MAP_INC;
    goto retry;
}

// zeng: 线程是否还存活
int threadIsAlive(Thread *thread) {
    return thread->state != 0;
}

// zeng: 线程是否被interrupt, 并清除interrupt状态
int threadInterrupted(Thread *thread) {
    int r = thread->interrupted;

    thread->interrupted = FALSE;

    return r;
}

// zeng: 线程是否被interrupt
int threadIsInterrupted(Thread *thread) {
    return thread->interrupted;
}

// zeng: 线程暂停指定时间
void threadSleep(Thread *thread, long long ms, int ns) {
    // zeng: 竞争sleep_mon
    monitorLock(&sleep_mon, thread);

    // zeng: 线程进行wait等待队列, 直到超时被唤醒或者被interrupt
    monitorWait(&sleep_mon, thread, ms, ns);

    // zeng: 释放sleep_mon
    monitorUnlock(&sleep_mon, thread);
}

// zeng: 当前线程让出cpu, 重新进入调度队列
void threadYield(Thread *thread) {
    pthread_yield();
}

// zeng: 中断`线程的暂停`
void threadInterrupt(Thread *thread) {
    // zeng: 获取线程等待的monitor
    Monitor *mon = thread->wait_mon;

    // zeng: interrupted设为TRUE
    thread->interrupted = TRUE;

    // zeng: 如果没有等待的monitor, 则什么都不做
    if (mon) {
        Thread *self = threadSelf();

        char owner = (mon->owner == self);

        if (!owner) {   // zeng: 该线程不持有该monitor
            int i;

            /* Another thread may be holding the monitor -
             * if we can't get it after a couple attempts give-up
             * to avoid deadlock */
            // zeng: 尝试持有该monitor
            for (i = 0; i < 5; i++) {

                if (!pthread_mutex_trylock(&mon->lock))
                    goto got_lock;  // zeng: 成功持有

                pthread_yield();

                if (thread->wait_mon != mon)
                    return;
            }

            return;
        }

        got_lock:

        if ((thread->wait_mon == mon) && thread->interrupted && !thread->interrupting && ((mon->notifying + mon->interrupting) < mon->waiting)) {
            // zeng: interrupting设为TRUE
            thread->interrupting = TRUE;
            // zeng: 还未处理interrupt的线程数+1
            mon->interrupting++;
            // zeng: 唤醒在该monitor的waiting等待队列上的所有线程(因为我们没有办法指定这个要中断的线程来唤醒)
            pthread_cond_broadcast(&mon->cv);
        }

        // zeng: 释放上面获得的互斥锁
        if (!owner)
            pthread_mutex_unlock(&mon->lock);

    }
}

// zeng: TODO
void *getStackTop(Thread *thread) {
    return thread->stack_top;
}

// zeng: TODO
void *getStackBase(Thread *thread) {
    return thread->stack_base;
}

// zeng: 获得java thread对象对应的thread结构体
Thread *threadSelf0(Object *jThread) {
    return (Thread *) (INST_DATA(jThread)[vmData_offset]);
}

// zeng: 获取当前线程的thread结构体
Thread *threadSelf() {
    return (Thread *) pthread_getspecific(threadKey);
}

// zeng: 将当前线程的thread结构体设置进threadKey线程变量中
void setThreadSelf(Thread *thread) {
    pthread_setspecific(threadKey, thread);
}

ExecEnv *getExecEnv() {
    return threadSelf()->ee;
}

// zeng: 通常由main方法 和 线程start方法 调用, 用来初始化线程执行上下文(主要好是分配线程的栈空间)
void initialiseJavaStack(ExecEnv *ee) {
    // zeng: 用malloc分配栈空间, 返回空间开始地址
    char *stack = malloc(java_stack_size);
    // zeng: 在栈空间里分配一个MethodBlock
    MethodBlock *mb = (MethodBlock *) stack;

    // zeng: 没有本地变量数组

    // zeng: 接下来的地址分配线程最顶层方法(c方法)的stack frame.
    Frame *top = (Frame *) (mb + 1);

    // zeng: c方法不需要操作数栈
    mb->max_stack = 0;

    // zeng: 设置c方法 stack frame中的MethodBlock
    top->mb = mb;

    // zeng: frame结构接下来的栈地址赋值给ostack 也就是frame结构中只保存ostack地址 ostack空间在栈空间里frame结构接下来的地址下分配
    // zeng: top方法(c方法)栈帧操作数栈地址. 由于max_stack为0, 所以实际上这个栈帧是没有操作栈空间的.
    top->ostack = (u4 *) (top + 1);

    top->prev = 0;

    // zeng: 设置执行上下文中的栈开始地址
    ee->stack = stack;
    // zeng: 置为 最近的stack frame
    ee->last_frame = top;
    // zeng: 设置执行上下文中的栈结束地址
    ee->stack_end = stack + java_stack_size - 1024;
}

// zeng: 开启线程
void *threadStart(void *arg) {
    // zeng: 线程结构体
    Thread *thread = (Thread *) arg;

    // zeng: 线程执行上下文
    ExecEnv *ee = thread->ee;
    // zeng: java线程对象
    Object *jThread = ee->thread;

    ClassBlock *cb = CLASS_CB(jThread->class);
    // zeng: 获取run方法
    MethodBlock *run = cb->method_table[run_mtbl_idx];

    Object *group, *excep;

    TRACE(("Thread 0x%x id: %d started\n", thread, thread->id));

    // zeng: 用来初始化线程执行上下文(主要好是分配线程的栈空间)
    initialiseJavaStack(ee);
    // zeng:  将线程结构体设置入线程私有变量中
    setThreadSelf(thread);

    /* Need to disable suspension as we'll most likely
     * be waiting on lock when we're added to the thread
     * list, and now liable for suspension */

    // zeng: TODO
    thread->stack_base = &group;
    disableSuspend0(thread, &group);

    // zeng: 互斥锁
    pthread_mutex_lock(&lock);

    // zeng:  生成jvm中线程唯一id
    thread->id = genThreadID();

    // zeng: 设置为start
    thread->state = STARTED;

    // zeng: 唤醒等待在条件变量上的所有线程
    pthread_cond_broadcast(&cv);

    // zeng: 等待thread_state变为RUNNING
    while (thread->state != RUNNING)
        pthread_cond_wait(&cv, &lock);

    // zeng: 解锁
    pthread_mutex_unlock(&lock);

    /* Execute the thread's run() method... */
    // zeng: 允许被被暂停
    enableSuspend(thread);
    // zeng: 执行thead对象的run方法
    executeMethod(jThread, run);

    // zeng: 下面就是执行完run方法,线程结束的清理工作了

    /* Call thread group's uncaughtException if exception
     * is of type java.lang.Throwable */

    // zeng: 获得thread对象的group字段值
    group = (Object *) INST_DATA(jThread)[group_offset];

    if (excep = exceptionOccured()) {   // zeng: 发生异常
        Class *throwable;
        MethodBlock *uncaught_exp;

        clearException();

        throwable = findSystemClass0("java/lang/Throwable");

        if (throwable && isInstanceOf(throwable, excep->class)
            && (uncaught_exp = lookupMethod(group->class, "uncaughtException",
                                            "(Ljava/lang/Thread;Ljava/lang/Throwable;)V")))
            // zeng: 执行 ThreadGroup 的 uncaughtException 方法
            executeMethod(group, uncaught_exp, jThread, excep);
        else {
            setException(excep);
            printException();
        }
    }

    /* remove thread from thread group */
    // zeng: 执行ThreadGroup的removeThread方法
    executeMethod(group, (CLASS_CB(group->class))->method_table[rmveThrd_mtbl_idx], jThread);

    // zeng: 上锁才能notify
    objectLock(jThread);

    // zeng: 线程执行完了, 需要唤醒thread对象wait等待队列上的所有线程
    objectNotifyAll(jThread);

    // zeng: state不再存活
    thread->state = 0;

    // zeng: 解锁
    objectUnlock(jThread);

    // zeng: 禁止线程被暂停
    disableSuspend0(thread, &group)

    // zeng; 互斥锁
    pthread_mutex_lock(&lock);

    /* remove from thread list... */

    // zeng: 从线程队列中移除
    if ((thread->prev->next = thread->next))
        thread->next->prev = thread->prev;

    // zeng: daemon线程
    if (!INST_DATA(jThread)[daemon_offset])
        non_daemon_thrds--;

    // zeng: 归还唯一id
    freeThreadID(thread->id);

    // zeng: 释放锁
    pthread_mutex_unlock(&lock);

    // zeng: 允许被暂停
    enableSuspend(thread);

    // zeng: 设置thread结构体为dead_thread
    INST_DATA(jThread)[vmData_offset] = (u4) &dead_thread;

    free(thread);
    free(ee->stack);
    free(ee);

    // zeng: 当前没有non_daemon线程
    if (non_daemon_thrds == 0) {
        /* No need to bother with disabling suspension
	 * around lock, as we're no longer on thread list */

        // zeng: exit_lock互斥锁
        pthread_mutex_lock(&exit_lock);

        // zeng: 唤醒等待在exit_cv的线程
        pthread_cond_signal(&exit_cv);

        // zeng: 释放锁
        pthread_mutex_unlock(&exit_lock);
    }

    TRACE(("Thread 0x%x id: %d exited\n", thread, thread->id));
}

// zeng: 创建java线程对象对应的c线程
void createJavaThread(Object *jThread) {
    ExecEnv *ee;
    Thread *thread;

    // zeng: 当前线程
    Thread *self = threadSelf();

    // zeng: 不允许被暂停
    disableSuspend(self);

    // zeng: 互斥锁
    pthread_mutex_lock(&lock);

    // zeng: 如果已经有c thread结构体
    if (INST_DATA(jThread)[vmData_offset]) {
        // zeng: 解锁
        pthread_mutex_unlock(&lock);

        // zeng: 允许被暂停
        enableSuspend(self);

        // zeng: 抛出异常
        signalException("java/lang/IllegalThreadStateException", "thread already started");

        return;
    }

    // zeng: 分配线程执行上下文对象结构体
    ee = (ExecEnv *) malloc(sizeof(ExecEnv));
    // zeng: 分配thread结构体
    thread = (Thread *) malloc(sizeof(Thread));
    // zeng: 置0
    memset(ee, 0, sizeof(ExecEnv));
    // zeng: 置0
    memset(thread, 0, sizeof(Thread));

    // zeng: 线程执行上下文
    thread->ee = ee;
    // zeng: java线程对象
    ee->thread = jThread;

    // zeng: 设置vmData字段
    INST_DATA(jThread)[vmData_offset] = (u4) thread;

    // zeng: 释放锁
    pthread_mutex_unlock(&lock);

    // zeng: 创建一个c线程, 用来执行threadStart,传参为thread结构体, 创建的c线程tid设置进thread->tid
    if (pthread_create(&thread->tid, &attributes, threadStart, thread)) {   // zeng: 创建失败
        INST_DATA(jThread)[vmData_offset] = 0;

        free(ee);
        free(thread);

        enableSuspend(self);

        // zeng: 抛出异常
        signalException("java/lang/OutOfMemoryError", "can't create thread");

        return;
    }

    // zeng: 互斥锁
    pthread_mutex_lock(&lock);

    // zeng: 等待threadStart中设置thread->state为STARTED
    while (thread->state != STARTED)
        pthread_cond_wait(&cv, &lock);

    /* add to thread list... */

    // zeng: 插入线程队列中main之后的位置
    if ((thread->next = main.next))
        main.next->prev = thread;
    thread->prev = &main;
    main.next = thread;

    // zeng: 如果不是daemon线程
    if (!INST_DATA(jThread)[daemon_offset])
        non_daemon_thrds++;

    // zeng: 设置thread->state为RUNNING
    thread->state = RUNNING;

    // zeng: 唤醒等待在条件变量上的所有线程
    pthread_cond_broadcast(&cv);

    // zeng: 解锁
    pthread_mutex_unlock(&lock);

    // zeng: 允许被暂停
    enableSuspend(self);
}

Thread *attachThread(char *name, char is_daemon, void *stack_base) {
    ExecEnv *ee;
    Thread *thread;

    ee = (ExecEnv *) malloc(sizeof(ExecEnv));
    thread = (Thread *) malloc(sizeof(Thread));
    memset(ee, 0, sizeof(ExecEnv));
    memset(thread, 0, sizeof(Thread));

    thread->tid = pthread_self();
    thread->state = RUNNING;
    thread->stack_base = stack_base;
    thread->ee = ee;

    initialiseJavaStack(ee);
    setThreadSelf(thread);

    ee->thread = allocObject(thread_class);

    INST_DATA(ee->thread)[daemon_offset] = FALSE;
    INST_DATA(ee->thread)[name_offset] = (u4) Cstr2String(name);
    INST_DATA(ee->thread)[group_offset] = INST_DATA(main_ee.thread)[group_offset];
    INST_DATA(ee->thread)[priority_offset] = 5;
    INST_DATA(ee->thread)[vmData_offset] = (u4) thread;

    /* add to thread list... */

    pthread_mutex_lock(&lock);
    if ((thread->next = main.next))
        main.next->prev = thread;
    thread->prev = &main;
    main.next = thread;

    if (!is_daemon)
        non_daemon_thrds++;

    thread->id = genThreadID();
    pthread_mutex_unlock(&lock);

    TRACE(("Thread 0x%x id: %d attached\n", thread, thread->id));
    return thread;
}

static void *shell(void *args) {
    void *start = ((void **) args)[1];
    Thread *self = attachThread(((char **) args)[0], TRUE, &self);

    free(args);
    (*(void (*)(Thread *)) start)(self);
}

void createVMThread(char *name, void (*start)(Thread *)) {
    void **args = malloc(2 * sizeof(void *));
    pthread_t tid;

    args[0] = name;
    args[1] = start;
    pthread_create(&tid, &attributes, shell, args);
}

// zeng: 等待所有non_daemon线程退出
void mainThreadWaitToExitVM() {
    Thread *self = threadSelf();

    TRACE(("Waiting for %d non-daemon threads to exit\n", non_daemon_thrds));

    // zeng: 不允许被暂停
    disableSuspend(self);

    // zeng: exit_lock互斥锁
    pthread_mutex_lock(&exit_lock);

    // zeng: 线程state设为WAITING
    self->state = WAITING;

    // zeng: 等待所有non_daemon线程退出
    while (non_daemon_thrds)
        pthread_cond_wait(&exit_cv, &exit_lock);

    // zeng: 解锁
    pthread_mutex_unlock(&exit_lock);

    // zeng: 允许被暂停
    enableSuspend(self);
}

// zeng: 暂停所有线程, 除了当前线程
void suspendAllThreads(Thread *self) {
    Thread *thread;

    TRACE(("Thread 0x%x id: %d is suspending all threads\n", self, self->id));

    // zeng; lock互斥锁
    pthread_mutex_lock(&lock);


    for (thread = &main; thread != NULL; thread = thread->next) {
        // zeng: 当前线程
        if (thread == self)
            continue;

        // zeng: suspend设为TRUE
        thread->suspend = TRUE;

        // zeng: 如果该线程没有被禁止暂停
        if (!thread->blocking)
            // zeng: 发送SIGUSR1信号
            pthread_kill(thread->tid, SIGUSR1);
    }

    for (thread = &main; thread != NULL; thread = thread->next) {
        if (thread == self)
            continue;
        while (!thread->blocking && thread->state != SUSPENDED)
            pthread_yield();
    }

    TRACE(("All threads suspended...\n"));
    pthread_mutex_unlock(&lock);
}

// zeng: 唤醒所有线程
void resumeAllThreads(Thread *self) {
    Thread *thread;

    TRACE(("Thread 0x%x id: %d is resuming all threads\n", self, self->id));

    // zeng: lock互斥锁
    pthread_mutex_lock(&lock);

    for (thread = &main; thread != NULL; thread = thread->next) {
        // zeng: 当前线程
        if (thread == self)
            continue;

        // zeng: suspend设为FALSE
        thread->suspend = FALSE;

        // zeng: 对于允许被暂停的线程, 发送SIGUSR1信号. 监听函数收到信号, 会恢复线程暂停前的状态.
        if (!thread->blocking)
            pthread_kill(thread->tid, SIGUSR1);
    }

    // zeng: 等待所有其他线程恢复状态
    for (thread = &main; thread != NULL; thread = thread->next) {
        while (thread->state == SUSPENDED)  // zeng: 该线程还未恢复状态
            pthread_yield();    // zeng: 当前线程让出cpu, 重新进入调度队列
    }

    TRACE(("All threads resumed...\n"));

    // zeng: 释放锁
    pthread_mutex_unlock(&lock);
}

// zeng: 暂停当前线程
static void suspendLoop(Thread *thread) {
    // zeng: 暂停前的state
    char old_state = thread->state;

    sigset_t mask;
    sigjmp_buf env;

    // zeng: TODO
    sigsetjmp(env, FALSE);

    // zeng: TODO
    thread->stack_top = &env;

    // zeng: state设置为SUSPENDED
    thread->state = SUSPENDED;

    sigfillset(&mask);
    // zeng: 不屏蔽SIGUSR1
    sigdelset(&mask, SIGUSR1);
    // zeng: 不屏蔽SIGTERM
    sigdelset(&mask, SIGTERM);

    // zeng: suspend为true的时候, 暂停当前线程
    while (thread->suspend)
        // zeng: 线程睡眠 等待SIGTERM SIGUSR1等信号唤醒
        sigsuspend(&mask);

    // zeng: 执行到此处, 线程已恢复执行

    // zeng: 恢复state
    thread->state = old_state;
}

// zeng: SIGUSR1信号 处理函数
static void suspendHandler(int sig) {
    Thread *thread = threadSelf();
    suspendLoop(thread);
}

// zeng: 禁止线程被暂停
void disableSuspend0(Thread *thread, void *stack_top) {
    sigset_t mask;

    // zeng: 屏蔽SIGUSR1信号
    sigemptyset(&mask);
    sigaddset(&mask, SIGUSR1);
    pthread_sigmask(SIG_BLOCK, &mask, NULL);

    // zeng:TODO
    thread->stack_top = stack_top;

    // zeng: blocking设为TRUE
    thread->blocking = TRUE;
}

// zeng: 允许新城被暂停
void enableSuspend(Thread *thread) {
    sigset_t mask;

    sigemptyset(&mask);

    // zeng: blocking设为FALSE
    thread->blocking = FALSE;

    // zeng: 如果线程的suspend之前被设为TRUE, 那么让该线程被咱暂停
    if (thread->suspend)
        suspendLoop(thread);

    // zeng: 不屏蔽SIGUSR1信号
    sigaddset(&mask, SIGUSR1);

    pthread_sigmask(SIG_UNBLOCK, &mask, NULL);
}

// zeng: 循环打印所有线程的信息
void *dumpThreadsLoop(void *arg) {
    Thread *thread, dummy;
    sigset_t mask;
    int sig;

    sigemptyset(&mask);
    sigaddset(&mask, SIGQUIT);
    sigaddset(&mask, SIGINT);

    for (;;) {
        // zeng: 等待信号
        sigwait(&mask, &sig);

        // zeng: 收到SIGINT时退出
        if (sig == SIGINT)
            exit(0);

        // zeng: 收到SIGQUIT时循环打印线程信息
        suspendAllThreads(&dummy);
        printf("Thread Dump\n-----------\n\n");
        for (thread = &main; thread != NULL; thread = thread->next) {
            char *name = String2Cstr((Object *) (INST_DATA(thread->ee->thread)[name_offset]));
            printf("Thread: %s 0x%x tid: %d state: %d\n", name, thread, thread->tid, thread->state);
            free(name);
        }
        resumeAllThreads(&dummy);
    }
}

// zeng: 线程接收信号相关设置
static void initialiseSignals() {
    struct sigaction act;
    sigset_t mask;
    pthread_t tid;

    // zeng: 监听SIGUSR1信号
    act.sa_handler = suspendHandler;
    sigemptyset(&act.sa_mask);
    act.sa_flags = 0;
    sigaction(SIGUSR1, &act, NULL);

    // zeng: 忽略SIGQUIT SIGINT信号
    sigemptyset(&mask);
    sigaddset(&mask, SIGQUIT);
    sigaddset(&mask, SIGINT);
    sigprocmask(SIG_BLOCK, &mask, NULL);

    // zeng: 开启一个线程 循环监听信号来打印所有 java thread 的信息
    pthread_create(&tid, &attributes, dumpThreadsLoop, NULL);
}

/* garbage collection support */

extern void scanThread(Thread *thread);

// zeng: 每个线程都调用scanThread方法
void scanThreads() {
    Thread *thread;

    for (thread = &main; thread != NULL; thread = thread->next)
        scanThread(thread);
}

// zeng: 是否存在线程是WAITING SUSPENDED状态
int systemIdle(Thread *self) {
    Thread *thread;

    for (thread = &main; thread != NULL; thread = thread->next)
        if (thread != self && thread->state < WAITING)
            return FALSE;

    return TRUE;
}

void initialiseMainThread(int stack_size) {
    Class *thrdGrp_class;
    FieldBlock *vmData;
    MethodBlock *run, *remove_thread, uncaught_exp;
    FieldBlock *daemon, *name, *group, *priority, *root;

    java_stack_size = stack_size;

    // zeng: 分配一个thread-specific data area中的空间, 用threadKey标识, threadKey + tid唯一标识一个value(pthread_getspecific的参数只有threadKey, 猜测pthread_getspecific里会取得当前线程的tid, 组成唯一标识)
    pthread_key_create(&threadKey, NULL);

    // zeng: 初始化互斥锁lock
    pthread_mutex_init(&lock, NULL);
    // zeng: 初始化条件变量cv
    pthread_cond_init(&cv, NULL);

    // zeng: 初始化互斥锁exit_lock
    pthread_mutex_init(&exit_lock, NULL);
    // zeng: 初始化条件变量exit_cv
    pthread_cond_init(&exit_cv, NULL);
    // zeng: 初始化 sleep_mon 这个monitor结构体
    monitorInit(&sleep_mon);

    // zeng: 设置线程属性配置
    pthread_attr_init(&attributes);
    pthread_attr_setdetachstate(&attributes, PTHREAD_CREATE_DETACHED);

    // zeng: TODO
    main.stack_base = &thrdGrp_class;

    // zeng: linux task -> pid
    main.tid = pthread_self();
    // zeng: 生成jvm中唯一id
    main.id = genThreadID();
    main.state = RUNNING;
    // zeng: 线程执行上下文
    main.ee = &main_ee;
    // zeng: 初始化线程栈,并设置入执行上下文中
    initialiseJavaStack(&main_ee);
    // zeng: 将main thread struct地址存入thread-specific data area 中
    setThreadSelf(&main);

    // zeng: 加载 链接 Thread类
    /* As we're initialising, VM will abort if Thread can't be found */
    thread_class = findSystemClass0("java/lang/Thread");

    // zeng: Thread对象中的字段
    vmData = findField(thread_class, "vmData", "I");
    daemon = findField(thread_class, "daemon", "Z");
    name = findField(thread_class, "name", "Ljava/lang/String;");
    group = findField(thread_class, "group", "Ljava/lang/ThreadGroup;");
    priority = findField(thread_class, "priority", "I");

    run = findMethod(thread_class, "run", "()V");

    /* findField and findMethod do not throw an exception... */
    if ((vmData == NULL) || (run == NULL) || (daemon == NULL) || (name == NULL) ||
        (group == NULL) || (priority == NULL))
        goto error;

    // zeng: 字段在对象内容体中的偏移量
    vmData_offset = vmData->offset;
    daemon_offset = daemon->offset;
    group_offset = group->offset;
    priority_offset = priority->offset;
    name_offset = name->offset;
    run_mtbl_idx = run->method_table_index;

    // zeng: 设置java thread对象
    main_ee.thread = allocObject(thread_class);

    thrdGrp_class = findSystemClass("java/lang/ThreadGroup");
    if (exceptionOccured()) {
        printException();
        exit(1);
    }

    root = findField(thrdGrp_class, "root", "Ljava/lang/ThreadGroup;");
    remove_thread = findMethod(thrdGrp_class, "removeThread", "(Ljava/lang/Thread;)V");

    /* findField and findMethod do not throw an exception... */
    if ((root == NULL) || (remove_thread == NULL))
        goto error;

    rmveThrd_mtbl_idx = remove_thread->method_table_index;

    INST_DATA(main_ee.thread)[daemon_offset] = FALSE;
    INST_DATA(main_ee.thread)[name_offset] = (u4) Cstr2String("main");
    INST_DATA(main_ee.thread)[group_offset] = root->static_value;
    INST_DATA(main_ee.thread)[priority_offset] = 5;

    INST_DATA(main_ee.thread)[vmData_offset] = (u4) &main;

    // zeng: 初始化signal相关 用于java层面线程的实现(例如suspend的实现)
    initialiseSignals();

    return;

    error:
    printf("Error initialising VM (initialiseMainThread)\n");
    exit(0);
}

