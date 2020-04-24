#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

int getlev(void);
void priority_boost(void);
int set_cpu_share(int percent);
void reset_distance(void);

// Dohyun, this structure is needed to find high priority in ptable 
// Dohyun, this array is needed to exec specification
int time_quantum[3] = {1, 2, 4};
int time_allotment[2] = {5, 10};
// for MLFQ
int total_tick = 0;
// for Stride
int BIG_TICKETS = 3000;
int total_percent = 0;
// for MFLQ + Stride Scheduling
int mlfq_distance = 0;
int stride_distance = 0;

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;
  //Dohyun init
  p->priority = 0;
  p->tick = 0;
  p->percent = 0;
  p->stride = 0;
  p->distance = 0;
  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      //Dohyun
      if(p->percent > 0){
        total_percent -= p->percent;
        p->priority = 0;
        p->tick = 0;
        p->percent = 0;
        p->stride = 0;
        p->distance = 0;
      }
      //Dohyun End
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }
  if(curproc->percent > 0){
    total_percent -= curproc->percent;
    curproc->priority = 0;
    curproc->tick = 0;
    curproc->percent = 0;
    curproc->stride = 0;
    curproc->distance = 0;
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.

int 
decide_scheduler(void)
{
    if(total_percent == 0){
        //mlfq selected
        return 1;
    }
    else{
        int stride_stride = BIG_TICKETS / total_percent;
        int mlfq_stride = BIG_TICKETS / (100 - total_percent);

        // when overflow is occured, reset distance
        if(mlfq_distance < 0 || stride_distance < 0){
            mlfq_distance = 0;
            stride_distance = 0;
        }

        if(mlfq_distance < stride_distance){
            // mlfq selected
            mlfq_distance += mlfq_stride;
            return 1;
        }else{
            // stride seleceted
            stride_distance += stride_stride;
            return 0;
        }
    }
}

void
scheduler(void)
{
  struct cpu *c = mycpu();
  
  // Dohyun, this is neeeded to priority boost
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();
    if(decide_scheduler()){
        // MLFQ
        struct proc *temp_p, *p;
        int top_priority = 2;
        // Get highest Priority, in this code most "lower priority number" means  higher than other.
        acquire(&ptable.lock);
        for(temp_p = ptable.proc; temp_p < &ptable.proc[NPROC]; temp_p++){
            if(temp_p->state != RUNNABLE || temp_p->stride != 0){
                continue;
            }
            if(temp_p->priority < top_priority){
                top_priority = temp_p->priority;
            }
        }
        // Find high priority process and run
        for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
            if(p->state != RUNNABLE || p->priority > top_priority || p->stride != 0){
                continue;
            }
            // exec process with diffrent time quantum
            for(int cnt=0; cnt < time_quantum[p->priority]; cnt++){
                if(p->state != RUNNABLE || p->stride != 0){
                    continue;
                }
                c->proc = p;
                switchuvm(p);
                p->state = RUNNING;
                swtch(&(c->scheduler), p->context);
                switchkvm();
                total_tick++;
                p->tick++;
                cprintf("MLFQ pid %d, p->priority %d, p->tick %d, total_tick %d\n", p->pid, p->priority, p->tick, total_tick);
                c->proc = 0;
                if(p->priority < 2 && p->tick >= time_allotment[p->priority]){
                    break;
                }
                //priority_boost
                if(total_tick >= 100){
                    priority_boost();
                }
            }
            // priority level down if process over the time quantum
            if(p->priority != 2 && p->tick >= time_allotment[p->priority]){
                p->priority++;
                p->tick = 0;
            }
        }
        release(&ptable.lock);
    }else{
        //Stride Scheudling
        int min_distance = 0;
        struct proc *temp, *p;
        acquire(&ptable.lock);
        for(temp = ptable.proc; temp < &ptable.proc[NPROC]; temp++){
            if( temp->stride != 0){
                min_distance = temp->distance;
                break;
            }
        }
        // find the min_distance 
        for(; temp < &ptable.proc[NPROC]; temp++){
            if(temp->stride != 0 && temp->distance < min_distance){
                min_distance = temp->distance;
            }
        }
        // overflow is occured, reset distance.
        if(min_distance < 0){
            reset_distance();
            min_distance = 0;
        }
        //cprintf("real min_distance %d\n", min_distance);
        // if process's distance is min_distance
        // swtch

        for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
            if(p->state == RUNNABLE && p->stride != 0 && p->distance == min_distance){
                //cprintf("min_distance %d\n", min_distance);
                //cprintf("STRIDE selected pid %d, distance: %d\n", p->pid, p->distance);
                p->distance += p->stride;
                c->proc = p;
                switchuvm(p);
                p->state = RUNNING;
                swtch(&(c->scheduler), p->context);
                switchkvm();
                c->proc = 0;
            }
        }
        release(&ptable.lock);
    }
    
    /* Dohyun, this is Original code.
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
        continue;

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    */

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

int
getppid(void)
{
    return myproc()->parent->pid;
}

int
getlev(void)
{
    return myproc()->priority;
}

void priority_boost(void){
    struct proc *temp_p;
    for(temp_p = ptable.proc; temp_p < &ptable.proc[NPROC]; temp_p++){
        if(temp_p->priority > 0){
            temp_p->priority = 0;
            temp_p->tick = 0;
        }
    }
    total_tick = 0;
}

int
set_cpu_share(int percent){
    struct proc *p;
    int min_distance = 0;

    // error case
    if(percent <= 0) return -1;
    if(total_percent + percent > 80) return -1;
    
    // plus total percent, and set total percent
    acquire(&ptable.lock);
    total_percent += percent;
    myproc()->percent = percent;
    // stride init value is 1, this means not real stride.
    // it means just this process will be scheduled by stride alogrithm
    myproc()->stride = 1; 
    myproc()->distance = 0;
    // find min_distance process
    // because new process's distance will be set to min_distance for fast response time
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        if ( p->stride != 0 ){
            min_distance = p->distance;
            break;
        }
    }
    // renew all process's stride, because total_percent is changed. 
    for(; p < &ptable.proc[NPROC]; p++){
        if(p->stride != 0){
            p->stride = BIG_TICKETS / p->percent;
            if(p->distance < min_distance) min_distance = p->distance;
        }
    }
    // set min distance to new process
    myproc()->distance = min_distance;
    release(&ptable.lock);
    return percent;
}

/*
void
renew_stride(void)
{
    struct proc *p;
    // I think total_percent * 20 is proper.
    // if total_percent is too small there will be loss stride.
    // think about process A has 2 percent, B has 3 percent
    // then total_percent is 5
    // 5 / 2 = 2, 5 / 3 = 1, process B more running 2 times than A.
    // it is unfair.
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        if( p->stride != 0 ){
            p->stride = (total_percent * 20)/ p->percent;
        }
    }
}
*/

void
reset_distance(void){
    struct proc *p;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        if( p->stride != 0 ){
            p->distance = 0;
        }
    }
}
