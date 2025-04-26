#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "fcntl.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"
#include "stat.h"

// For kernel file management
int proc_close(int fd);
int proc_write(int fd, char *text, int size);
static struct inode* proc_create(char *path, short type, short major, short minor);
static int proc_fdalloc(struct file *f);
int proc_open(char *path, int omode);
int proc_read(int fd, int n, char *p);

int swapOutProcessRunning = 0;
int swapInProcessRunning = 0;

int mappages(pde_t *pgdir, void *va, uint size, uint pa, int perm);

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

// Adding circular queue struct of processes reqd. for swapping out
struct circularQueue {
  // Spinlock for synchronization amongst processes
  struct spinlock lock;
  // Circular queue
  struct proc* queue[NPROC + 1];
  int start;
  int end;
};

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
  initlock(&swapOutRequiredQueue.lock, "swap out queue");
  initlock(&swapOutChanelLock, "sleeping channel lock");
  initlock(&swapInWaitingQueue.lock, "swap in queue");
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

  // Instantiate start and end for swapOutRequiredQueue
  acquire(&swapOutRequiredQueue.lock);
  swapOutRequiredQueue.start = 0;
  swapOutRequiredQueue.end = 0;
  release(&swapOutRequiredQueue.lock);

  // Instantiate start and end for swapInWaitingQueue
  acquire(&swapInWaitingQueue.lock);
  swapInWaitingQueue.start = 0;
  swapInWaitingQueue.end = 0;
  release(&swapInWaitingQueue.lock);

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
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
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
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      // Killing the clearSwapOutRequiredQueue
      if(p->state == UNUSED && !strncmp(p->name, "oldSwapOut", strlen("oldSwapOut") + 1)){
        kfree(p->kstack);
        p->kstack = 0;
        p->name[0] = 0;
        p->pid = 0;
      }

      // Killing the clearSwapInQueue process
      if(p->state == UNUSED && !strncmp(p->name, "oldSwapIn", strlen("oldSwapIn") + 1)){
        kfree(p->kstack);
        p->kstack = 0;
        p->name[0] = 0;
        p->pid = 0;
        
      }

      if(p->state != RUNNABLE)
        continue;

      // Clear the accessed bit of the process
      for(int i=0;i<NPDENTRIES;i++){
        //If PDE was accessed earlier
        if(((p->pgdir)[i])&PTE_P && ((p->pgdir)[i])&PTE_A){
          // We need to unset all accessed bits of the subtable
          // Iterating through the page directory entry &
          pte_t* pgentry = (pte_t*)P2V(PTE_ADDR((p->pgdir)[i]));
          for(int j=0;j<NPTENTRIES;j++){
            // unsetting the accessed bits
            if(pgentry[j]&PTE_A){
              pgentry[j]^=PTE_A;
            }
          }
          // Unsetting accessed bit of page directory
          ((p->pgdir)[i])^=PTE_A;
        }
      }

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
    release(&ptable.lock);

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


// create_kernel_process(const char*, void (*f)()) 
// This function takes in process name and a void function pointer
// It allocated a new kernel process (a process that only runs in kernel mode)
// and makes it execute the function pointer provided
void
create_kernel_process(const char* name, void (*entrypoint)()){
  // Allocate a process
  struct proc* p;
  p = allocproc();
  if(p == 0){
    panic("kernel process creation failed");
  }

  // Set up the kernel table in the page table
  p->pgdir = setupkvm();
  if(p->pgdir == 0){
    panic("setupkvm failed");
  }

  // No need to initialse trapframe since this is a kernel process

  // Set eip in context to entrypoint
  p->context->eip = (uint)entrypoint;

  // Set process name
  safestrcpy(p->name, name, sizeof(name));

  // Set process as Runnable
  acquire(&ptable.lock);
  p->state = RUNNABLE;
  release(&ptable.lock);
}

// Pop function for circular queue of processes
struct proc* 
circularQueuePop(struct circularQueue* queue){
  // Acquire lock over circular queue
  acquire(&queue->lock);

  // Check if queue is empty
  if(queue->start == queue->end){
    release(&queue->lock);
    return 0;
  }

  // Get process in front
  struct proc* p;
  p = queue->queue[queue->start];
  
  // Move start
  queue->start += 1;
  queue->start %= NPROC;

  // Release lock over circular queue
  release(&queue->lock);

  return p;
}

// Push function for circular queue of processes
int 
circularQueuePush(struct circularQueue* queue, struct proc* p){
  // Acquire lock over circular queue
  acquire(&queue->lock);
  
  // Check if queue is full
  if((queue->end + 1)%NPROC == queue->start){
    release(&queue->lock);
    return 0;
  }

  // Add to queue
  queue->queue[queue->end] = p;

  // Move end
  queue->end += 1;
  queue->end %= NPROC;

  // Release lock over circular queue
  release(&queue->lock);

  return 1;
}

// Swap Out Required Queue
// All processes that failed to allocate memory for themselves are sleeping and present on this queue
// waiting for someone to swapout pages and wake them up
struct circularQueue swapOutRequiredQueue;

// Swap In Waiting Queue
// All processes that faced a page fault due to page being swapped out are sleeping and present on this queue
struct circularQueue swapInWaitingQueue;

// Copy for file close for kernel use
int
proc_close(int fd)
{
  struct file *f;

  if(fd < 0 || fd >= NOFILE || (f=myproc()->ofile[fd]) == 0)
    return -1;
  
  myproc()->ofile[fd] = 0;
  fileclose(f);
  return 0;
}

// Copy for file write for kernel use
int
proc_write(int fd, char *p, int n)
{
  struct file *f;
  if(fd < 0 || fd >= NOFILE || (f=myproc()->ofile[fd]) == 0)
    return -1;
  return filewrite(f, p, n);
}

// Copy for file create for kernel use
static struct inode*
proc_create(char *path, short type, short major, short minor)
{
  struct inode *ip, *dp;
  char name[DIRSIZ];

  if((dp = nameiparent(path, name)) == 0)
    return 0;
  ilock(dp);

  if((ip = dirlookup(dp, name, 0)) != 0){
    iunlockput(dp);
    ilock(ip);
    if(type == T_FILE && ip->type == T_FILE)
      return ip;
    iunlockput(ip);
    return 0;
  }

  if((ip = ialloc(dp->dev, type)) == 0)
    panic("create: ialloc");

  ilock(ip);
  ip->major = major;
  ip->minor = minor;
  ip->nlink = 1;
  iupdate(ip);

  if(type == T_DIR){  // Create . and .. entries.
    dp->nlink++;  // for ".."
    iupdate(dp);
    // No ip->nlink++ for ".": avoid cyclic ref count.
    if(dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
      panic("create dots");
  }

  if(dirlink(dp, name, ip->inum) < 0)
    panic("create: dirlink");

  iunlockput(dp);

  return ip;
}

// Copy for file fdalloc for kernel use
static int
proc_fdalloc(struct file *f)
{
  int fd;
  struct proc *curproc = myproc();

  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd] == 0){
      curproc->ofile[fd] = f;
      return fd;
    }
  }
  return -1;
}

// Copy for file open for kernel use
int proc_open(char *path, int omode){

  int fd;
  struct file *f;
  struct inode *ip;

  begin_op();

  if(omode & O_CREATE){
    ip = proc_create(path, T_FILE, 0, 0);
    if(ip == 0){
      end_op();
      return -1;
    }
  } else {
    if((ip = namei(path)) == 0){
      end_op();
      return -1;
    }
    ilock(ip);
    if(ip->type == T_DIR && omode != O_RDONLY){
      iunlockput(ip);
      end_op();
      return -1;
    }
  }

  if((f = filealloc()) == 0 || (fd = proc_fdalloc(f)) < 0){
    if(f)
      fileclose(f);
    iunlockput(ip);
    end_op();
    return -1;
  }
  iunlock(ip);
  end_op();

  f->type = FD_INODE;
  f->ip = ip;
  f->off = 0;
  f->readable = !(omode & O_WRONLY);
  f->writable = (omode & O_WRONLY) || (omode & O_RDWR);
  return fd;
}

// Copy of file read for kernel use
int proc_read(int fd, int n, char *p)
{
  struct file *f;
  if(fd < 0 || fd >= NOFILE || (f=myproc()->ofile[fd]) == 0)
  return -1;
  return fileread(f, p, n);

}

// modified stoi
void int_to_string(int x, char *c){
  if(x==0){
    c[0]='0';
    c[1]='\0';
    return;
  }

  int i=0;
  while(x>0){
    c[i]=x%10+'0';
    i++;
    x/=10;
  }
  c[i]='\0';

  for(int j=0;j<i/2;j++){
    char a=c[j];
    c[j]=c[i-j-1];
    c[i-j-1]=a;
  }
}

// Constructs filename using pid, page directory number and page entry number
void
getFileName(char* fileName, int pid, int pdNum, int peNum){
  int virtualPageNumber = ((1<<22)*pdNum)+((1<<12)*peNum);

  int_to_string(pid,fileName);
  int x=strlen(fileName);
  fileName[x]='_';

  int_to_string(virtualPageNumber,fileName+x+1);

  safestrcpy(fileName+strlen(fileName),".swp",5);
}

// clearSwapOutRequiredQueue()
// This function is started as a kernel process when memory allocation fails for some process.
// This function saves an old page of a process in the disk and calls kfree to free that page
// kfree is further responsible for waking up the sleeping processes
// This function is active as a kernel process until all memory needs of the waiting processes are satisified.
void
clearSwapOutRequiredQueue(){
  // Acquire lock over swapOutRequiredQueue
  acquire(&swapOutRequiredQueue.lock);

  // Iterate through all sleeping processes
  while(swapOutRequiredQueue.start != swapOutRequiredQueue.end){
    // Get process from queue
    struct proc *p;
    p = circularQueuePop(&swapOutRequiredQueue);

    // Iterate through all page directory entries of this process
    pde_t* pdentry = p->pgdir;
    for(int i = 0; i < NPDENTRIES; i++){

      // If page directory accessed then skip
      if(pdentry[i]&PTE_A) // PTE_A defined in mmu.h and used to extract the 6th bit of the page flags, representing accessed
        continue;

      // When you find a not recently accesed page directory, iterate through that to find a physical page
      pte_t* pgentry;
      pgentry = (pte_t*)P2V(PTE_ADDR(pdentry[i]));

      for(int j = 0; j < NPTENTRIES; j++){
        // Skip if accessed or not present
        if(pgentry[j]&PTE_A || !(pgentry[j]&PTE_P))
          continue;
        
        // Now we have found an old page that we can remove
        pte_t* pageToRemove = (pte_t*)P2V(PTE_ADDR(pgentry[j]));

        // Get filename
        char fileName[50];
        getFileName(fileName, p->pid, i, j);

        // Open file
        int fd=proc_open(fileName, O_CREATE | O_RDWR);
        if(fd<0){
          cprintf("error creating or opening file: %s\n", fileName);
          panic("swap_out_process");
        }

        // Write to File
        if(proc_write(fd,(char *)pageToRemove, PGSIZE) != PGSIZE){
          cprintf("error writing to file: %s\n", fileName);
          panic("swap_out_process");
        }
        proc_close(fd);

        // Mark the page as free
        kfree((char*)pageToRemove);
        memset(&pgentry[j],0,sizeof(pgentry[j]));

        // Mark this page as being swapped out by using the earlier unused 7th bit
        pgentry[j]=((pgentry[j])^(0x080));

        // Now that we have used this page table, we will use another next time
        break;
      }
    }
  }

  // Release lock over swapOutRequiredQueue once all done
  release(&swapOutRequiredQueue.lock);

  // Killing its own kernel process
  struct proc* p;
  p = myproc();
  if(p == 0)
    panic("swapOutProcess died");

  swapOutProcessRunning = 0;
  p->parent = 0;
  safestrcpy(p->name, "oldSwapOut", strlen("oldSwapOut") + 1);
  p->killed = 0;
  p->state = UNUSED;
  sched();
}

// clearSwapInQueue()
// This function is called when a process encounters page fault due to its page
// being swapped out earlier.
// It extracts a process waiting for page read, allocates a page using kalloc
// then fills in the page using the swapped out earlier.
// Then it uses mappages to add the newly allocated page in its page table
// Then it wakes up the process and after all the proceeses are done it stops itself
void
clearSwapInQueue(){
  // Acquire lock over swapInWaitingQueue
	acquire(&swapInWaitingQueue.lock);

  // Iterate through all elements
	while(swapInWaitingQueue.start != swapInWaitingQueue.end){
    // Get proc in front of the queue;
		struct proc *p;
    p = circularQueuePop(&swapInWaitingQueue);

    // Get filename of the saved file 
    char fileName[50];
    int_to_string(p->pid, fileName);
    int x = strlen(fileName);
    fileName[strlen(fileName)] = '_';
    int_to_string(PTE_ADDR(p->pfAddr), fileName + x + 1);
    safestrcpy(fileName + strlen(fileName), ".swp", 5);

    // Open the file and raise error if not exists
    int fd=proc_open(fileName, O_RDONLY);
    if(fd<0){
      release(&swapInWaitingQueue.lock);
      cprintf("could not find swapped out page file in memory: %s\n", fileName);
      panic("swap in illegal access");
    }

    // Allocate a new page and fill the page data in it
    char *mem = kalloc();
    proc_read(fd, PGSIZE, mem);

    // Add the new page to the page table of the process
    if(mappages(p->pgdir, (void *)PTE_ADDR(p->pfAddr), PGSIZE, V2P(mem), PTE_W|PTE_U) < 0){
      release(&swapInWaitingQueue.lock);
      panic("failed to mappages while swapping in");
    }

    // Wakeup this sleeping process
    wakeup(p);
	}

  // After all processes are done, release the lock
  release(&swapInWaitingQueue.lock);

  // Kill its own kernel process
  struct proc *p;
  p = myproc();
	if(p == 0)
	  panic("swapInProcess died");

	swapInProcessRunning = 0;
	p->parent = 0;
  safestrcpy(p->name, "oldSwapIn", strlen("oldSwapIn") + 1);
	p->killed = 0;
	p->state = UNUSED;
	sched();
}