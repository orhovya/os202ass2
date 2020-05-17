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


// void 
// change_state_cas(struct proc* p, int state){
//   int curr_val;
//     pushcli();
//     do{
//       curr_val = p->state;
//     }
//     while (!cas(&p->state, curr_val, state));
//     popcli(); 
// }

int 
change_state_cas(struct proc* p, int curr_val , int state){
  int val= cas(&p->state, curr_val, state);
  return val;
}

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


int 
allocpid(void) 
{
  int pid;
  pushcli();
  do {
    pid = nextpid;
  } while (!cas(&nextpid, pid, pid + 1));
  popcli();
  return pid;
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
  // cprintf("Enterd allocproc \n");
  pushcli();
  do {
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
      if(p->state == UNUSED)
        break;
    if (p == &ptable.proc[NPROC]) {                               // if loop reached to the end and did not find an unused process.
      popcli();
     // cprintf("there is no process unused , cprint");
      return 0; 
    }
  } while (!(cas(&p->state, UNUSED, EMBRYO)));
  popcli();

  p->pid = allocpid();
  // cprintf("after loop allocproc chosed pid is %d \n",p->pid);

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

  //cprintf("curproc->pid = %d \n",p->pid);
  // init proc signals array and variables
  for (int i = 0; i < SIG_NUM; i++) {
    p->helper_sigaction[i] = (struct sigaction){ SIG_DFL, 0};
    p->signalhandlers[i] = &(p->helper_sigaction[i]);
 //   cprintf("curproc->signalhandlers[i]->sa_handler = %d \n",p->signalhandlers[i]->sa_handler);
 //   cprintf("curproc->signalhandlers[i]->sigmask = %d  \n",p->signalhandlers[i]->sigmask);
  }
  p->pendingsig = 0;
  p->sigmask = 0;
  p->trapframebackup = 0;
  p->inusermode = 0;
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

  // cprintf("userinit with pid %d and state %d \n",p->pid,p->state);

  // this assignment to p->state lets other cores
  // run this process. 
  
  if(!change_state_cas(p, EMBRYO, RUNNABLE)){}
  // cprintf("end of userinit with pid %d and state %d \n",p->pid,p->state);

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
    // Maybe not necessary to do with cas
    np->state=UNUSED;
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

  np->pendingsig = 0;
  np->sigmask = curproc->sigmask;
  // int n = sizeof(curproc->signalhandlers) / sizeof(curproc->signalhandlers[0]);
  //cprintf("curproc->pid = %d \n",curproc->pid);

  for (int i = 0; i < SIG_NUM; i++) {
     np->signalhandlers[i] = curproc->signalhandlers[i];
   //cprintf("curproc->signalhandlers[i]->sa_handler = %d \n",((struct sigaction*)(curproc->signalhandlers[i]))->sa_handler);
  // cprintf("curproc->signalhandlers[i]->sigmask = %d  \n",((struct sigaction*)(curproc->signalhandlers[i]))->sigmask);
  }

  np->inusermode = 0;
  np->trapframebackup = 0;
  np->stopped = 0;

  if(!change_state_cas(np,EMBRYO,RUNNABLE))
        panic("fork: cas failed");
 
  // cprintf("Fork function, created new process with id %d , Parent is %d\n",np->pid,curproc->pid);
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

  pushcli();
  if(!change_state_cas(curproc,RUNNING,-ZOMBIE))
    panic("exit cas did not work");
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
  // cprintf("in exit before sched\n");
  // Jump into the scheduler, never to return.
  // cprintf("b\n");
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

  pushcli();

  for(;;){

    if (!change_state_cas(curproc, RUNNING, -SLEEPING)) {
      panic("running -> neg_sleeping cas failed");
    }

    curproc->chan= (void *)curproc;

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
        change_state_cas(p,ZOMBIE, UNUSED);
          change_state_cas(curproc,-SLEEPING, RUNNING);

        popcli();

        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      curproc->chan = 0;
      if (!change_state_cas(curproc, -SLEEPING, RUNNING)) {
        panic("neg_sleeping->running cas failed");
      }

      popcli();
      return -1;
    }
    sched();
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
  //cprintf("first in scheduler \n");
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    pushcli();

    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      // if(p->state != RUNNABLE) 
      if(!change_state_cas(p,RUNNABLE, -RUNNING))
        continue;


      // Switch to chosen process.
      c->proc = p;   
      // cprintf("in scheduler swtch pid %d and cpu is %d\n",p->pid,cpuid());
   
      switchuvm(p);
      if(!change_state_cas(p,-RUNNING, RUNNING)){}

      // change_state_cas(p,RUNNING);

      // cprintf("after change state in schedler state of pid %d\n",p->pid,p->state);


      swtch(&(c->scheduler), p->context);
      // cprintf("returend from scheduler swtch pid %d and cpu is %d\n",p->pid),cpuid();

      switchkvm();

      // cprintf("returend from scheduler switchkvm and pid is %d and cpu is %d\n",p->pid,cpuid());


   
      if (change_state_cas(p,-RUNNABLE,RUNNABLE)){
        // cprintf("scheduler state changed to RUNNABLE for pid %d and state is %d and cpu is %d\n",p->pid,p->state,cpuid());
      }
      if (change_state_cas(p,-SLEEPING,SLEEPING)){
        // cprintf("scheduler p->state == -SLEEPING for pid %d and state is %d and cpu is %d\n",p->pid,p->state,cpuid());
      if(p->killed){
        change_state_cas(p,SLEEPING,RUNNABLE);
        // cprintf("scheduler state changed to RUNNABLE for pid and state is %d and cpu is %d\n",p->pid,p->state,cpuid());
       }
      }


        

      if (change_state_cas(p,-ZOMBIE,ZOMBIE)){
        // cprintf("scheduler state changed to SLEEPING before wakeup1 \n");
        wakeup1(p->parent);
        // cprintf("scheduler returend from wakeup1 \n");
      }
            // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;   
    }
    popcli();
  }
  // cprintf("scheduler exited from loop \n");
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
  // insted of using lock on the table we will use only atomic opertions

  if(mycpu()->ncli != 1){
    // cprintf("mycpu()->ncli  = %d . \n",mycpu()->ncli);
    panic("sched locks" );
  }

  if(p->state == RUNNING )
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");

  // cprintf("sched reach the tests\n");  

  intena = mycpu()->intena;
  
  // cprintf("sched before swtch\n");  
  swtch(&p->context, mycpu()->scheduler);

  // cprintf("sched complete swtch\n");  

  mycpu()->intena = intena;


  // cprintf("end of sched\n");  


}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  // cprintf("enterd to yield with pid %d and state %d and cpu is %d\n",myproc()->pid,myproc()->state,cpuid());
  // needed????
  pushcli();

  // change_state_cas(myproc(),-RUNNABLE);
  if (!change_state_cas(myproc(), RUNNING, -RUNNABLE))
    panic("yield: cas failed");
  // cprintf("middle to yield with pid %d and state %d and cpu %d \n",myproc()->pid,myproc()->state,cpuid());

  sched();
  
  // needed????
  popcli();
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  popcli();

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
  pushcli();
  // if(lk != &ptable.lock){  //DOC: sleeplock0
  //   release(lk);
  // }
  p->chan = chan;

  // Go to sleep.
  if(!change_state_cas(p,RUNNING,-SLEEPING))
    panic("sleep: cas failed");  // cprintf("slepppppp for pid %d and  \n",p->pid);
// cprintf("slepppppp for pid %d and state %d \n",p->pid,p->state);
    release(lk);
  sched();
  // cprintf("returend slepppppp pid %d and\n",p->pid);
  // Tidy up.
       acquire(lk);

  popcli();

  // Reacquire original lock.
  // if(lk != &ptable.lock){  //DOC: sleeplock2
  //   acquire(lk);
  // }

}




//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
/*static void
wakeup1(void *chan)
{
struct proc *p;

 pushcli();
  do {
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if((p->chan == chan) && (p->state == SLEEPING || p->state == -SLEEPING))
        break;
    } 
    
    if (p == &ptable.proc[NPROC]) {    
      break; 
      }
  } while (!(cas(&p->state, SLEEPING, -RUNNABLE)));
  popcli();
}*/


static void
wakeup1(void *chan)
{
  struct proc *p;
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if((p->chan == chan) && (p->state == SLEEPING || p->state == -SLEEPING)){
     while(!change_state_cas(p, SLEEPING, -RUNNABLE)){
        if (p->state == RUNNING)
          break;
      }
      if (p->state != RUNNING){   
        p->chan=0;
        if(!change_state_cas(p, -RUNNABLE, RUNNABLE))
          panic("wakeup1 failed");
      }
    }

  }   
}


// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  pushcli();
  wakeup1(chan);
  popcli();
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid, int signum)
{
struct proc *p;
  if( (pid < 0) || (signum < 0) || (signum > (SIG_NUM-1)) ){
    return -1;
  }
  int oldVal;
  pushcli();
  do {
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->pid == pid)
        break;
      }
      if (p == &ptable.proc[NPROC]) {                               // if loop reached to the end 
        popcli();
        return -1; 
      }
      //cprintf("In kill func, non default signal in kill func for pid %d and signum is %d\n",p->pid,signum);
      oldVal =  p->pendingsig;
  } while (!(cas(&p->pendingsig, oldVal , oldVal | (1 << signum))));
  popcli();
  return 0;
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
sigaction(int sigNum, const struct sigaction *act, struct sigaction *oldact){
  struct proc *proc = myproc();
  if(oldact){
    oldact->sa_handler = ((struct sigaction*) proc->signalhandlers[sigNum])->sa_handler; 
    oldact->sigmask =  ((struct sigaction*) proc->signalhandlers[sigNum])->sigmask;

  }
  ((struct sigaction*) proc->signalhandlers[sigNum])->sa_handler =act->sa_handler;
  ((struct sigaction*) proc->signalhandlers[sigNum])->sigmask =act->sigmask;
  return 0; 
}

void 
sigret(void){
  struct proc *proc = myproc();
  // cprintf("In sigret func, process %d return\n",proc->pid);
  memmove(proc->tf, proc->trapframebackup, sizeof(struct trapframe));
  proc->tf->esp += sizeof (struct trapframe);
  proc->inusermode = 0;
  // cprintf("In sigret handlers mask was %d", proc->sigmask);
  proc->sigmask = proc->sigmaskbackup;    
  // cprintf("In sigret proc mask is %d", proc->sigmask);
}


void handlesignals(void){

  struct proc *p = myproc();
  struct sigaction* currAction;
  uint sizeofsigret;

  if (!p) {
    return;
  }

  // handle Stop of process as a result of SIGSTOP - waits until SIGCONT and if ther is no SIGCONT yields
  if (p->stopped) {
    // cprintf("procss %d is stopped , will enter handel contsig.\n",p->pid);
    stopped_loop:
    // cprintf("procss %d is stopped , entered loop.\n",p->pid);
      while (1) {
        for (int i = 0; i < SIG_NUM; i++) {
          currAction = (struct sigaction*)(p->signalhandlers[i]);
          if (p->pendingsig & (1 << SIGCONT) || currAction->sa_handler == (void *) SIGCONT) {
            // cprintf("In handle cont sig func for process %d -  Got sig cont in pending signals. .\n",p->pid);
            pushcli();
            if (cas(&p->stopped, 1, 0)) {
              // cprintf("In handle cont sig func for process %d - stopped value is %d.\n",p->pid,p->stopped);
              p->pendingsig ^= (1 << SIGCONT);
              // cprintf("In handle cont sig func for process %d -  Handled cont sig and reverted to 0 in pending signals.\n",p->pid);
            }
            popcli();
            break;
          } 
        }
        if(p->stopped ==0){
          p->sigmask = p->sigmaskbackup;
          break;
        }
        else
          yield();
      }
  }
  // cprintf("In handlesignals, entering for Loop.\n");
  for (int i = 0; i < SIG_NUM; i++) {
    currAction = (struct sigaction*)(p->signalhandlers[i]);


    // CHECK IF SIG IN SIGMASK
    if ((((1 << i) & p->sigmask) >0 ) & (i !=  SIGKILL) & (i != SIGSTOP) ){ // if handling this signal is not allowd by proc mask - continue.
      // cprintf("In handlesignals, the signal that is being handled is %d an it is in sigmask so skipped.\n",i);
      continue;
    }

    if (((1 << i) & p->pendingsig) == 0){                              // if the bit of signal is not activated (set to 1) then we continue to the next one.
      // cprintf("In handlesignals, the signal that is being handled is %d and it is not set in pending signals of proc.\n",i);
      continue;
    }

    p->pendingsig ^= (1 << i);                                          // xor which remove the signal from pending signals.

    // SIGIGN
    if (currAction->sa_handler == (void *) SIG_IGN) {                     // if signal is sig ignore we will just continue to the next signal.
      // cprintf("In handlesignals, the signal that is being handled is %d and it is SIG_IGN so ignored.\n",i);
      continue;
    }

    // SIGSTOP
    if (i == SIGSTOP || currAction->sa_handler == (void *) SIGSTOP) {     // if SigStop signal
      p->stopped=1;                                                        // process will be stopped and jump into a loop until it gets SitgCont.
      goto stopped_loop;
    }

    // SIGKILL OR SIGDFL
    if (currAction->sa_handler == (void *) SIG_DFL || currAction->sa_handler == (void *) SIGKILL) {                     // default signal is sigkill, so if givven we activate it straightforward.
      // cprintf("In handlesignals, the signal that is being handled is %d and it is SIGKILL, activate kill func with pid %d .\n",i,p->pid);
      p->killed = 1;
        // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;  
      continue;
    }


    p->sigmaskbackup = p->sigmask;                                      // backup signal mask of process before moving to mask of signal
    p->sigmask = currAction->sigmask;                                   // set sigmask of signal as process sigmask.
    


    // USER SIGNAL HANDLERS
    if(p->inusermode){                                                  // check if currently in usermode signal - to check nested signals.
      p->sigmask = p->sigmaskbackup;                                    // if in the middle of user signal then do not run another signal
      p->pendingsig ^= (1 << i);                                        // xor to add the signal to pending signals again as we didnt handled it. 
      continue; 
    }
    else{
      p->inusermode = 1;
      // cprintf("In handlesignals, the signal that is being handled is %d and it is user signal\n",i);
      p->tf->esp -= sizeof(struct trapframe);                             // make space foe trapframe save.
      memmove((void *) (p->tf->esp), p->tf, sizeof(struct trapframe));    // move to esp of current trapframe the pointer to current trapframe.
      p->trapframebackup = (void *) (p->tf->esp);                         // save to backup trapframe the current trapframe
      
      // activate the signal handler in user space with "injecting" return to sigret function after finishing.

      sizeofsigret  = (uint) &sigretend - (uint) &sigretstart;            // save the size of sigret function.
      p->tf->esp -= sizeofsigret;                                         // move esp to save space for sigret function call.
      memmove((void *) (p->tf->esp), sigretstart, sizeofsigret);          // move to esp the beginning of sigret func.
      *((int *) (p->tf->esp - 4)) = i;                                    // push to stack signum parameter
      *((int *) (p->tf->esp - 8)) = p->tf->esp;                           // push to stack return address of sigret
      p->tf->esp -= 8;                                                    // move esp to the beginning of params for handler func.
      p->tf->eip = (uint)(currAction->sa_handler);                         // move eip to the handler's func in user space to run it.
      break;
    }
  }
}
