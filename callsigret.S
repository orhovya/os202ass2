#include "syscall.h"
#include "traps.h"

.globl sigretstart
.globl sigretend

sigretstart:
  movl $SYS_sigret, %eax
  int $T_SYSCALL
sigretend: