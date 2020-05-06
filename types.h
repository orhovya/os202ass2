typedef unsigned int   uint;
typedef unsigned short ushort;
typedef unsigned char  uchar;
typedef uint pde_t;

struct sigaction {
  void (*sa_handler)(int);
  uint sigmask;
};