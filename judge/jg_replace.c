#include "valgrind.h"
#include <errno.h>

int I_WRAP_SONAME_FNNAME_ZU(libcZdZa,socket)(int domain, int type, int protocol)
{
   errno = EACCES;
   return -1;
}

