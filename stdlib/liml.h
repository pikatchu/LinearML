#include "./config.h"

#include <stdlib.h>

// Option.None - machine representation
#define NONE 1

#ifdef ARCH_32

typedef lint   lvalue ;
#define lfloat float;

#define V2F(x)   (*((float*)&(x)))
#define F2V(x)   ((lvalue)(*((int*)&(x))))

#endif

#ifdef ARCH_64

typedef long   lvalue ;
#define lint   long
#define lfloat double

#define V2F(x)   (*((double*)&(x)))
#define F2V(x)   (*((long*)&(x)))

#endif
