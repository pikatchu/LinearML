#include "./config.h"

#ifdef ARCH_32

typedef int   lvalue ;

#define V2F(x)   (*((float*)&(x)))
#define F2V(x)   ((lvalue)(*((int*)&(x))))

#endif

#ifdef ARCH_64

typedef long   lvalue ;
#define lint   long
#define lfloat lvalue

#define V2F(x)   (*((double*)&(x)))
#define F2V(x)   (*((int*)&(x)))

#endif
