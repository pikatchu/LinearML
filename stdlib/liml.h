#include "./config.h"

#ifdef ARCH_32
#include<malloc.h>

typedef int   lvalue ;

#define V2F(x)   (*((float*)&(x)))
#define F2V(x)   ((lvalue)(*((int*)&(x))))

#endif

#ifdef ARCH_64
#include<malloc.h>

typedef long   lvalue ;
#define lint   long
#define lfloat lvalue

#define V2F(x)   (*((double*)&(x)))
#define F2V(x)   (*((int*)&(x)))

#endif
