#define DARCH_32

#ifdef DARCH_32

typedef void   *lvalue ;
#define lint   int
#define lfloat lvalue

#define V2F(x)   (*((float*)&(x)))
#define F2V(x)   ((void*)(*((int*)&(x))))

#endif

#ifdef DARCH_64

typedef void   *lvalue ;
#define lint   int
#define lfloat lvalue

#define V2F(x)   (*((double*)&(x)))
#define F2V(x)   (*((int*)&(x)))

#endif
