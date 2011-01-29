#include<stdio.h>
double float_of_int(int x){ return (double)x ; }
int lsl(int x, int y){ return (x << y) ; }
int land(int x, int y) { return (x & y) ; }
void debug(void* p) { printf("%p\n", p) ; } 
void* magic(void* p) { return p; }
void magic2(void* p) { return ; }
