#include "liml.h"
#include<stdio.h>

lvalue debug(lvalue v){
  printf("%p\n", (void*)v) ;
  return 0 ;
}

int land(int n1, int n2){
  return (n1 & n2) ;
}

int lsl(int n1, int n2){
  return (n1 << n2) ;
}
