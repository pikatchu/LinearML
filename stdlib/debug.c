#include "liml.h"
#include<stdio.h>

lvalue debug(lvalue v){
  printf("%p\n", (void*)v) ;
  return 0 ;
}

lvalue land(lvalue n1, lvalue n2){
  return (n1 & n2) ;
}

lvalue lsl(lvalue n1, lvalue n2){
  return (n1 << n2) ;
}
