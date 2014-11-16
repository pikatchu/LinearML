#include"liml.h"
#include<stdio.h>

lvalue print_int(lvalue n__){
  lint n = (lint) n__ ;

#ifdef ARCH_32
  printf("%d", n) ;
#endif

#ifdef ARCH_64
  printf("%ld", n) ;
#endif

  return 0 ;
}

lvalue print_newline(){
  printf("\n") ;
  return 0 ;
}

lvalue print_float(lvalue x__){
  lfloat x = V2F(x__) ;
  printf("%f", x) ;
  return 0 ;
}

lvalue print_string(lvalue x__){
  char *x = (char*) x__ ;
  printf("%s", x) ;
  return 0 ;
}

lvalue print_char(lvalue x){
  printf("%c", (char)x) ;
  return 0;
}
