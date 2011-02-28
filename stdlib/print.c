#include"liml.h"
#include<stdio.h>

lvalue print_int(lvalue n__){
  int n = (int) n__ ;
  printf("%d", n) ;
  return 0 ;
}

lvalue print_newline(){
  printf("\n") ;
  return 0 ;
}

lvalue print_float(lvalue x__){
  float x = V2F(x__) ;
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
