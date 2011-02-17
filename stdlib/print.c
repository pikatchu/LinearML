#include"liml.h"
#include<stdio.h>

void print_int(lvalue n__){
  int n = (int) n__ ;
  printf("%d", n) ;
}

void print_newline(){
  printf("\n") ;
}

void print_float(lvalue x__){
  float x = V2F(x__) ;
  printf("%f", x) ;
}

void print_string(lvalue x__){
  char *x = (char*) x__ ;
  printf("%s", x) ;
}
