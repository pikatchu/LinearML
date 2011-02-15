#include"liml.h"
#include<stdio.h>

void print_int(lint n__){
  int n = (int) n__ ;
  printf("%d", n) ;
}

void print_newline(){
  printf("\n") ;
}

void print_float(lfloat x__){
  float x = V2F(x__) ;
  printf("%f", x) ;
}

void print_string(lvalue x__){
  char *x = (char*) x__ ;
  printf("%s", x) ;
}
