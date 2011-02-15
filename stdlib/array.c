#define DARCH_32 
#include"liml.h"
#include<malloc.h>

lvalue liml_array_make(lint size__, lvalue f__){
  int size = (int) size__ ;
  int(*f)(int) = (int (*)(int)) f__ ;
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;
  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = f(i) ;
  }
  return (lvalue)res ;
}

lvalue liml_array_fmake(lint size, lfloat f){
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;
  res++ ;

  for(i = 0 ; i < size ; i++){
    res[i] = f ;
  }
  return (lvalue)res ;
}

lvalue liml_array_imake(lint size, lint n){
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;
  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = n ;
  }

  return (lvalue)res ;
}

lint liml_array_length(lvalue t__){
  int* t = (int*) t__ ;
  return (lint)*(t-1) ; 
}

void liml_array_release(lvalue f__, lvalue t__){
  int* t = (int*) t__ ;
  void(*f)(int) = (void(*)(int)) f__ ;
  int i ;
  int size = *(t-1) ;

  for(i = 0 ; i < size ; i++){
    f(t[i]) ;
  }
  return;
}

void liml_array_ifrelease(lvalue t__){
  int* t = (void*) t__;
  free(t-1) ;
  return;
}
