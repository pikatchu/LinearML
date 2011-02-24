#include"liml.h"
#include<malloc.h>

lvalue liml_array_make(lvalue size__, lvalue call__, lvalue f){
  int size = (int) size__ ;
  lvalue (*call)(lvalue, lvalue) = 
    (lvalue (*)(lvalue, lvalue)) call__ ;
  int i ;
  int* t = malloc(sizeof(int) * (size + 1)) ;
  *t = size ;
  t++ ;
  
  for(i = 0 ; i < size ; i++){
    t[i] = call(f, i) ; 
  }

  return (lvalue)t ;
}

lvalue liml_array_ifmake(lvalue size, lvalue n){
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;
  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = n ;
  }

  return (lvalue)res ;
}

lvalue liml_array_length(lvalue t__){
  lvalue* t = (lvalue*) t__ ;
  return (lvalue)*(t-1) ; 
}

lvalue liml_array_release(lvalue call__, lvalue f, lvalue t__){
  int* t = (int*) t__ ;
  lvalue(*call)(lvalue, lvalue) = (lvalue(*)(lvalue,lvalue)) call__ ;
  int i ;
  int size = *(t-1) ;

  for(i = 0 ; i < size ; i++){
    call(f, t[i]) ;
  }
  free(t-1) ;
  return 0;
}

lvalue liml_array_ifrelease(lvalue t__){
  int* t = (void*) t__;
  free(t-1) ;
  return 0;
}
