#define DARCH_32 
#include"liml.h"
#include<malloc.h>

typedef struct{
  lvalue fst ;
  lvalue snd ;
} couple ;

lvalue magic(){
  return 0 ;
}

lvalue liml_array_make(lvalue size__, lvalue call__, lvalue f, lvalue acc){
  int size = (int) size__ ;
  couple(*call)(lvalue, lvalue, lvalue) = 
    (couple (*)(lvalue, lvalue, lvalue)) call__ ;
  couple res ;
  int i ;
  int* t = malloc(sizeof(int) * (size + 1)) ;
  *t = size ;
  t++ ;

  printf("here %p %p %p %p\n", size, call, f, acc) ; exit(0) ;
  
  for(i = 0 ; i < size ; i++){
    couple c = call(f, acc, i) ;
    printf("here\n") ;
    acc = c.fst ;
    t[i] = c.snd ;
  }

  res.fst = acc ;
  res.snd = (lvalue)t ;

  return 0 ;
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
