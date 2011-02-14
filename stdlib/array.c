#include<malloc.h>

int* liml_array_make(int(*f)(int), int size){
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;

  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = f(i) ;
  }
  return res ;
}

int* liml_array_fmake(int size, float f){
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;
  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = f ;
  }
  return res ;
}

int* liml_array_imake(int size, int n){
  int i ;
  int* res = malloc(sizeof(int) * (size + 1)) ;
  *res = size ;
  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = n ;
  }

  return res ;
}

int liml_array_length(int* t){ 

  return *(t-1) ; 
}

void liml_array_release(void(*f)(int), int* t){
  int i ;
  int size = *(t-1) ;

  for(i = 0 ; i < size ; i++){
    f(t[i]) ;
  }
  return;
}

void liml_array_ifrelease(int* t){
  free(t-1) ;
  return;
}
