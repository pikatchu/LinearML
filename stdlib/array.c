#include<malloc.h>

int* liml_array_make(int(*f)(int), int size){
  int* res = malloc(sizeof(int) * (size + 1)) ;
  int i ;
  *res = (int)(void*)size ;
  res++ ;
  for(i = 0 ; i < size ; i++){
    res[i] = f(i) ;
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
