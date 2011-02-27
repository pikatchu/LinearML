#include "liml.h"
#include<string.h>

lvalue string_make(lvalue v_){
  char* v = (char*)v_ ;
  char* s ;
  lvalue* ptr;
  lvalue size = strlen(v) ;
  
  s = malloc(size + sizeof(lvalue) + 1) ;
  ptr = (lvalue*)s ;
  *ptr = size ;
  s = (char*) (ptr+1) ;
  strcpy(s, v) ;
  return (lvalue)s ;
}

lvalue string_release(lvalue s){
  lvalue* ptr = (lvalue*) s ;
  free(ptr-1) ;
  return 0 ;
}

lvalue string_length(lvalue s){
  lvalue* ptr = (lvalue*) s ;
  return (*(ptr-1)) ;
}

lvalue string_concat(lvalue s1, lvalue s2){
  lvalue size1 = string_length(s1) ;
  lvalue size2 = string_length(s2) ;
  lvalue size = size1 + size2 ;
  lvalue* ptr ;

  char* res = malloc (size + 1 + sizeof(lvalue)) ;
  *((lvalue*)res) = size ;
  res = res + sizeof(lvalue) ;
  strcpy(res, (char*)s1) ;
  strcpy(res+size1, (char*)s2) ;

  return (lvalue) res ;
}
