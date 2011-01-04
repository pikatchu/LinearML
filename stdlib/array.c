#include<malloc.h>

typedef struct{
  int size ;
  void** t ;
} array_t ;

typedef struct{
  array_t *t ;
  void* v ;
} get_return_t ;

array_t* array_make(int size){
  void** t = malloc(sizeof(void*) * size) ;
  array_t *res = malloc (sizeof(array_t)) ;
  res->size = size ;
  res->t = t ;
  return res ;
}

array_t* array_set(array_t *t, int n, void* v){
  if(n < 0 || n >= t->size)
    return t ;
  t->t[n] = v ;
  return t ;
}

void* array_get(array_t *t, int n){
  if( n < 0 || n >= t->size)
    return NULL ;

  void* res ;
  res = t->t[n] ;
  t->t[n] = NULL ;
  return res ;
}

void array_free(array_t* t, void (*free_v)(void*)){
  void** h = t->t ;
  int i ;
  for (i = 0 ; i < t->size ; i++){
    free_v(h[i]) ;
  }
  free(h) ;
  free(t) ;
}
