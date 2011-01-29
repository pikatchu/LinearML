#include<malloc.h>
#include<string.h>

int* unsafe_iarray_make(int n, int d){
  int* res = malloc(sizeof(int) * n) ;
  int i ;

  for (i = 0 ; i < n ; i++){
    res[i] = d ;
  }

  return res ;
}

void unsafe_iarray_release(int* d){
  free(d) ;
  return ;
}

void* unsafe_iarray_copy(void* src, void* dest, int n){
  memcpy(dest, src, n * sizeof(int)) ;
  return dest ;
}
