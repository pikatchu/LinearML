#include<malloc.h>

double* unsafe_farray_make(int n, double d){
  double* res = malloc(sizeof(double) * n) ;
  int i ;

  for (i = 0 ; i < n ; i++){
    res[i] = d ;
  }

  return res ;
}

void unsafe_farray_release(double* d){
  free(d) ;
  return ;
}

