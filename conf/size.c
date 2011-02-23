/*
  Program used to determin which kind of architecture we are dealing with
*/

#include <stdio.h>

int main(int argc, char** argv){

  int isize = sizeof(int) ;
  int vsize = sizeof(void*) ;
  int fsize = sizeof(float) ;
  int dsize = sizeof(double) ;
    
  if(isize == 4){
    if(vsize == 4 && fsize == 4){
      printf("ARCH_32\n") ; return 0 ;
    }
  }

  if(isize == 8){
    if(vsize == 8 && dsize == 8){
      printf("ARCH_64\n"); return 0 ;
    }
  }

  printf("UNKOWN\n") ;
  return 0 ;
}
