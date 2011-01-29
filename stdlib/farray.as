
; ModuleID = 'FA'

define fastcc double @unsafe_farray_get(i8* %t, i32 %i) alwaysinline{
entry:
  %td  = bitcast i8* %t to double* ;
  %tmp = getelementptr double* %td, i32 %i ;
  %res = load double* %tmp ;
  ret double %res ;
}

define fastcc i8* @unsafe_farray_set(i8* %t, i32 %i, double %x) alwaysinline{
entry:
  %td  = bitcast i8* %t to double* ;
  %tmp = getelementptr double* %td, i32 %i ;
  store double %x, double* %tmp ;
  ret i8* %t ;	
}
