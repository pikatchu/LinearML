
; ModuleID = 'FA'

define fastcc i32 @unsafe_iarray_get(i8* %t, i32 %i) alwaysinline{
entry:
  %td  = bitcast i8* %t to i32* ;
  %tmp = getelementptr i32* %td, i32 %i ;
  %res = load i32* %tmp ;
  ret i32 %res ;
}

define fastcc i8* @unsafe_iarray_set(i8* %t, i32 %i, i32 %x) alwaysinline{
entry:
  %td  = bitcast i8* %t to i32* ;
  %tmp = getelementptr i32* %td, i32 %i ;
  store i32 %x, i32* %tmp ;
  ret i8* %t ;	
}
