; Bugs when interpreted with lli -O0 

; ModuleID = 'T'

%0 = type { i32 }

define fastcc i32 @T_add(i32, i32) {
__tmp48:
  %__tmp45 = add i32 %0, %1
  ret i32 %__tmp45
}

define i32 @f(i8* nest, i32) {
;  %3 = getelementptr inbounds %0* %0, i32 0, i32 0
;  %4 = load i32* %3
;  %5 = call fastcc i32 @T_add(i32 %4, i32 %1)
  ret i32 0 ; %5
}


define void @main() {
__tmp44:
  %0 = alloca %0
  %1 = getelementptr inbounds %0* %0, i32 0, i32 0
  store i32 1, i32* %1
  %2 = alloca [10 x i8], align 4
  %3 = getelementptr [10 x i8]* %2, i32 0, i32 0
  %4 = bitcast i32* %1 to i8*
  %5 = call i8* @llvm.init.trampoline(i8* %3, i8* bitcast (i32 (i8* nest, i32)* @f to i8*), i8* %4)
  %6 = bitcast i8* %5 to i32 (i32)*
  %7 = call i32 %6(i32 1)
  ret void
}

declare i8* @llvm.init.trampoline(i8*, i8*, i8*) nounwind

