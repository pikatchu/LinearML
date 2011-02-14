; ModuleID = 'T'

define void @main() {
__tmp:
  %0 = call float @T_id(float 1.000000e+00)
  call void @print_float(float %0)
  ret void
}

define float @T_id(float) {
__tmp:
  %1 = call float @sin(float %0)
  call void @print_float(float %1)
  ret float %1
}

declare float @sin(float)

declare void @print_float(float)
