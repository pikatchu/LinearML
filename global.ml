
let root = GenGlobals.root
let tramp_size = 10
let tramp_align = 4 
let max_reg_return = 1
let suffix = ".lml"
let (@@) x l = (root ^ x ^ suffix) :: l
let stdlib =
  "print" @@
  "array" @@ 
  "list" @@ 
  "math" @@ 
  []

