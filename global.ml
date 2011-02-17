
let root = GenGlobals.root
let max_reg_return = 1
let suffix = ".lml"
let (@@) x l = (root ^ x ^ suffix) :: l
let stdlib =
  "print" @@
  "array" @@ 
  "list" @@ 
  "math" @@ 
  []

