
let root = GenGlobals.root
let suffix = ".lml"
let (@@) x l = (root ^ x ^ suffix) :: l
let stdlib =
  "print" @@
  "array" @@ 
  "list" @@ []

