
type t = module_ list

and id = string
and label = string
and value = string
and idx = int
and module_ = string * function_ list

and function_ = {
    flink: int ;
    fname: string ;
    fargs: type_ list ;
    fbody: block list ;
    frett: type_ ;
  }

and type_ = 
  | Int1 | Int8 
  | Int16 | Int32 
  | Int64 | ConstInt
  | Float | Double
  | Array of type_
  | Pointer of type_
  | Struct of type_ list
  | Function of type_ list * type_ list

and binop = 
  | Add | Fadd | Sub | Fsub 
  | Mul | Fmul | Udiv | Sdiv 
  | Fdiv | Urem | Srem | Frem 
  | Shl | Lshr | Ashr | And
  | Or | Xor

and icmp =
  | Eq | Ne | Ugt | Uge
  | Ult | Ule | Sgt | Sge
  | Slt | Sle

and fcmp =
  | Oeq | Ogt | Oge | Olt
  | Ole | One | Ord | Ueq
  | Ugt | Uge | Ult | Ule
  | Une | Uno

and block = {
    bname: string ;
    bdecl: phi list ;
    bbody: equation list ;
    bret: id ;
  }

and phi = type_ * (id * label) list

and equation = id * instruction
and instruction = 
  | Br of label * label
  | Switch of (value * label) list
  | Binop of binop * type_ * id * id
  | Extract_value of type_ * idx
  | Insert of type_ * type_ * idx
  | Alloca of type_ 
  | Load of type_ * id
  | Store of type_ * id * id (* value * pointer *)
  | Get_element_ptr of int
  | Icmp of icmp * type_ * id * id
  | Fcmp of fcmp * type_ * id * id
