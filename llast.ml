open Utils

type t = module_ list

and id = string
and label = string
and value = string
and idx = int
and module_ = { 
    md_id: string ; 
    md_defs: def list ;
    md_strings: string SMap.t ;
  }

and def = 
  | Type of string * type_
  | Fun of function_

and function_ = {
    flink: Llvm.Linkage.t ;
    fcc:   int ;
    fname: string ;
    fargs: id list ;
    ftargs: type_ list ;
    fbody: block list ;
    frett: type_ ;
  }

and type_ = 
  | Any
  | Id of string
  | Path of string * string
  | Void
  | Int1 
  | Int8 
  | Int16 
  | Int32 
  | Int64 
  | ConstInt
  | Float 
  | Double
  | Array of type_
  | Pointer of type_
  | Struct of type_ list
  | Union of type_ list
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
  | FOeq | FOgt | FOge | FOlt
  | FOle | FOne | FOrd | FUeq
  | FUgt | FUge | FUlt | FUle
  | FUne | FUno

and block = {
    bname: string ;
    bdecl: phi list ;
    bbody: instruction list ;
    bret: block_return ;
  }

and block_return = 
  | Return of id list
  | Jmp of id
  | Br of id * label * label
  | Switch of id * (value * label) list * label

and phi = id * type_ * (id * label) list

and instruction = 
  | Alias of id * id
  | Const of id * type_ * const
  | Binop of id * binop * type_ * id * id
  | Extract_value of id * type_ * idx
  | Insert of id * type_ * type_ * idx
  | Alloca of id * type_ 
  | Load of id * type_ * id
  | Store of id * id
  | Get_element_ptr of id * id * int
  | Get_field of id * id * int
  | Icmp of id * icmp * type_ * id * id
  | Fcmp of id * fcmp * type_ * id * id
  | Alloc of id * type_
  | VAlloc of id * type_ * type_
  | Cast of id * id * type_
  | Call of bool * id * id * id list

and const = 
  | Const_int of string
  | Const_float of string
  | Const_enum of int
  | Const_string of string
