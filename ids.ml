

type program = handler list

and handler = (pat list) * handler_body

and id = 
  | Var of string
  | BCall of string

and pat = 
  | Id  of id
  | Neg of id

and instruction = 
  | Emit of string list
  | VCall of string

and handler_body = (instruction list) * (case list)

and case = (pat list) * (instruction list)

