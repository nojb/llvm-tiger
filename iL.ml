type llvm_type =
  | Tint of int
  | Tarray of int * llvm_type
  | Tpointer of llvm_type
  | Tstruct of llvm_type array
  | Tnamedstruct of string

type value =
  | Undef
  | Int       of int * int
  | Null      of llvm_type
  | Global    of string
  | Function  of string
  | Var       of string
  | Loadvar   of string

type cmp =
  | Eq | Ne | Le | Ge | Lt | Gt

type binary =
  | Add | Mul | Div | Sub | Icmp of cmp
  
type unary =
  | Ptrtoint  of llvm_type

type label =
  string

type block =
  | Binary    of string * binary * value * value * block
  | Unary     of string * unary * value * block
  | Malloc    of string * llvm_type * block
  | Alloca    of string * llvm_type * bool * block
  | Load      of string * value * block
  | Gep       of string * value * value list * block
  | Phi       of string * (label * value) list * block
  | Call      of string * value * value list * block
  | Store     of value * value * block
  | Condbr    of value * label * label
  | Br        of label
  | Ret       of value option

module M = Map.Make (String)

type fundef = {
  name : string;
  rtyp : llvm_type option;
  args : (string * llvm_type) list;
  body : block M.t;
  main : label
}
