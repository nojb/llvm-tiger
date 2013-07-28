open Globals

type bin = 
  Parsetree.bin

type llvm_type =
  | Tint of int
  | Tarray of int * llvm_type
  | Tpointer of llvm_type
  | Tstruct of llvm_type array
  | Tnamedstruct of string

type signature = {
  sig_args : llvm_type array;
  sig_rtyp : llvm_type option
}

type value =
  | VUNDEF
  | VINT of int * int
  | VNULL of llvm_type
  | VVAR of Id.t
  | VLOAD of Id.t

type cexp =
  | VAL of value
  | ALLOCA of bool * llvm_type
  | MALLOC of llvm_type
  | ARRAY_MALLOC of value * value
  | LOAD of value
  | STORE of value * value
  | BINOP of value * bin * value
  | CALL of Id.t * value list
  | EXT_CALL of string * value list
  | GEP of value * value list
  | PTRTOINT of value

type exp =
  | DIE of string
  | LET of Id.t * llvm_type * cexp * exp
  | IF of value * exp * exp
  | RETURN of cexp
  | LET_BLOCK of Id.t * (Id.t * llvm_type) list * exp * exp
  | GOTO of Id.t * value list
  | LET_REC of (Id.t, llvm_type, exp) fundef list * exp

type prog = {
  prog_named : (string * llvm_type list) list;
  prog_strings : (Id.t * string) list;
  prog_body : exp
}
