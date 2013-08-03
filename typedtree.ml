open Globals

type type_spec =
  | VOID
  | INT
  | STRING
  | ARRAY   of string * type_spec
  | RECORD  of string * Id.t (* name, unique name *)
  | PLACE   of string

type bin =
  Parsetree.bin

type ptr_flag =
  | IsPtr of bool

type free_flag =
  | IsFree of bool

type void_flag =
  | IsVoid of bool

type imm_flag =
  | IsImm of bool

type arg =
  | ArgNonLocal of string
  | ArgExp of exp * ptr_flag

and var =
  | TVsimple of string * imm_flag
  | TVsubscript of int (* line no *) * var * exp
  | TVfield of int (* line no *) * var * int

and exp =
  | TCint of int
  | TCstring of string
  | TCnil of type_spec
  | Tvar of var
  | Tbinop of exp * bin * exp
  | Tassign of var * exp
  | Tcall of string * arg list
  | Tseq of exp list
  | Tmakearray of type_spec * exp * exp (* element type, size, init value *)
  | Tmakerecord of type_spec * (exp * ptr_flag) list
  | Tif of exp * exp * exp * void_flag * type_spec
  | Twhile of exp * exp
  | Tfor of string * exp * exp * exp
  | Tbreak
  | Tletvar of string * ptr_flag * type_spec * exp * exp

let rec triggers (e : exp) : bool =
  match e with
  | TCint _
  | TCstring _
  | TCnil _ -> false
  | Tvar (v) -> triggers_var v
  | Tbinop (e1, _, e2) -> triggers e1 || triggers e2
  | Tassign (v, e) -> triggers_var v || triggers e
  | Tcall _ -> true
  | Tseq (es) -> List.exists triggers es
  | Tmakearray _
  | Tmakerecord _ -> true
  | Tif (e1, e2, e3, _, _) -> triggers e1 || triggers e2 || triggers e3
  | Twhile (e1, e2) -> triggers e1 || triggers e2
  | Tfor (_, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Tbreak -> false
  | Tletvar (_, _, _, e1, e2) -> triggers e1 || triggers e2

and triggers_var = function
  | TVsimple _ -> false
  | TVsubscript (_, v, e) -> triggers_var v || triggers e
  | TVfield (_, v, _) -> triggers_var v

