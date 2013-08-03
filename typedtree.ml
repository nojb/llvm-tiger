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

type access =
  | Local
  | NonLocal of int

type var =
  | TVlocal of string * bool
  | TVnonLocal of int * int
  | TVsubscript of int * var * exp
  | TVfield of int * var * int

and exp =
  | TCint of int
  | TCstring of string
  | TCnil of type_spec
  | Tvar of var
  | Tbinop of exp * bin * exp
  | Tassign of var * exp
  | Tcall of string * (exp * bool (* is_ptr *)) list
  | Tseq of exp list
  | Tmakearray of type_spec * exp * exp (* element type, size, init value *)
  | Tmakerecord of type_spec * (exp * bool (* is_ptr *)) list
  | Tif of exp * exp * exp * bool (* is_void *)
  | Twhile of exp * exp
  | Tfor of string * exp * exp * exp
  | Tbreak
  | Tletvar of string * access ref * bool (* is_ptr *) * type_spec * exp * exp
  | Tletfuns of (string, type_spec, type_spec * access ref * bool (* is_ptr *), exp) fundef list * exp

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
  | Tif (e1, e2, e3, _) -> triggers e1 || triggers e2 || triggers e3
  | Twhile (e1, e2) -> triggers e1 || triggers e2
  | Tfor (_, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Tbreak -> false
  | Tletvar (_, _, _, _, e1, e2) -> triggers e1 || triggers e2
  | Tletfuns (_, e) -> triggers e

and triggers_var = function
  | TVlocal _
  | TVnonLocal _ -> false
  | TVsubscript (_, v, e) -> triggers_var v || triggers e
  | TVfield (_, v, _) -> triggers_var v

