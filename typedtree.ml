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
  | TVlocal of string
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
  | Tmakearray of exp * exp
  | Tmakerecord of string * exp list
  | Tif of exp * exp * exp * bool (* is_void *)
  | Twhile of exp * exp
  | Tfor of string * exp * exp * exp
  | Tbreak
  | Tletvar of string * access ref * bool (* is_ptr *) * type_spec * exp * exp
  | Tletfuns of (string, type_spec, type_spec * access ref, exp) fundef list * exp
