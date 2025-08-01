type comparison =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type binary_operation =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_cmp of comparison

type type_structure =
  | Tarray of type_id
  | Trecord of (string * type_id) list

and type_id =
  | Tint
  | Tstring
  | Tconstr of string

type signature =
  type_id list * type_id option

type variable =
  | Vsimple of string
  | Vsubscript of variable * expression
  | Vfield of variable * int
  | Vup of int * int

and expression =
  | Eint of int32
  | Estring of string
  | Enil
  | Evar of type_id * variable
  | Ebinop of expression * binary_operation * expression
  | Ecall of string * expression list
  | Earray of string * expression * expression
  | Erecord of string * (string * expression) list

and statement =
  | Sskip
  | Sloop of statement
  | Sbreak
  | Sifthenelse of expression * statement * statement
  | Sseq of statement * statement
  | Sassign of variable * expression
  | Scall of string * expression list * signature
  | Sreturn of expression option

and fundef =
  { fn_name: string;
    fn_rtyp: type_id option;
    fn_args: (string * type_id) list;
    fn_vars: (string * type_id) list;
    fn_body: statement }

and program =
  {
    p_name: string;
    p_cstr: (string, type_structure) Hashtbl.t;
    p_funs: (string, fundef) Hashtbl.t;
    p_vars: (string, type_id) Hashtbl.t;
    p_body: statement;
  }
