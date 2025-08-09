type 'a loc =
  {
    desc: 'a;
    loc: Lexing.position;
  }

type comparison =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_cmp of comparison

type ident =
  string loc

type typ =
  | Tname of ident
  | Tarray of ident
  | Trecord of (ident * ident) list

type var =
  var_ loc

and var_ =
  | Vsimple of ident
  | Vsubscript of var * exp
  | Vfield of var * ident

and exp =
  exp_ loc

and exp_ =
  | Eint of int64
  | Estring of string
  | Enil
  | Evar of var
  | Ebinop of exp * bin * exp
  | Eassign of var * exp
  | Ecall of  ident * exp list
  | Eseq of exp list
  | Earray of ident * exp * exp
  | Erecord of ident * (ident * exp) list
  | Eif of exp * exp * exp option
  | Ewhile of exp * exp
  | Efor of ident * exp * exp * exp
  | Ebreak
  | Elet of dec list * exp

and dec =
  | Dtype of ident * typ
  | Dfun of fundef
  | Dvar of ident * ident option * exp

and fundef =
  { fn_name: ident;
    fn_rtyp: ident option;
    fn_args: (ident * ident) list;
    fn_body: exp }

type program =
  {
    name: string;
    body: exp;
  }
