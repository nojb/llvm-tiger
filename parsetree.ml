open Globals

type cmp_op =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_and | Op_or | Op_cmp of cmp_op


type pos =
  Lexing.position

type pos_string = {
  s : string;
  p : Lexing.position
}

type typ =
  | PTname of pos_string
  | PTarray of pos_string
  | PTrecord of (pos_string * pos_string) list

type var =
  | PVsimple of pos_string
  | PVsubscript of pos * var * exp
  | PVfield of pos * var * pos_string

and exp =
  | Pint of pos * int
  | Pstring of pos * string
  | Pnil of pos
  | Pvar of pos * var
  | Pbinop of pos * exp * bin * exp
  | Passign of pos * var * exp
  | Pcall of pos * pos_string * exp list
  | Pseq of pos * exp list
  | Pmakearray of pos * pos_string * exp * exp
  | Pmakerecord of pos * pos_string * (pos_string * exp) list
  | Pif of pos * exp * exp * exp option
  | Pwhile of pos * exp * exp
  | Pfor of pos * pos_string * exp * exp * exp
  | Pbreak of pos
  | Pletvar of pos * pos_string * pos_string option * exp * exp
  | Pletfuns of pos * (pos_string, pos_string option, pos_string, exp) fundef list * exp
  | Plettype of pos * (pos_string * typ) list * exp

let exp_p = function
  | Pint (p, _)
  | Pstring (p, _)
  | Pnil p
  | Pvar (p, _)
  | Pbinop (p, _, _, _)
  | Passign (p, _, _)
  | Pcall (p, _, _)
  | Pseq (p, _)
  | Pmakearray (p, _, _, _)
  | Pmakerecord (p, _, _)
  | Pif (p, _, _, _)
  | Pwhile (p, _, _)
  | Pfor (p, _, _, _, _)
  | Pbreak p
  | Pletvar (p, _, _, _, _)
  | Pletfuns (p, _, _)
  | Plettype (p, _, _) -> p

let var_p = function
  | PVsimple s -> s.p
  | PVsubscript (p, _, _)
  | PVfield (p, _, _) -> p
