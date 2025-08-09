module Ident: sig
  type t
  type state
  val new_state: unit -> state
  val create: state -> string -> t
  val name: t -> string
  val equal: t -> t -> bool
  module Map: Map.S with type key = t
end = struct
  type t = { name: string; id: int }
  type state = int ref
  let new_state () = ref 0
  let create r name = incr r; { name; id = !r }
  let name { name; id = _ } = name
  let compare t1 t2 = Int.compare t1.id t2.id
  let equal t1 t2 = Int.equal t1.id t2.id
  module Map = Map.Make(struct type nonrec t = t let compare = compare end)
end

type ident = Ident.t

type type_structure =
  | Tarray of type_id
  | Trecord of (string * type_id) list

and type_id =
  | Tint
  | Tstring
  | Tconstr of ident

type signature =
  type_id list * type_id option

type loc =
  {
    filename: string;
    lineno: int;
    column: int;
  }

type variable =
  | Vsimple of ident
  | Vsubscript of type_id * variable * expression
  | Vfield of loc * type_id array * variable * int
  | Vup of int * int

and expression =
  | Eint of int64
  | Estring of string
  | Enil
  | Evar of type_id * variable
  | Ebinop of expression * Tabs.bin * expression

and statement =
  | Sskip
  | Sloop of statement
  | Sbreak
  | Sifthenelse of expression * statement * statement
  | Sseq of statement * statement
  | Sassign of variable * expression
  | Scall of variable option * string * expression list * signature
  | Sreturn of expression option
  | Sarray of variable * expression * type_id * expression
  | Srecord of variable * type_id array * expression list

and fundef =
  { fn_name: ident;
    fn_rtyp: type_id option;
    fn_args: (ident * type_id) list;
    fn_vars: (ident * type_id) list;
    fn_body: statement }

and program =
  {
    p_name: string;
    p_cstr: (ident, type_structure) Hashtbl.t;
    p_vars: (ident, type_id) Hashtbl.t;
    p_body: statement;
  }
