module Ident: sig
  type t
  type state
  val new_state: unit -> state
  val create: state -> string -> t
  val name: t -> string
  val unique_name: t -> string
  val equal: t -> t -> bool
  module Set: Set.S with type elt = t
  module Map: Map.S with type key = t
end = struct
  type t = { name: string; id: int }
  type state = int ref
  let new_state () = ref 0
  let create r name = incr r; { name; id = !r }
  let name { name; id = _ } = name
  let unique_name { name; id } = Printf.sprintf "%s_%i" name id
  let compare t1 t2 = Int.compare t1.id t2.id
  let equal t1 t2 = Int.equal t1.id t2.id
  module Set = Set.Make(struct type nonrec t = t let compare = compare end)
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

type implem =
  | External of string
  | Internal of ident

type 'a typed =
  {
    desc: 'a;
    ty: type_id;
  }

type variable' =
  | Vsimple of ident
  | Vsubscript of loc * variable * expression
  | Vfield of loc * variable * int

and variable =
  variable' typed

and expression' =
  | Eint of int64
  | Estring of string
  | Enil
  | Evar of variable
  | Ebinop of expression * Tabs.bin * expression

and expression =
  expression' typed

and statement =
  | Sskip
  | Sloop of statement
  | Sbreak
  | Sifthenelse of expression * statement * statement
  | Sseq of statement * statement
  | Sassign of variable * expression
  | Scall of variable option * implem * expression list * signature
  | Sreturn of expression option
  | Sarray of variable * expression * expression
  | Srecord of variable * expression list

type fundef_name =
  | Main
  | Internal of ident

type fundef =
  { fn_name: fundef_name;
    fn_rtyp: type_id option;
    fn_args: (ident * type_id) list;
    fn_vars: (ident * type_id) list;
    fn_esca: Ident.Set.t;
    fn_body: statement }

type program =
  {
    p_cstr: (ident * type_structure) list;
    p_funs: fundef list;
  }
