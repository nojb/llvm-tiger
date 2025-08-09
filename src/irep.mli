type ty =
  | Tvoid
  | Tstruct of ty list
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer
  | Tint of int

type signature = ty list * ty

type operation =
  | Pconstint of int64
  | Pconststring of string
  | Pnull
  | Pparam of int
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep of ty
  | Pcmpint of Tabs.comparison
  | Pand
  | Pzext
  | Ialloca of ty * bool (* gcroot *)
  | Iexternal of string * signature
  | Icall of Typing.ident
  | Imakearray
  | Imakerecord of int

module Reg: sig
  type t
  type state
  val create: unit -> state
  val next: state -> t
  module Map: Map.S with type key = t
end

module Label: sig
  type t
  type state
  val create: unit -> state
  val next: state -> t
  module Map: Map.S with type key = t
  module Tbl: Hashtbl.S with type key = t
end

type reg = Reg.t
type label = Label.t

type instruction =
  | Iop of operation * reg list * reg * instruction
  | Iload of ty * reg * reg * instruction
  | Istore of reg * reg * instruction
  | Iifthenelse of reg * label * label
  | Igoto of label
  | Ireturn of reg option
  | Iunreachable

type fundef =
  {
    name: Typing.fundef_name;
    signature: signature;
    code: instruction Label.Map.t;
    entrypoint: instruction;
  }

type program =
  {
    funs: fundef list;
  }

val transl_program: program -> Llvm.llmodule
