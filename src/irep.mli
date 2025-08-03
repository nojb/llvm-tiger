type ty =
  | Tvoid
  | Tstruct of ty array
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer
  | Tint of int

type signature = ty array * ty

type operation =
  | Pconstint of int32
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep
  | Pcmpint of Tabs.comparison
  | Ialloca of ty
  | Iapply of string
  | Iexternal of string * signature

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

type program =
  {
    name: string;
    code: instruction Label.Map.t;
    entrypoint: instruction;
  }

val transl_program: program -> Llvm.llmodule
