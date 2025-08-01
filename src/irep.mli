type ty =
  | Tvoid
  | Tstruct of ty array
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer
  | Tint of int

type signature = ty array * ty

type comparison = Cleq

type operation =
  | Pconstint of int32
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep
  | Pcmpint of comparison
  | Ialloca of ty
  | Iapply of string
  | Iexternal of string * signature

module Ident: sig
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

type ident = Ident.t
type label = Label.t

type instruction =
  | Iop of operation * ident list * ident * instruction
  | Iload of ty * ident * ident * instruction
  | Istore of ident * ident * instruction
  | Iifthenelse of ident * label * label
  | Igoto of label
  | Ireturn of ident option

type program =
  {
    name: string;
    code: instruction Label.Map.t;
    entrypoint: instruction;
  }

val transl_program: program -> Llvm.llmodule
