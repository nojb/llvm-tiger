open Globals

type bin = 
  Parsetree.bin

type typ =
  | Tint of int
  | Tarray of int * typ
  | Tpointer of typ
  | Tstruct of typ array
  | Tnamedstruct of string

type signature = {
  sig_args : typ array;
  sig_rtyp : typ option
}

type value =
  | Vundef
  | Vint      of int * int
  | Vstring   of string
  | Vnull     of typ
  | Vvar      of Id.t
  | Vload     of Id.t

type exp =
  | Ealloca       of bool * typ
  | Emalloc       of typ
  | Earraymalloc  of value * value
  | Eload         of value
  | Ebinop        of value * bin * value
  | Ecall         of Id.t * value array
  | Eextcall      of string * signature * value array
  | Egep          of value * value array
  | Eassert       of value * exp * string
  | Optrtoint     of value

type stm =
  | Sskip
  | Sseq    of stm * stm
  | Sstore  of value * value
  | Sif     of value * stm * stm
  | Sloop   of stm
  | Sbreak
  | Slet    of Id.t * typ * exp * stm
  | Sletrec of (Id.t, typ, stm) fundef list * stm
  | Sreturn of value option

type prog = {
  prog_named : (string * typ array) list;
  prog_strings : (Id.t * string) list;
  prog_body : stm
}
