(* The MIT License (MIT)

   Copyright (c) 2013-2016 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE. *)

type type_desc =
  | VOID
  | INT
  | STRING
  | ARRAY of type_expr
  | RECORD of (string * type_expr) list
  | ANY
  | REF of type_expr option ref

and type_expr =
  {
    tname: string;
    mutable tid: int;
    mutable tdesc: type_desc;
  }

val next_tid: unit -> int
val any_ty: type_expr
val string_ty: type_expr
val int_ty: type_expr
val void_ty: type_expr

val type_equal: type_expr -> type_expr -> bool

val name_of_type: type_expr -> string

type ident =
  {
    stamp: int;
    name: string;
  }

val new_ident: string -> ident

type var_desc  =
  | Tsimple of ident
  | Tindex of var * exp
  | Tfield of var * int

and var =
  {
    tvar_desc: var_desc;
    tvar_type: type_expr;
  }

and exp_desc =
  | Tunit
  | Tint of int
  | Tstring of string
  | Tnil
  | Tvar of var
  | Tbinop of exp * Tabs.bin * exp
  | Tassign of var * exp
  | Tcall of ident * exp list
  | Tseq of exp * exp
  | Tmakearray of exp * exp
  | Tmakerecord of exp list
  | Tif of exp * exp * exp
  | Twhile of exp * exp
  | Tfor of ident * exp * exp * exp
  | Tbreak
  | Tlet of ident * exp * exp
  | Tletrec of fundef list * exp

and exp =
  {
    texp_desc: exp_desc;
    texp_type: type_expr;
  }

and fundef =
  {
    fun_name: ident;
    fun_args: (ident * type_expr) list;
    fun_rety: type_expr;
    fun_body: exp;
  }

val mkexp: exp_desc -> type_expr -> exp
val mkvar: var_desc -> type_expr -> var
