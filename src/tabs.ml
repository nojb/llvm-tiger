(* The MIT License (MIT)

   Copyright (c) 2013-2014 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

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

type cmp_op =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_cmp of cmp_op

type ident =
  {
    pid_text: string;
    pid_pos: Lexing.position;
  }

type typ =
  | Tname of ident
  | Tarray of ident
  | Trecord of (ident * ident) list

type var_desc =
  | Vsimple of ident
  | Vsubscript of var * exp
  | Vfield of var * ident

and var =
  {
    pvar_desc: var_desc;
    pvar_pos: Lexing.position;
  }

and exp_desc =
  | Eunit
  | Eint of int
  | Estring of string
  | Enil
  | Evar of var
  | Ebinop of exp * bin * exp
  | Eassign of var * exp
  | Ecall of ident * exp list
  | Eseq of exp * exp
  | Emakearray of ident * exp * exp
  | Emakerecord of ident * (ident * exp) list
  | Eif of exp * exp * exp
  | Ewhile of exp * exp
  | Efor of ident * exp * exp * exp
  | Ebreak
  | Elet of dec * exp

and exp =
  {
    pexp_desc: exp_desc;
    pexp_pos: Lexing.position;
  }

and dec =
  | Dtypes of (ident * typ) list
  | Dfuns of fundef list
  | Dvar of ident * ident option * exp

and fundef =
  {
    fn_name: ident;
    fn_rtyp: ident option;
    fn_args: (ident * ident) list;
    fn_body: exp
  }

module Typedtree = struct
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
      tlevel: int;
      mutable tid: int;
      mutable tdesc: type_desc;
    }

  let last_tid = ref (-1)
  let next_tid () = incr last_tid; !last_tid

  let any_ty = {tid = next_tid (); tname = "<any>"; tlevel = -1; tdesc = ANY}
  let string_ty = {tid = next_tid (); tname = "string"; tlevel = -1; tdesc = STRING}
  let int_ty = {tid = next_tid (); tname = "int"; tlevel = -1; tdesc = INT}
  let void_ty = {tid = next_tid (); tname = "void"; tlevel = -1; tdesc = VOID}

  let type_equal t1 t2 =
    t1.tid == t2.tid || t1.tid == any_ty.tid || t2.tid == any_ty.tid

  let rec name_of_type ty = ty.tname

  type var_desc  =
    | Tsimple of string
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
    | Tbinop of exp * bin * exp
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

  let mkexp d t =
    {
      texp_desc = d;
      texp_type = t;
    }

  let mkvar d t =
    {
      tvar_desc = d;
      tvar_type = t;
    }
end

module S = Set.Make (String)

(* let remove_list l s = *)
(*   List.fold_right S.remove l s *)

(* let union_list l = *)
(*   List.fold_left S.union S.empty l *)

(* let rec fc = function *)
(*   | Eunit *)
(*   | Eint _ *)
(*   | Estring _ *)
(*   | Enil -> S.empty *)
(*   | Evar (_, v) -> fc_var v *)
(*   | Ebinop (_, e1, _, e2) -> S.union (fc e1) (fc e2) *)
(*   | Eassign (_, v, e) -> S.union (fc_var v) (fc e) *)
(*   | Ecall (_, x, es) -> *)
(*       S.add x.s (union_list (List.map fc es)) *)
(*   | Eseq (_, e1, e2) *)
(*   | Emakearray (_, _, e1, e2) -> S.union (fc e1) (fc e2) *)
(*   | Emakerecord (_, _, xes) -> *)
(*       union_list (List.map (fun (_, e) -> fc e) xes) *)
(*   | Eif (_, e1, e2, e3) -> S.union (fc e1) (S.union (fc e2) (fc e3)) *)
(*   | Ewhile (_, e1, e2) -> S.union (fc e1) (fc e2) *)
(*   | Efor (_, _, e1, e2, e3) -> S.union (fc e1) (S.union (fc e2) (fc e3)) *)
(*   | Ebreak _ -> S.empty *)
(*   | Elet (_, Dvar (_, _, e1), e2) -> S.union (fc e1) (fc e2) *)
(*   | Elet (_, Dfuns fundefs, e) -> *)
(*       remove_list (List.map (fun fundef -> fundef.fn_name.s) fundefs) *)
(*         (S.union (fc e) (union_list (List.map *)
(*           (fun fundef -> fc fundef.fn_body) fundefs))) *)
(*   | Elet (_, Dtypes _, e) -> fc e *)

(* and fc_var = function *)
(*   | Vsimple _ -> S.empty *)
(*   | Vsubscript (_, v, e) -> S.union (fc_var v) (fc e) *)
(*   | Vfield (_, v, _) -> fc_var v *)

(* let rec fv = function *)
(*   | Eunit _ *)
(*   | Eint _ *)
(*   | Estring _ *)
(*   | Enil _ -> S.empty *)
(*   | Evar (_, v) -> fv_var v *)
(*   | Ebinop (_, e1, _, e2) -> S.union (fv e1) (fv e2) *)
(*   | Eassign (_, v, e) -> S.union (fv_var v) (fv e) *)
(*   | Ecall (_, _, es) -> union_list (List.map fv es) *)
(*   | Eseq (_, e1, e2) *)
(*   | Emakearray (_, _, e1, e2) -> S.union (fv e1) (fv e2) *)
(*   | Emakerecord (_, _, xes) -> *)
(*       List.fold_left S.union S.empty (List.map (fun (_, e) -> fv e) xes) *)
(*   | Eif (_, e1, e2, e3) -> S.union (fv e1) (S.union (fv e2) (fv e3)) *)
(*   | Ewhile (_, e1, e2) -> S.union (fv e1) (fv e2) *)
(*   | Efor (_, i, e1, e2, e3) -> *)
(*       S.union (fv e1) (S.union (fv e2) (S.remove i.s (fv e3))) *)
(*   | Ebreak _ -> S.empty *)
(*   | Elet (_, Dvar (x, _, e1), e2) -> S.union (fv e1) (S.remove x.s (fv e2)) *)
(*   | Elet (_, Dfuns fundefs, e) -> *)
(*       S.union (fv e) *)
(*         (union_list (List.map (fun fundef -> *)
(*           remove_list (List.map (fun (x, _) -> x.s) fundef.fn_args) *)
(*             (fv fundef.fn_body)) fundefs)) *)
(*   | Elet (_, Dtypes _, e) -> fv e *)

(* and fv_var = function *)
(*   | Vsimple x -> S.singleton x.s *)
(*   | Vsubscript (_, v, e) -> S.union (fv_var v) (fv e) *)
(*   | Vfield (_, v, _) -> fv_var v *)

(* let rec triggers = function *)
(*   | Eunit _ *)
(*   | Eint _ *)
(*   | Estring _ *)
(*   | Enil _ -> false *)
(*   | Evar (_, v) -> triggers_var v *)
(*   | Ebinop (_, e1, _, e2) -> triggers e1 || triggers e2 *)
(*   | Eassign (_, v, e) -> triggers_var v || triggers e *)
(*   | Ecall _ -> true *)
(*   | Eseq (_, e1, e2) -> triggers e1 || triggers e2 *)
(*   | Emakearray _ *)
(*   | Emakerecord _ -> true *)
(*   | Eif (_, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3 *)
(*   | Ewhile (_, e1, e2) -> triggers e1 || triggers e2 *)
(*   | Efor (_, _, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3 *)
(*   | Ebreak _ -> false *)
(*   | Elet (_, Dvar (_, _, e1), e2) -> triggers e1 || triggers e2 *)
(*   | Elet (_, Dfuns _, e) *)
(*   | Elet (_, Dtypes _, e) -> triggers e *)

(* and triggers_var = function *)
(*   | Vsimple _ -> false *)
(*   | Vsubscript (_, v, e) -> triggers_var v || triggers e *)
(*   | Vfield (_, v, _) -> triggers_var v *)
