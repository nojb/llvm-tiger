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

type cmp_op =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_cmp of cmp_op

type pos_string =
  { s: string;
    p: Lexing.position }

type typ =
  | Tname of pos_string
  | Tarray of pos_string
  | Trecord of (pos_string * pos_string) list

type var_desc =
  | Vsimple of pos_string
  | Vsubscript of var * exp
  | Vfield of var * pos_string

and var =
  { vdesc: var_desc;
    vpos: Lexing.position }

and exp_desc =
  | Eunit
  | Eint of int32
  | Estring of string
  | Enil
  | Evar of var
  | Ebinop of exp * bin * exp
  | Eassign of var * exp
  | Ecall of  pos_string * exp list
  | Eseq of exp * exp
  | Emakearray of pos_string * exp * exp
  | Emakerecord of pos_string * (pos_string * exp) list
  | Eif of exp * exp * exp
  | Ewhile of exp * exp
  | Efor of pos_string * exp * exp * exp
  | Ebreak
  | Elet of dec * exp

and exp =
  { edesc: exp_desc;
    epos: Lexing.position }

and dec =
  | Dtypes of (pos_string * typ) list
  | Dfuns of fundef list
  | Dvar of pos_string * pos_string option * exp

and fundef =
  { fn_name: pos_string;
    fn_rtyp: pos_string option;
    fn_args: (pos_string * pos_string) list;
    fn_body: exp }

module S = Set.Make (String)

let remove_list l s =
  List.fold_right S.remove l s

let union_list l =
  List.fold_left S.union S.empty l

let rec fv e =
  match e.edesc with
  | Eunit
  | Eint _
  | Estring _
  | Enil -> S.empty
  | Evar v -> fv_var v
  | Ebinop (e1, _, e2) -> S.union (fv e1) (fv e2)
  | Eassign (v, e) -> S.union (fv_var v) (fv e)
  | Ecall (_, es) -> union_list (List.map fv es)
  | Eseq (e1, e2)
  | Emakearray (_, e1, e2) -> S.union (fv e1) (fv e2)
  | Emakerecord (_, xes) ->
      List.fold_left S.union S.empty (List.map (fun (_, e) -> fv e) xes)
  | Eif (e1, e2, e3) -> S.union (fv e1) (S.union (fv e2) (fv e3))
  | Ewhile (e1, e2) -> S.union (fv e1) (fv e2)
  | Efor (i, e1, e2, e3) ->
      S.union (fv e1) (S.union (fv e2) (S.remove i.s (fv e3)))
  | Ebreak -> S.empty
  | Elet (Dvar (x, _, e1), e2) -> S.union (fv e1) (S.remove x.s (fv e2))
  | Elet (Dfuns fundefs, e) ->
      S.union (fv e)
        (union_list (List.map (fun fundef ->
          remove_list (List.map (fun (x, _) -> x.s) fundef.fn_args)
            (fv fundef.fn_body)) fundefs))
  | Elet (Dtypes _, e) -> fv e

and fv_var v =
  match v.vdesc with
  | Vsimple x -> S.singleton x.s
  | Vsubscript (v, e) -> S.union (fv_var v) (fv e)
  | Vfield (v, _) -> fv_var v
