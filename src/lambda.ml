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

type ident = Typedtree.ident

type comparison =
  | Ceq | Cneq | Clt | Cgt | Cle | Cge

type constant =
  | Const_int of int
  | Const_string of string

type primitive =
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgetfield of int
  | Psetfield of int
  | Parrayget
  | Parrayset
  | Pcompint of comparison
  | Pcompstring of comparison
  | Pmakearray
  | Pmakeblock of int
  | Pccall of string

type lambda =
  | Lconst of constant
  | Lvar of ident
  | Lifthenelse of lambda * lambda * lambda
  | Lassign of ident * lambda
  | Lwhile of lambda * lambda
  | Lfor of ident * lambda * lambda * lambda
  | Lstaticcatch of lambda
  | Lstaticfail
  | Lprim of primitive * lambda list
  | Lapply of ident * lambda list
  | Lletrec of (ident * ident list * lambda) list * lambda
  | Llet of ident * lambda * lambda
  | Lsequence of lambda * lambda

module Ident = struct
  type t = ident
  let compare id1 id2 =
    compare id1.Typedtree.stamp id2.Typedtree.stamp
end

module IdentSet = Set.Make (Ident)

let rec fv = function
  | Lconst _ ->
      IdentSet.empty
  | Lvar id ->
      IdentSet.singleton id
  | Lifthenelse (e1, e2, e3) ->
      IdentSet.union (fv e1) (IdentSet.union (fv e2) (fv e3))
  | Lassign (id, e) ->
      IdentSet.add id (fv e)
  | Lwhile (e1, e2) ->
      IdentSet.union (fv e1) (fv e2)
  | Lfor (id, e1, e2, e3) ->
      IdentSet.union (fv e1) (IdentSet.union (fv e2) (IdentSet.remove id (fv e3)))
  | Lstaticcatch e ->
      fv e
  | Lstaticfail ->
      IdentSet.empty
  | Lprim (_, el) | Lapply (_, el) ->
      List.fold_left (fun s e -> IdentSet.union s (fv e)) IdentSet.empty el
  | Lletrec (funs, e) ->
      List.fold_left (fun s f -> IdentSet.union s (fv_fundef f)) (fv e) funs
  | Llet (id, e1, e2) ->
      IdentSet.union (fv e1) (IdentSet.remove id (fv e2))
  | Lsequence (e1, e2) ->
      IdentSet.union (fv e1) (fv e2)

and fv_fundef (_, args, body) =
  List.fold_right IdentSet.remove args (fv body)
