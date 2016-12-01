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

type comparison =
  | Cle

type primitive =
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgetfield of int
  | Psetfield of int
  | Parrayref
  | Parrayset
  | Pintcomp of comparison
  | Pccall of string

type ident = string

type lambda =
  | Lvar of ident
  | Lconst of int64
  | Lapply of ident * lambda list
  | Llet of ident * lambda * lambda
  | Lletrec of (ident * lfunction) list * lambda
  | Lprim of primitive * lambda list
  | Lexit of int
  | Lcatch of lambda
  | Lifthenelse of lambda * lambda * lambda
  | Lsequence of lambda * lambda
  | Lloop of lambda
  | Lassign of ident * lambda

and lfunction =
  {
    name: ident;
    args: ident list;
    body: lambda;
  }

open Format

let rec print ppf = function
  | Lvar id ->
      pp_print_string ppf id
  | Lconst n ->
      fprintf ppf "%Ld" n
  | Lapply (f, args) ->
      let aux ppf = List.iter (fprintf ppf "@ %a" print) args in
      fprintf ppf "@[<2>(%s%t)@]" f aux
  | Llet (v, e1, e2) ->
      fprintf ppf "@[<2>(let %s@ %a@ %a)@]" v print e1 print e2
  | Lletrec (funs, e) ->
      let aux ppf args = List.iteri (fun i arg -> if i > 0 then fprintf ppf "@ "; pp_print_string ppf arg) args in
      let aux ppf =
        List.iter (fun (_, {name; args; body}) ->
            fprintf ppf "@ @[<2>(%s@ @[<2>(%a)@]@ %a)@]" name aux args print body
          ) funs
      in
      fprintf ppf "@[<2>(letrec%t@ %a)@]" aux print e
  | Lprim (_, args) ->
      let aux ppf = List.iter (fprintf ppf "@ %a" print) args in
      fprintf ppf "@[<2>(PRIM%t)@]" aux
  | Lexit n ->
      fprintf ppf "@[<2>(exit@ %d)@]" n
  | Lcatch e ->
      fprintf ppf "@[<2>(catch@ %a)@]" print e
  | Lifthenelse (e1, e2, e3) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" print e1 print e2 print e3
  | Lsequence (e1, e2) ->
      let rec aux ppf = function
        | Lsequence (e1, e2) -> fprintf ppf "%a@ %a" aux e1 aux e2
        | e -> print ppf e
      in
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" aux e1 aux e2
  | Lloop e ->
      fprintf ppf "@[<2>(loop@ %a)@]" print e
  | Lassign (v, e) ->
      fprintf ppf "@[<2>(assign@ %s@ %a)@]" v print e
