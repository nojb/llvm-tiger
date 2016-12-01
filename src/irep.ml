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
