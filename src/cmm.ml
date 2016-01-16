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

type ty =
  | Tint of int
  | Tptr of ty

type operation =
  | Caddint
  | Csubint
  | Cmulint
  | Cgep
  | Cload

type ident = int

type expr =
  | Cint of int32
  | Cop of operation * expr list
  | Cvar of ident

type code =
  | Calloca of ident * ty * code
  | Cstore of expr * expr * code
  | Cgoto of block
  | Cifthenelse of expr * block * block
  | Capply of ident * string * expr list * code
  | Cexternal of ident * string * expr list * code
  | Creturn of expr option

and block =
  {
    bid: int;
    mutable bcode: code;
  }

let tbl : (int, unit) Hashtbl.t = Hashtbl.create 3

open Format

let rec print_expr ppf = function
  | Cvar i ->
      fprintf ppf "x%i" i

let rec print_code ppf = function
  | Calloca (id, t, c) ->
      fprintf ppf "\tx%i = alloca\n" id;
      print_code ppf c
  | Cstore (e1, e2, c) ->
      fprintf ppf "\tstore %a, %a\n" print_expr e1 print_expr e2;
      print_code ppf c
  | Cgoto b ->
      print ppf b

and print ppf b =
  if Hashtbl.mem tbl b.bid then begin
    fprintf ppf "\tgoto L%i\n" b.bid
  end else begin
    Hashtbl.add tbl b.bid;
    fprintf ppf "L%i:";
    print_code ppf b.bcode
  end
