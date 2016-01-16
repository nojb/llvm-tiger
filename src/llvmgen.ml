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

open Cmm
open Llvm

type env =
  {
    blocks: (int, llbasicblock) Hashtbl.t;
    builder: llbuilder;
    context: llcontext;
    variables: (int, llvalue) Hashtbl.t;
  }

let rec compile_op env op args =
  match op, args with
  | Cload, [e] ->
      build_load (compile_expr env e) "" env.builder

and compile_expr env = function
  | Cint n ->
      const_int (i32_type env.context) (Int32.to_int n)
  | Cvar i ->
      Hashtbl.find env.variables i

let rec compile_code env = function
  | Cstore (e1, e2, c) ->
      build_store (compile_expr env e2) (compile_expr env e1) env.builder;
      compile_code env c
  | Cgoto b ->
      let bb = Hashtbl.find env.blocks b.bid in
      build_br bb env.builder
  | Cifthenelse (e1, b2, b3) ->
      let bb2 = Hashtbl.find env.blocks b2.bid in
      let bb3 = Hashtbl.find env.blocks b3.bid in
      build_cond_br (compile_expr env e1) bb2 bb3 env.builder
  | Creturn None ->
      build_ret_void env.builder
  | Creturn (Some e) ->
      build_ret (compile_expr env e) env.builder

let compile _ =
  create_module (global_context ())
