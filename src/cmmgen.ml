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

open Tabs
open Typedtree
open Cmm

let last_bid = ref (-1)

let mkblock c =
  incr last_bid;
  {
    bid = !last_bid;
    bcode = c;
  }

let rec compile_var env v k =
  match v.tvar_desc with
  | Tsimple id ->
      k (Cvar id.stamp)
  | Tindex (v, e) ->
      compile_var env v
        (fun v ->
           compile env e
             (fun e ->
                k (Cop (Cgep, [Cop (Cload, [v]); e]))))
  | Tfield (v, i) ->
      compile_var env v
        (fun v ->
           k (Cop (Cgep, [Cop (Cload, [v]); Cint (Int32.of_int i)])))

and compile env e k =
  match e.texp_desc with
  | Tunit ->
      k (Cint 0l)
  | Tint n ->
      k (Cint (Int32.of_int n))
  | Tnil ->
      k (Cint 0l)
  | Tvar v ->
      compile_var env v (fun v -> k (Cop (Cload, [v])))
  | Tassign (v, e) ->
      compile_var env v
        (fun v ->
           compile env e
             (fun e ->
                Cstore (v, e, k (Cint 0l))))
  | Tseq (e1, e2) ->
      compile env e1 (fun _ -> compile env e2 k)
  | Tif (e1, e2, e3) when type_equal e2.texp_type void_ty ->
      let b = mkblock (k (Cint 0l)) in
      let b2 = mkblock (compile env e2 (fun _ -> Cgoto b)) in
      let b3 = mkblock (compile env e3 (fun _ -> Cgoto b)) in
      compile env e1 (fun e1 -> Cifthenelse (e1, b2, b3))
  | Tif (e1, e2, e3) ->
      let id = (-1) in (* CHECK *)
      let b = mkblock (k (Cop (Cload, [Cvar id]))) in
      let b2 = mkblock (compile env e2 (fun e -> Cstore (Cvar id, e, Cgoto b))) in
      let b3 = mkblock (compile env e3 (fun e -> Cstore (Cvar id, e, Cgoto b))) in
      compile env e1 (fun e1 -> Cifthenelse (e1, b2, b3))
  | Twhile (e1, e2) ->
      let b3 = mkblock (k (Cint 0l)) in
      let rec b = {bid = 3; bcode = Cgoto b} in
      let b2 = {bid = 6; bcode = compile env e2 (fun _ -> Cgoto b)} in
      b.bcode <- compile env e1 (fun e1 -> Cifthenelse (e1, b2, b3));
      Cgoto b
  | Tbreak ->
      Cgoto env
  | Tlet (id, e1, e2) ->
      Calloca (id.name, assert false, compile env e1 (fun e1 -> Cstore (Cvar id.stamp, e1, compile env e2 k)))
