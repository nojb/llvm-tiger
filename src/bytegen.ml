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

open Lambda
open Instruct

let label_num = ref (-1)

let new_label () =
  incr label_num;
  !label_num

let label_code k =
  match k with
  | Klabel l :: _ ->
      k, l
  | _ ->
      let l = new_label () in
      Klabel l :: k, l

let add_var id sz env =
  (id, sz) :: env

let rec pop n k =
  if n = 0 then k
  else begin
    match k with
    | Kpop m :: k -> pop (n+m) k
    | _ -> Kpop n :: k
  end

let rec goto l k =
  match k with
  | [] -> [Kbranch l]
  | Klabel _ :: _ -> Kbranch l :: k
  | _ :: k -> goto l k

let rec compile env e brk sz k =
  match e with
  | Lconst c ->
      Kconst c :: k
  | Lifthenelse (e1, e2, e3) ->
      let kk, lk = label_code k in
      let k3, l3 = label_code (compile env e3 brk sz kk) in
      compile env e1 brk sz (Kbranchifnot l3 :: compile env e2 brk sz (Kbranch lk :: k3))
  | Lwhile (e1, e2) ->
      let k, lend = label_code k in
      let ltest = new_label () in
      Klabel ltest :: compile env e1 brk sz
        (Kbranchifnot lend :: compile env e2 brk sz (Kbranch ltest :: k))
  | Lstaticcatch e ->
      let k, l = label_code k in
      compile env e (l, sz) sz k
  | Lstaticfail ->
      let lexit, sz' = brk in
      pop (sz - sz') (goto lexit k)
  | Llet (id, e1, e2) ->
      (* CHECK add_var +1 *)
      compile env e1 brk sz (Kpush :: compile (add_var id (sz+1) env) e2 brk (sz+1) (pop 1 k))
  | Lsequence (e1, e2) ->
      compile env e1 brk sz (compile env e2 brk sz k)
