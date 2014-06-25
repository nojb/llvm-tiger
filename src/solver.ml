(* The MIT License (MIT)

   Copyright (c) 2014 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

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

open Error

module S = Set.Make (String)
module M = Map.Make (String)

let add_list xts env =
  List.fold_left (fun env (x, t) -> M.add x t env) env xts

let union_list l =
  List.fold_left S.union S.empty l

let eqns : (string * S.t * string list) list ref = ref []
let reset () = eqns := []
let add_equation f s gs = eqns := (f, s, gs) :: !eqns
let solve () =
  let count = ref 0 in
  debug () "LL equations";
  List.iter (fun (f, s, gs) ->
    debug () "\t%s = {%s} u %s"
      f
      (String.concat " " (S.elements s))
      (String.concat " u " gs)) !eqns;
  let start = List.fold_left
    (fun m (f, s, _) -> M.add f s m) M.empty !eqns in
  let iter m =
    incr count;
    debug () "LL iteration %d" !count;
    List.fold_left (fun m (f, _, gs) ->
      let s' = M.find f m in
      let new_s' = union_list (s' :: List.map (fun g -> M.find g m) gs) in
      debug () "free vars for %s (%s): %s" f (String.concat " " gs)
        (String.concat " " (S.elements new_s'));
      M.add f (union_list (s' :: List.map (fun g -> M.find g m) gs)) m) m
      !eqns in
  let rec loop m =
    let m' = iter m in
    if M.equal S.equal m m' then
      begin debug () "LL fixpoint reached."; m' end
    else
      loop m'
  in loop start
