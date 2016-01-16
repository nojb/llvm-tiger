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

open Instruct

(* let resize_heap n = *)
(*   if n < mach.hp then assert false; *)
(*   let heap = Array.make n 0 in *)
(*   Array.blit mach.heap 0 heap 0 mach.hp; *)
(*   mach.heap <- heap *)

(* let resize_stack n = *)
(*   if n < mach.sp then assert false; *)
(*   let stack = Array.make n 0 in *)
(*   Array.blit mach.stack 0 stack 0 mach.sp; *)
(*   mach.stack <- stack *)

let run code startpc =
  let stop = ref false in
  let accu = ref 0 in
  let pc = ref startpc in
  let sp = ref 0 in
  let hp = ref 0 in
  let stack = [| |] in
  let heap = [| |] in
  while not !stop do
    let c = code.(!pc) in
    incr pc;
    match c with
    | Klabel _ -> ()
    | Kacc n ->
        accu := stack.(!sp - n)
    | Kpush ->
        sp := !sp + 1;
        stack.(!sp) <- accu
    | Kpop n ->
        sp := !sp - n
    | Kassign n ->
        stack.(!sp - n) <- !accu
    | Kconst (Const_int n) ->
        accu := n
    | Kmakeblock (sz, tag) ->
        heap.(!hp + 1) <- tag;
        accu := !hp + 2;
        hp := !hp + sz + 1
    | Kgetfield i ->
        accu := heap.(!accu + i)
    | Kbranch l ->
        pc := l
    | Kbranchif l ->
        if !accu != 0 then pc := l
    | Kbranchifnot l ->
        if !accu = 0 then pc := l
    | Kaddint ->
        accu := !accu + stack.(!sp);
        sp := !sp - 1
    | Kstop ->
        stop := true
  done

let run code lstart =
  let code = Array.of_list code in
  let h = Hashtbl.create 101 in
  for i = 0 to Array.length code - 1 do
    match code.(i) with
    | Klabel l -> Hashtbl.add h l (i+1);
    | _ -> ()
  done;
  for i = 0 to Array.length code - 1 do
    match code.(i) with
    | Kbranch l -> code.(i) <- Kbranch (Hashtbl.find h l)
    | Kbranchif l -> code.(i) <- Kbranchif (Hashtbl.find h l)
    | Kbranchifnot l -> code.(i) <- Kbranchifnot (Hashtbl.find h l)
    | _ -> ()
  done;
  let startpc = Hashtbl.find h lstart in
  run code startpc
