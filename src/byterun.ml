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

type machine =
  {
    mutable acc: int;
    mutable sp: int;
    mutable pc: int;
    mutable hp: int;
    mutable stack: int array;
    mutable heap: int array;
    mutable code: instruction array;
  }

let mach =
  {
    acc = 0;
    sp = 0;
    pc = 0;
    hp = 0;
    stack = [| |];
    heap = [| |];
    code = [| |];
  }

let resize_heap n =
  if n < mach.hp then assert false;
  let heap = Array.make n 0 in
  Array.blit mach.heap 0 heap 0 mach.hp;
  mach.heap <- heap

let resize_stack n =
  if n < mach.sp then assert false;
  let stack = Array.make n 0 in
  Array.blit mach.stack 0 stack 0 mach.sp;
  mach.stack <- stack

let push () =
  mach.stack.(mach.sp) <- mach.acc;
  mach.sp <- mach.sp + 1

let pop n =
  mach.sp <- mach.sp - n

let assign n =
  mach.stack.(mach.sp - n) <- mach.acc

let access n =
  mach.acc <- mach.stack.(mach.sp - n)

let make_block sz tag =
  mach.heap.(mach.hp) <- tag;
  mach.acc <- mach.hp + 1;
  mach.hp <- mach.hp + sz + 1

let run () =
  let stop = ref false in
  while not !stop do
    let c = mach.code.(mach.pc) in
    mach.pc <- mach.pc + 1;
    match c with
    | Klabel _ -> ()
    | Kacc n -> access n
    | Kpush -> push ()
    | Kpop n -> pop n
    | Kassign n -> assign n
    | Kconst (Const_int n) -> mach.acc <- n
    | Kmakeblock (sz, tag) -> make_block sz tag (* CHECK *)
    | Kgetfield i -> mach.acc <- mach.heap.(mach.acc + i)
    | Kbranch l -> mach.pc <- l
    | Kbranchif l -> if mach.acc != 0 then mach.pc <- l
    | Kbranchifnot l -> if mach.acc = 0 then mach.pc <- l
    | Kstop -> stop := true
  done

let run code lstart =
  mach.code <- Array.of_list code;
  let h = Hashtbl.create 101 in
  for i = 0 to Array.length mach.code - 1 do
    match mach.code.(i) with
    | Klabel l -> Hashtbl.add h l (i+1);
    | _ -> ()
  done;
  for i = 0 to Array.length mach.code - 1 do
    match mach.code.(i) with
    | Kbranch l -> mach.code.(i) <- Kbranch (Hashtbl.find h l)
    | Kbranchif l -> mach.code.(i) <- Kbranchif (Hashtbl.find h l)
    | Kbranchifnot l -> mach.code.(i) <- Kbranchifnot (Hashtbl.find h l)
    | _ -> ()
  done;
  mach.pc <- Hashtbl.find h lstart;
  run ()
