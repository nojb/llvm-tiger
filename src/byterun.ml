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
    mutable stack: int array;
    mutable heap: int array;
  }

let mach =
  {
    acc = 0;
    sp = 0;
    pc = 0;
    stack = [| |];
    heap = [| |];
  }

let push () =
  mach.stack.(mach.sp) <- mach.acc;
  mach.sp <- mach.sp + 1

let pop n =
  mach.sp <- mach.sp - n

let assign n =
  mach.stack.(mach.sp - n) <- mach.acc

let access n =
  mach.acc <- mach.stack.(mach.sp - n)

let rec run code =
  let c = code.(mach.pc) in
  mach.pc <- mach.pc + 1;
  match c with
  | Klabel _ -> run code
  | Kacc n -> access n; run code
  | Kpush -> push (); run code
  | Kpop n -> pop n; run code
  | Kassign n -> assign n; run code
  | Kconst (Const_int n) -> mach.acc <- n; run code
  | Kbranch l -> mach.pc <- l; run code
  | Kbranchif l -> if mach.acc != 0 then mach.pc <- l; run code
  | Kbranchifnot l -> if mach.acc = 0 then mach.pc <- l; run code
  | Kstop -> ()

let run code lstart =
  let codea = Array.of_list code in
  let h = Hashtbl.create 101 in
  for i = 0 to Array.length codea - 1 do
    match codea.(i) with
    | Klabel l -> Hashtbl.add h l (i+1);
    | _ -> ()
  done;
  for i = 0 to Array.length codea - 1 do
    match codea.(i) with
    | Kbranch l -> codea.(i) <- Kbranch (Hashtbl.find h l)
    | Kbranchif l -> codea.(i) <- Kbranchif (Hashtbl.find h l)
    | Kbranchifnot l -> codea.(i) <- Kbranchifnot (Hashtbl.find h l)
    | _ -> ()
  done;
  mach.pc <- Hashtbl.find h lstart;
  run codea
