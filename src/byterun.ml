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

let blocks = Hashtbl.create 7

let rec pop n stack =
  match n, stack with
  | 0, _ -> stack
  | n, _ :: stack -> pop (n-1) stack
  | _, [] -> failwith "pop"

let rec access n stack =
  match n, stack with
  | 0, x :: _ -> x
  | n, _ :: stack -> access (n-1) stack
  | _, [] -> failwith "access"

let rec assign n acc stack =
  match n, stack with
  | 0, _ :: stack -> acc :: stack
  | n, x :: stack -> x :: assign (n-1) acc stack
  | _, [] -> failwith "assign"

let get l =
  Hashtbl.find blocks l

type machine =
  {
    mutable acc: int;
    mutable sp: int;
    mutable stack: int array;
    mutable heap: int array;
  }

let mach =
  {
    acc = 0;
    sp = 0;
    stack = [| |];
    heap = [| |];
  }

let push () =
  mach.stack.(mach.sp) <- mach.acc;
  mach.sp <- mach.sp + 1

let pop () =
  mach.sp <- mach.sp - 1;
  mach.acc <- mach.stack.(mach.sp)

let assign n =
  mach.stack.(mach.sp - n) <- mach.acc

let access n =
  mach.acc <- mach.stack.(mach.sp - n)

let rec run = function
  | Klabel _ :: k -> run k
  | Kacc n :: k -> access n; run k
  | Kpush :: k -> push (); run k
  | Kpop n :: k -> pop (); run k
  | Kassign n :: k -> assign n; run k
  | Kconst (Const_int n) :: k -> mach.acc <- n; run k
  | Kbranch l :: _ -> run (get l)
  | Kbranchif l :: k -> run  (if mach.acc != 0 then get l else k)
  | Kbranchifnot l :: k -> run (if mach.acc != 0 then k else get l)
  | Kstop :: _ -> ()
  | [] -> failwith "run"

let run code lstart =
  let rec aux = function
    | Klabel l :: k -> Hashtbl.add blocks l k; aux k
    | _ :: k -> aux k
    | [] -> ()
  in
  aux code;
  run (Hashtbl.find blocks lstart)
