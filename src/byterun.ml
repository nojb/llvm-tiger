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

let rec run stack acc = function
  | Klabel _ :: k -> run stack acc k
  | Kacc n :: k -> run stack (access n stack) k
  | Kpush :: k -> run (acc :: stack) acc k
  | Kpop n :: k -> run (pop n stack) acc k
  | Kassign n :: k -> run (assign n acc stack) acc k
  | Kconst (Const_int n) :: k -> run stack n k
  | Kbranch l :: _ -> run stack acc (Hashtbl.find blocks l)
  | Kbranchif l :: k -> run stack acc (if acc != 0 then Hashtbl.find blocks l else k)
  | Kbranchifnot l :: k -> run stack acc (if acc != 0 then k else Hashtbl.find blocks l)
  | Kstop :: _ -> acc
  | [] -> failwith "run"

let run code lstart =
  let rec aux = function
    | Klabel l :: k -> Hashtbl.add blocks l k; aux k
    | _ :: k -> aux k
    | [] -> ()
  in
  aux code;
  run [] 0 (Hashtbl.find blocks lstart)
