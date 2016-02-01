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
  | Tvoid
  | Tstruct of ty array
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer of ty
  | Tint of int

type comparison =
  | Cleq

type signature = ty array * ty

type operation =
  | Pconstint of int32
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep
  | Pload
  | Pcmpint of comparison
  | Ialloca of ty
  | Istore
  | Iapply of string
  | Iexternal of string * signature

type ident = int

type instruction_desc =
  | Iop of operation
  | Iifthenelse of instruction * instruction
  | Iloop of instruction
  | Icatch of instruction
  | Iexit of int
  | Ireturn of bool
  | Iend

and instruction =
  { desc: instruction_desc;
    arg: ident array;
    res: ident array;
    next: instruction }

let rec dummy_instr =
  { desc = Iend;
    arg = [||];
    res = [||];
    next = dummy_instr }

let end_instr () =
  { desc = Iend;
    arg = [||];
    res = [||];
    next = dummy_instr }

let rec print_typ ppf ty =
  let open Format in
  match ty with
  | Tint w -> fprintf ppf "i%i" w
  | Tpointer t -> fprintf ppf "p%a" print_typ t
  | Tarray (t, n) -> fprintf ppf "a%i%a" n print_typ t
  | Tnamed s -> fprintf ppf "%s" s
  | Tvoid -> fprintf ppf "void"

let print_args ppf arg =
  let open Format in
  for i = 0 to Array.length arg - 1 do
    if i > 0 then fprintf ppf ", ";
    fprintf ppf "x%i" arg.(i)
  done

let print_operation ppf op arg res =
  let open Format in
  match op with
  | Pconstint n ->
      fprintf ppf "%li" n
  | Paddint ->
      fprintf ppf "x%i + x%i" arg.(0) arg.(1)
  | Psubint ->
      fprintf ppf "x%i - x%i" arg.(0) arg.(1)
  | Pmulint ->
      fprintf ppf "x%i * x%i" arg.(0) arg.(1)
  | Pdivint ->
      fprintf ppf "x%i / x%i" arg.(0) arg.(1)
  | Pgep ->
      fprintf ppf "gep x%i, ..." arg.(0)
  | Pload ->
      fprintf ppf "!x%i" arg.(0)
  | Pcmpint _ ->
      fprintf ppf "cmp"
  | Ialloca ty ->
      fprintf ppf "x%i = alloca %a" arg.(0) print_typ ty
  | Istore ->
      fprintf ppf "x%i := x%i" arg.(0) arg.(1)
  | Iapply (f)
  | Iexternal (f, _) ->
      fprintf ppf "x%i = %s(%a)" arg.(0) f print_args arg

let rec print_instruction ppf i =
  let open Format in
  begin match i.desc with
    | Iop op ->
        print_operation ppf op i.arg i.res
    | Iifthenelse (ifso, ifnot) ->
        fprintf ppf "@[<v 2>if x%i then@,%a" i.arg.(0) print_instruction ifso;
        fprintf ppf "@;<0 -2>else@,%a" print_instruction ifnot;
        fprintf ppf "@;<0 -2>endif@]"
    | Iloop body ->
        fprintf ppf "@[<v 2>loop@,%a" print_instruction body;
        fprintf ppf "@;<0 -2>endloop@]"
    | Icatch body ->
        fprintf ppf "@[<v 2>catch@,%a" print_instruction body;
        fprintf ppf "@;<0 -2>endcatch@]"
    | Iexit i ->
        fprintf ppf "exit %i" i
    | Ireturn false ->
        fprintf ppf "ret"
    | Ireturn true ->
        fprintf ppf "ret x%i" i.arg.(0)
    | Iend ->
        ()
  end;
  match i.next.desc with
  | Iend ->
      ()
  | _ ->
      fprintf ppf "@,%a" print_instruction i.next

let print_instruction ppf i =
  Format.fprintf ppf "@[<v>%a@]@." print_instruction i

type fundecl =
  { name: string;
    args: ident array;
    signature: signature;
    body: instruction }

let print_fundecl ppf f =
  let open Format in
  fprintf ppf "@[<v>%s(%a):@,%a@]@." f.name print_args f.args print_instruction f.body

open Llvm

module IdentMap = Map.Make (struct type t = ident let compare = Pervasives.compare end)

let rec transl_ty m ty =
  let c = module_context m in
  match ty with
  | Tvoid ->
      void_type c
  | Tarray (ty, len) ->
      array_type (transl_ty m ty) len
  | Tstruct tys ->
      struct_type c (Array.map (transl_ty m) tys)
  | Tnamed name ->
      named_struct_type c name
  | Tpointer base ->
      pointer_type (transl_ty m base)
  | Tint width ->
      integer_type c width

let transl_operation env m b op arg =
  match op with
  | Pconstint n ->
      let c = module_context m in
      [|const_of_int64 (i32_type c) (Int64.of_int32 n) false|]
  | Paddint ->
      [|build_add arg.(0) arg.(1) "" b|]
  | Psubint ->
      [|build_sub arg.(0) arg.(1) "" b|]
  | Pmulint ->
      [|build_mul arg.(0) arg.(1) "" b|]
  | Pdivint ->
      [|build_sdiv arg.(0) arg.(1) "" b|]
  | Pload ->
      [|build_load arg.(0) "" b|]
  | Pgep ->
      [|build_gep arg.(0) (Array.sub arg 1 (Array.length arg - 1)) "" b|]
  | Ialloca (ty) ->
      [|build_alloca (transl_ty m ty) "" b|]
  | Istore ->
      ignore (build_store arg.(0) arg.(1) b);
      [||]
  | Iapply (f) ->
      let f =
        match lookup_function f m with
        | None -> assert false
        | Some f -> f
      in
      [|build_call f arg "" b|]
  | Iexternal (f, (tys, ty)) ->
      let f =
        declare_function f (function_type (transl_ty m ty) (Array.map (transl_ty m) tys)) m
      in
      [|build_call f arg "" b|]
  | _ ->
      assert false

let rec transl_instr env m b i lexit l =
  match i.desc with
  | Iop op ->
      let arg = Array.map (fun id -> IdentMap.find id env) i.arg in
      let res = transl_operation env m b op arg in
      let env = ref env in
      for n = 0 to Array.length res - 1 do
        env := IdentMap.add i.res.(n) res.(n) !env
      done;
      transl_instr !env m b i.next lexit l
  | Iifthenelse (ifso, ifnot) ->
      let c = module_context m in
      let f = block_parent (insertion_block b) in
      let lnext = append_block c "" f in
      let lifso = append_block c "" f in
      let lifnot = append_block c "" f in
      ignore (build_cond_br (IdentMap.find i.arg.(0) env) lifso lifnot b);
      position_at_end lifso b;
      transl_instr env m b ifso lexit lnext;
      position_at_end lifnot b;
      transl_instr env m b ifnot lexit lnext;
      position_at_end lnext b;
      transl_instr env m b i.next lexit l
  | Iloop body ->
      let c = module_context m in
      let f = block_parent (insertion_block b) in
      let lstart = append_block c "" f in
      ignore (build_br lstart b);
      position_at_end lstart b;
      transl_instr env m b body lexit lstart
  | Icatch body ->
      let c = module_context m in
      let f = block_parent (insertion_block b) in
      let lnext = append_block c "" f in
      transl_instr env m b body (lnext :: lexit) lnext;
      position_at_end lnext b;
      transl_instr env m b i.next lexit l
  | Iexit i ->
      ignore (build_br (List.nth lexit i) b)
  | Iend ->
      ignore (build_br l b)
  | Ireturn true ->
      ignore (build_ret (IdentMap.find i.arg.(0) env) b)
  | Ireturn false ->
      ignore (build_ret_void b)

let transl_fundecl_1 m f =
  let tys, ty = f.signature in
  let fty = function_type (transl_ty m ty) (Array.map (transl_ty m) tys) in
  ignore (define_function f.name fty m)

let transl_fundecl_2 m f =
  let v =
    match lookup_function f.name m with
    | None -> assert false
    | Some v -> v
  in
  let c = module_context m in
  let b = builder c in
  let l = entry_block v in
  position_at_end l b;
  let env = ref IdentMap.empty in
  for n = 0 to Array.length f.args - 1 do
    env := IdentMap.add f.args.(n) (param v n) !env
  done;
  transl_instr !env m b f.body [] l

let transl_program m l =
  List.iter (transl_fundecl_1 m) l;
  List.iter (transl_fundecl_2 m) l
