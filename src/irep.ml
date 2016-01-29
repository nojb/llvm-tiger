type ty =
  | Tnamed of string
  | Tpointer of ty
  | Tint of int

type primitive =
  | Paddint
  | Psubint
  | Pmulint
  | Pgep
  | Pload

type ident = int

type expression =
  | Iconst of int32
  | Iprim of primitive * expression list
  | Ivar of ident

type instruction_desc =
  | Ialloca of ident * ty
  | Istore of expression * expression
  | Iifthenelse of expression * instruction * instruction
  | Iloop of instruction
  | Icatch of instruction
  | Iexit of int
  | Iapply of ident * string * expression list
  | Iexternal of ident * string * expression list
  | Ireturn of expression option
  | Iend

and instruction =
  {
    desc: instruction_desc;
    next: instruction;
  }

let rec dummy_instr =
  { desc = Iend;
    next = dummy_instr }

let end_instr () =
  { desc = Iend;
    next = dummy_instr }

open Llvm

module IdentMap = Map.Make (struct type t = ident let compare = Pervasives.compare end)

let rec transl_ty m ty =
  match ty with
  | Tnamed name ->
      let c = module_context m in
      named_struct_type c name
  | Tpointer base ->
      pointer_type (transl_ty m ty)
  | Tint width ->
      let c = module_context m in
      integer_type c width

let transl_primitive env m b p args =
  match p, args with
  | Paddint, [v; w] ->
      build_add v w "" b
  | Pload, [v] ->
      build_load v "" b

let rec transl_expr env m b e =
  match e with
  | Iconst n ->
      let c = module_context m in
      const_of_int64 (i32_type c) (Int64.of_int32 n) false
  | Iprim (p, args) ->
      transl_primitive env m b p (List.map (transl_expr env m b) args)
  | Ivar id ->
      IdentMap.find id env

let rec transl_instr env m b i lexit l =
  match i.desc with
  | Ialloca (id, ty) ->
      let env = IdentMap.add id (build_alloca (transl_ty m ty) "" b) env in
      transl_instr env m b i.next lexit l
  | Istore (v, p) ->
      build_store (transl_expr env m b v) (transl_expr env m b p) b;
      transl_instr env m b i.next lexit l
  | Iifthenelse (e, ifso, ifnot) ->
      let c = module_context m in
      let f = block_parent (insertion_block b) in
      let lnext = append_block c "" f in
      let lifso = append_block c "" f in
      let lifnot = append_block c "" f in
      build_cond_br (transl_expr env m b e) lifso lifnot b;
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
      build_br lstart b;
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
      build_br (List.nth lexit i) b
  | Iend ->
      build_br l b
  | Ireturn (Some e) ->
      build_ret (transl_expr env m b e) b
  | Ireturn None ->
      build_ret_void b
