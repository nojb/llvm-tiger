type ty =
  | Tvoid
  | Tstruct of ty list
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer of ty
  | Tint of int

type primitive =
  | Pconstint of int32
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep
  | Pload

type ident = int

type instruction_desc =
  | Ilet of ident * primitive * ident list
  | Ialloca of ident * ty
  | Istore of ident * ident
  | Iifthenelse of ident * instruction * instruction
  | Iloop of instruction
  | Icatch of instruction
  | Iexit of int
  | Iapply of ident * string * ident list
  | Iexternal of ident * string * ident list
  | Ireturn of ident option
  | Iend

and instruction =
  { desc: instruction_desc;
    next: instruction }

type fundecl =
  { name: string;
    args: ident list;
    signature: ty list * ty;
    body: instruction }

let rec dummy_instr =
  { desc = Iend;
    next = dummy_instr }

let end_instr () =
  { desc = Iend;
    next = dummy_instr }

let instr_seq = ref dummy_instr
let insert_instr desc = instr_seq := {desc; next = !instr_seq}

let extract () =
  let rec aux i next =
    if i == dummy_instr then
      next
    else
      aux i.next {i with next}
  in
  aux !instr_seq (end_instr ())

let extract_instr_seq f =
  let curr = !instr_seq in
  instr_seq := dummy_instr;
  match f () with
  | () ->
      let i = extract () in
      instr_seq := curr;
      i
  | exception e ->
      instr_seq := curr;
      raise e

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
      struct_type c (Array.of_list (List.map (transl_ty m) tys))
  | Tnamed name ->
      named_struct_type c name
  | Tpointer base ->
      pointer_type (transl_ty m ty)
  | Tint width ->
      integer_type c width

let transl_primitive env m b p args =
  match p, args with
  | Pconstint n, [] ->
      let c = module_context m in
      const_of_int64 (i32_type c) (Int64.of_int32 n) false
  | Paddint, [v; w] ->
      build_add v w "" b
  | Psubint, [v; w] ->
      build_sub v w "" b
  | Pmulint, [v; w] ->
      build_mul v w "" b
  | Pdivint, [v; w] ->
      build_sdiv v w "" b
  | Pload, [v] ->
      build_load v "" b
  | Pgep, v :: args ->
      build_gep v (Array.of_list args) "" b
  | _ ->
      assert false

let rec transl_instr env m b i lexit l =
  match i.desc with
  | Ilet (id, p, args) ->
      let args = List.map (fun id -> IdentMap.find id env) args in
      let env = IdentMap.add id (transl_primitive env m b p args) env in
      transl_instr env m b i.next lexit l
  | Ialloca (id, ty) ->
      let env = IdentMap.add id (build_alloca (transl_ty m ty) "" b) env in
      transl_instr env m b i.next lexit l
  | Istore (v, p) ->
      ignore (build_store (IdentMap.find v env) (IdentMap.find p env) b);
      transl_instr env m b i.next lexit l
  | Iifthenelse (e, ifso, ifnot) ->
      let c = module_context m in
      let f = block_parent (insertion_block b) in
      let lnext = append_block c "" f in
      let lifso = append_block c "" f in
      let lifnot = append_block c "" f in
      ignore (build_cond_br (IdentMap.find e env) lifso lifnot b);
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
  | Iapply (id, f, args) ->
      let f =
        match lookup_function f m with
        | None -> assert false
        | Some f -> f
      in
      let v = build_call f (Array.of_list (List.map (fun id -> IdentMap.find id env) args)) "" b in
      let env = IdentMap.add id v env in
      transl_instr env m b i.next lexit l
  | Iend ->
      ignore (build_br l b)
  | Ireturn (Some e) ->
      ignore (build_ret (IdentMap.find e env) b)
  | Ireturn None ->
      ignore (build_ret_void b)

let transl_fundecl_1 m f =
  let tys, ty = f.signature in
  let fty = function_type (transl_ty m ty) (Array.of_list (List.map (transl_ty m) tys)) in
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
  transl_instr IdentMap.empty m b f.body [] l

let transl_program m l =
  List.iter (transl_fundecl_1 m) l;
  List.iter (transl_fundecl_2 m) l
