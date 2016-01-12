(* The MIT License (MIT)

   Copyright (c) 2013-2014 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

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
open Tabs

let tmp_counter = ref (-1)

let gentmp s =
  incr tmp_counter;
  s ^ "__" ^ (string_of_int !tmp_counter)

type type_spec =
  | VOID
  | INT
  | STRING
  | ARRAY   of string * type_spec
  | RECORD  of string * (string * type_spec) list
  | NAME    of string

let rec string_of_type = function
  | VOID          -> "void"
  | INT           -> "int"
  | STRING        -> "string"
  | ARRAY (x, _)
  | RECORD (x, _)
  | NAME x        -> x

let describe_type = function
  | VOID      -> "void"
  | INT       -> "int"
  | STRING    -> "string"
  | ARRAY _   -> "array"
  | RECORD _  -> "record"
  | NAME x    -> "named type " ^ x

type var_info =
  {
    vtype : type_spec;
    vimm : bool;
    (* v_alloca : llvalue *)
  }

type fun_info =
  {
    fname : string;
    fsign : type_spec list * type_spec;
    f_user : bool;
    (* f_llvalue : llvalue Lazy.t *)
  }

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

(* type loop_flag = *)
(*   | NoLoop *)
(*   | InLoop of llbasicblock *)

type env =
  {
    venv : value_desc M.t;
    tenv : type_spec M.t;
    (* in_loop : loop_flag; *)
    (* used for lambda lifting *)
    (* sols : S.t M.t *)
  }

let rec base_type env = function
  | NAME x -> base_type env (M.find x env.tenv)
  | _ as t -> t

let type_equal env t1 t2 =
  base_type env t1 == base_type env t2

let empty_env =
  {
    venv = M.empty;
    tenv = M.empty;
    (* in_loop = NoLoop; *)
    (* sols = M.empty *)
  }

let find_var id env =
  try
    match M.find id.s env.venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with
    Not_found ->
      error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?immutable:(immut=false) t llv env =
  let vi = { vtype = t; vimm = immut; (* v_alloca = llv *) } in
  { env with venv = M.add x.s (Variable vi) env.venv }

let mem_var x env =
  try match M.find x env.venv with
  | Variable _ -> true
  | Function _ -> false
  with Not_found -> false

let add_fun x uid atyps rtyp llv env =
  let fi =
    {
      fname = uid;
      fsign = atyps, rtyp;
      f_user = true;
      (* f_llvalue = lazy llv *)
    }
  in
  { env with venv = M.add x.s (Function fi) env.venv }

let mem_user_fun x env =
  try match M.find x env.venv with
  | Function fi -> fi.f_user
  | Variable _ -> false
  with Not_found -> false

let find_fun x env =
  try
    match M.find x.s env.venv with
    | Variable _ -> raise Not_found
    | Function fi -> fi
  with
    Not_found ->
      error x.p "unbound function '%s'" x.s

(* type tenv = (string * E.typ) list *)

let find_type x env =
  try
    M.find x.s env.tenv
  with Not_found ->
    error x.p "unbound type '%s'" x.s

let add_type x t env =
  { env with tenv = M.add x.s t env.tenv }

let find_array_type x env =
  match base_type env (find_type x env) with
  | ARRAY (_, t') as t -> t, t'
  | _ as t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s
        (describe_type t)

let find_record_type env x =
  match base_type env (find_type x env) with
  | RECORD (_, xts) as t -> t, xts
  | _ as t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s
        (describe_type t)

let find_record_field env t (x : pos_string) =
  let t, xts = match base_type env t with RECORD (t, xts) -> t, xts | _ -> assert false in
  (* let ts = M.find t env.renv in *)
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in loop 0 xts

(* * LLVM Utils *)

(* type llvm_value = *)
(*   | VAL of llvalue *)
(*   | LOADVAL of llvalue *)

(* let g_context = global_context () *)
(* let g_module  = create_module g_context "" *)
(* let g_builder = builder g_context *)

(* let new_block () = *)
(*   (\* this assumes that the builder is already set up *)
(*    * inside a function *\) *)
(*   let f = block_parent (insertion_block g_builder) in *)
(*   append_block g_context "" f *)

(* let llvm_value = function *)
(*   | VAL v -> v *)
(*   | LOADVAL v -> build_load v "" g_builder *)

(* let dump_llvm_value = function *)
(*   | VAL v *)
(*   | LOADVAL v -> dump_value v *)

(* let int_t w = *)
(*   integer_type g_context w *)

(* let void_t = *)
(*   void_type g_context *)

(* let ptr_t t = *)
(*   pointer_type t *)

(* let struct_t fields = *)
(*   struct_type g_context fields *)

(* let const_int0 w n = *)
(*   const_int (int_t w) n *)

(*   (\* This one shadows Llvm.const_int *\) *)
(* let const_int w n = *)
(*   VAL (const_int (int_t w) n) *)

(* let const_null0 = *)
(*   const_null *)

(* let const_null t = *)
(*   VAL (const_null t) *)

(* let size_of t = (\* shadows Llvm.size_of *\) *)
(*   VAL (size_of t) *)

(* let malloc v = *)
(*   build_call (declare_function "malloc" *)
(*     (function_type (ptr_t (int_t 8)) [| int_t Sys.word_size  |]) g_module) *)
(*     [| llvm_value v |] "" g_builder *)

(* let gc_alloc v = *)
(*   build_call (declare_function "llvm_gc_allocate" *)
(*     (function_type (ptr_t (int_t 8)) [| int_t Sys.word_size  |]) g_module) *)
(*     [| llvm_value v |] "" g_builder *)

(* let gc_alloc_type t = *)
(*   dump_llvm_value (size_of t); *)
(*   let v = build_call (declare_function "llvm_gc_allocate" *)
(*     (function_type (ptr_t (int_t 8)) [| int_t Sys.word_size  |]) g_module) *)
(*     [| llvm_value (size_of t) |] "" g_builder in *)
(*   build_pointercast v (ptr_t t) "" g_builder *)

(* let alloca is_ptr ty = *)
(*   let b = builder_at_end g_context *)
(*     (entry_block (block_parent (insertion_block g_builder))) in *)
(*   let a = build_alloca ty "" b in *)
(*   if is_ptr then begin *)
(*     let v = build_pointercast a (ptr_t (ptr_t (int_t 8))) "" b in *)
(*     ignore (build_call (declare_function "llvm.gcroot" *)
(*       (function_type void_t [| ptr_t (ptr_t (int_t 8)); ptr_t (int_t 8) |]) *)
(*       g_module) [| v; const_null0 (ptr_t (int_t 8)) |] "" b) *)
(*   end; *)
(*   a *)

(* let add v1 v2 = *)
(*   VAL (build_add (llvm_value v1) (llvm_value v2) "" g_builder) *)

(* let mul v1 v2 = *)
(*   VAL (build_mul (llvm_value v1) (llvm_value v2) "" g_builder) *)

(* let load v = *)
(*   VAL (build_load (llvm_value v) "" g_builder) *)

(* let nil = *)
(*   const_int 32 0 *)

(* let store v p = *)
(*   ignore (build_store (llvm_value v) (llvm_value p) g_builder) *)

(* let gep v vs = *)
(*   VAL (build_gep (llvm_value v) *)
(*     (Array.of_list (List.map llvm_value vs)) "" g_builder) *)

(* let binop op v1 v2 = *)
(*   VAL (op (llvm_value v1) (llvm_value v2) "" g_builder) *)

(* let unop op v = *)
(*   VAL (op (llvm_value v) "" g_builder) *)

(* let call v0 vs = *)
(*   VAL (build_call v0 (Array.of_list (List.map llvm_value vs)) "" g_builder) *)

(* let phi incoming = *)
(*   VAL (build_phi *)
(*     (List.map (fun (v, bb) -> llvm_value v, bb) incoming) "" g_builder) *)

(* let cond_br c yaybb naybb = *)
(*   ignore (build_cond_br (llvm_value c) yaybb naybb g_builder) *)

(* let array_length_addr v = *)
(*   gep v [ const_int 32 0; const_int 32 0 ] *)

(* let strcmp v1 v2 = *)
(*   VAL (build_call (declare_function "strcmp" *)
(*     (function_type (int_t 32) *)
(*       [| ptr_t (int_t 8); ptr_t (int_t 8) |]) g_module) *)
(*     [| llvm_value v1; llvm_value v2 |] "" g_builder) *)

(* let printf msg = *)
(*   ignore (build_call (declare_function "printf" *)
(*     (var_arg_function_type (int_t 32) [| ptr_t (int_t 8) |]) *)
(*     g_module) [| build_global_stringptr msg "" g_builder |] "" g_builder) *)

(* let die msg = *)
(*   printf msg; *)
(*   ignore (build_call (declare_function "exit" *)
(*     (function_type void_t [| int_t 32 |]) g_module) [| const_int0 32 2 |] "" *)
(*     g_builder); *)
(*   ignore (build_unreachable g_builder) *)

(* let array_index lnum v x = *)
(*   let v = VAL (llvm_value v) in *)
(*   let yesbb = new_block () in *)
(*   let diebb = new_block () in *)
(*   let l = load (array_length_addr v) in *)
(*   let c1 = binop (build_icmp Icmp.Sle) x l in *)
(*   let c2 = binop (build_icmp Icmp.Sge) x (const_int 32 0) in *)
(*   let c = binop build_and c1 c2 in *)
(*   cond_br c yesbb diebb; *)
(*   position_at_end diebb g_builder; *)
(*   die (Printf.sprintf "Runtime error: index out of bounds in line %d\n" lnum); *)
(*   position_at_end yesbb g_builder; *)
(*   gep v [ const_int 32 0; const_int 32 1; x ] *)

(* let record_index lnum v i = *)
(*   let v = VAL (llvm_value v) in *)
(*   let yesbb = new_block () in *)
(*   let diebb = new_block () in *)
(*   let ptr = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in *)
(*   let c = binop (build_icmp Icmp.Ne) ptr (const_int Sys.word_size 0) in *)
(*   cond_br c yesbb diebb; *)
(*   position_at_end diebb g_builder; *)
(*   die (Printf.sprintf *)
(*     "Runtime error: field access to nil record in line %d\n" lnum); *)
(*   position_at_end yesbb g_builder; *)
(*   gep v [ const_int 32 0; const_int 32 i ] *)

(* let save triggers v = *)
(*   if triggers then *)
(*     match v with *)
(*     | LOADVAL _ -> v *)
(*     | VAL v -> *)
(*         let a = alloca true (type_of v) in *)
(*         ignore (build_store v a g_builder); *)
(*         LOADVAL a *)
(*   else *)
(*     v *)

(* let named_structs : (type_spec * Llvm.lltype) list ref = ref [] *)

(* let rec transl_typ env t = *)
(*   let rec loop t = *)
(*     match t with *)
(*     | VOID    -> int_t 32 *)
(*     | INT     -> int_t 32 *)
(*     | STRING  -> pointer_type (int_t 8) *)
(*     | ARRAY (_, t) -> (\* { i32, [0 x t] }* *\) *)
(*         ptr_t (struct_t [| int_t 32; array_type (loop t) 0 |]) *)
(*     | RECORD (x, xts) -> *)
(*         if not (List.mem_assq t !named_structs) then begin *)
(*           let ty = named_struct_type g_context x in *)
(*           named_structs := (t, ty) :: !named_structs; *)
(*           struct_set_body ty *)
(*             (Array.of_list (List.map (fun (_, t) -> loop t) xts)) *)
(*             false *)
(*         end; *)
(*         pointer_type (List.assq t !named_structs) *)
(*     | NAME y -> *)
(*         loop (M.find y env.tenv) *)
(*   in loop t *)

let declare_type env (x, t) =
  let find_type y env =
    try M.find y.s env.tenv
    with Not_found -> NAME y.s in
  match t with
  | Tname y ->
      add_type x (find_type y env) env
  | Tarray y ->
      add_type x (ARRAY (x.s, find_type y env)) env
  | Trecord xs ->
      add_type x (RECORD (x.s, List.map (fun (x, t) -> x.s, find_type t env) xs)) env

let check_unique_type_names xts =
  let rec bind = function
    | [] -> ()
    | (x, _) :: xts ->
        let matches = List.filter (fun (x', _) -> x.s = x'.s) xts in
        if List.length matches > 0 then
          let (x', _) = List.hd matches in
          error x'.p
            "type name '%s' can only be defined once in each type declaration"
            x.s
        else
          bind xts
  in bind xts

let check_type env (x, _) =
  let visited = ref [] in
  let rec loop thru_record t =
    if List.memq t !visited then
      if thru_record then ()
      else error x.p "type declaration cycle does not pass through record type"
    else begin
      visited := t :: !visited;
      match t with
      | VOID
      | INT
      | STRING -> ()
      | ARRAY (_, t) ->
          loop thru_record t
      | RECORD (_, xts) ->
          List.iter (fun (_, t) -> loop true t) xts
      | NAME y ->
          begin try
            loop thru_record (M.find y env.tenv)
          with
            Not_found -> error x.p "unbound type '%s'" y
            (* FIXME x.p != position of y in general *)
          end
    end
  in loop false (M.find x.s env.tenv)

let let_type env tys =
  check_unique_type_names tys;
  let env = List.fold_left declare_type env tys in
  List.iter (check_type env) tys;
  env

(** ----------------------------------------- *)

let rec structured_type env t =
  match t with
  | NAME y -> structured_type env (M.find y env.tenv)
  | STRING
  | ARRAY _
  | RECORD _ -> true
  | _ -> false

(* These utility functions are used in the processing of function definitions *)

let check_unique_fundef_names fundefs =
  let rec bind = function
    | [] -> ()
    | fundef :: fundefs ->
        let matches =
          List.filter (fun fundef' -> fundef.fn_name.s = fundef'.fn_name.s)
          fundefs in
        if List.length matches > 0 then
          let fundef' = List.hd matches in
          error fundef'.fn_name.p
            "function name '%s' can only be defined once in each type declaration"
            fundef'.fn_name.s
        else
          bind fundefs
  in bind fundefs

let tr_return_type env fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t env

(* let llvm_return_type env = function *)
(*   | VOID -> void_t *)
(*   | t -> transl_typ env t *)

(* let tr_function_header env fn = *)
(*   let type_of_free_var env x = *)
(*     match M.find x env.venv with *)
(*     | Variable vi -> *)
(*         if vi.vimm then transl_typ env vi.vtype *)
(*         else pointer_type (transl_typ env vi.vtype) *)
(*     | Function _ -> assert false in *)
(*   let free_vars = S.elements (M.find fn.fn_name.s env.sols) in *)
(*   let free_vars = List.map (fun x -> (x, type_of_free_var env x)) *)
(*     free_vars in *)
(*   let rtyp = tr_return_type env fn in *)
(*   let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in *)
(*   let uid = gentmp fn.fn_name.s in *)
(*   let llv = define_function uid *)
(*     (function_type (llvm_return_type env rtyp) *)
(*       (Array.of_list (List.map snd free_vars @ *)
(*       (List.map (transl_typ env) argst)))) g_module in *)
(*   set_linkage Linkage.Internal llv; *)
(*   set_gc (Some "shadow-stack") llv; *)
(*   let env' = add_fun fn.fn_name uid argst *)
(*     rtyp llv env in *)
(*   env' *)

(* let rec tr_function_body env fundef = *)
(*   let add_free_var env x llv = *)
(*     match M.find x env.venv with *)
(*     | Variable vi -> *)
(*         { env with venv = *)
(*           M.add x (Variable {vi with v_alloca = llv}) env.venv } *)
(*     | Function _ -> assert false in *)

  (* let fi = find_fun fundef.fn_name env in *)
  (* let ts, t = fi.fsign in *)

  (* position_at_end (entry_block (Lazy.force fi.f_llvalue)) g_builder; *)
  (* let startbb = new_block () in *)
  (* position_at_end startbb g_builder; *)
  (* let count = ref (-1) in *)

  (* (\* Process arguments *\) *)
  (* let env = List.fold_left (fun env x -> *)
  (*   incr count; *)
  (*   let f_llvalue = Lazy.force fi.f_llvalue in *)
  (*   set_value_name x (param f_llvalue !count); *)
  (*   add_free_var env x (param f_llvalue !count)) *)
  (*   env (S.elements (M.find fundef.fn_name.s env.sols)) in *)
  (* let env = List.fold_left2 (fun env (x, _) t -> *)
  (*   incr count; *)
  (*   let a = alloca (structured_type env t) (transl_typ env t) in *)
  (*   set_value_name x.s a; *)
  (*   store (VAL (param (Lazy.force fi.f_llvalue) !count)) (VAL a); *)
  (*   add_var x t a env) env fundef.fn_args ts in *)

  (* (\* Process the body *\) *)
  (* typ_exp { env with in_loop = NoLoop } fundef.fn_body t (fun body -> *)
  (*   if fundef.fn_rtyp = None then *)
  (*     ignore (build_ret_void g_builder) *)
  (*   else *)
  (*     ignore (build_ret (llvm_value body) g_builder)); *)

  (* position_at_end (entry_block (Lazy.force fi.f_llvalue)) g_builder; *)
  (* ignore (build_br startbb g_builder) *)

(* and let_funs env fundefs e nxt = *)
(*   check_unique_fundef_names fundefs; *)

(*   let sols' = *)
(*     List.fold_left (fun s f -> *)
(*     let ffv = List.fold_left (fun s (x, _) -> S.remove x.s s) *)
(*         (fv f.fn_body) f.fn_args in *)
(*     S.union ffv s *)
(*       ) S.empty fundefs *)
(*   in *)
(*   let sols' = List.fold_left (fun sols f -> M.add f.fn_name.s sols' sols) env.sols fundefs in *)
(*   let env' = {env with sols = sols'} in *)
(*   let curr = insertion_block g_builder in *)
(*   let env' = List.fold_left tr_function_header env' fundefs in *)
(*   List.iter (tr_function_body env') fundefs; *)
(*   position_at_end curr g_builder; *)

(*   exp env' e nxt *)

(* and array_var env v nxt = *)
(*   var env v (fun v' t -> *)
(*     match base_type env t with *)
(*     | ARRAY (_, t') -> nxt v' t' *)
(*     | _ -> *)
(*         error (var_p v) "expected variable of array type, but type is '%s'" *)
(*           (describe_type t)) *)

(* and record_var env v nxt = *)
(*   var env v (fun v' t -> *)
(*     match base_type env t with *)
(*     | RECORD _ -> nxt v' t *)
(*     | _ -> *)
(*         error (var_p v) "expected variable of record type, but type is '%s'" *)
(*           (describe_type t)) *)

let rec typ_exp env e t' =
  let t, e' = exp env e in
  if type_equal env t t' then
    e'
  else
    error (exp_p e)
      "type mismatch: expected type '%s', instead found '%s'"
      (string_of_type t') (string_of_type t)

and int_exp env e =
  typ_exp env e INT

and void_exp env e =
  typ_exp env e VOID

(* Main typechecking/compiling functions *)

and var env = function
  | Vsimple x ->
      let vi = find_var x env in
      vi.vtype, Lvar x.s
  (* | Vsubscript (p, v, x) -> *)
  (*     array_var env v (fun v t' -> *)
  (*     let v = save (triggers x) v in *)
  (*     int_exp env x (fun x -> *)
  (*     let v = array_index p.Lexing.pos_lnum v x in *)
  (*     nxt (load v) t')) *)
  (* | Vfield (p, v, x) -> *)
  (*     record_var env v (fun v t' -> *)
  (*     let i, tx = find_record_field env t' x in *)
  (*     let v = record_index p.Lexing.pos_lnum v i in *)
  (*     nxt (load v) tx) *)

and exp env = function
  | Eunit _ ->
      VOID, Lconst 0n
  | Eint (_, n) ->
      INT, Lconst (Nativeint.of_int n)
  | Estring (_, s) ->
      failwith "not implemented"
      (* nxt (VAL (build_global_stringptr s "" g_builder)) STRING *)
  | Enil p ->
      error p
        "'nil' should be used in a context where \
        its type can be determined"
  | Evar (_, v) ->
      var env v
  | Ebinop (_, e1, Op_add, e2) ->
      let e1 = int_exp env e1 in
      let e2 = int_exp env e2 in
      INT, Lprim (Paddint, [e1; e2])
  | Ebinop (_, e1, Op_sub, e2) ->
      let e1 = int_exp env e1 in
      let e2 = int_exp env e2 in
      INT, Lprim (Psubint, [e1; e2])
  (* | Ebinop (_, x, Op_mul, y) -> *)
  (*     int_exp env x (fun x -> *)
  (*     int_exp env y (fun y -> *)
  (*     nxt (binop build_mul x y) INT)) *)
  (* | Ebinop (_, x, Op_div, y) -> *)
  (*     int_exp env x (fun x -> *)
  (*     int_exp env y (fun y -> *)
  (*     nxt (binop build_sdiv x y) INT)) *)
  (* | Ebinop (_, x, Op_cmp Ceq, Enil _) *)
  (* | Ebinop (_, Enil _, Op_cmp Ceq, x) -> *)
  (*     exp env x (fun v tx -> *)
  (*       match base_type env tx with *)
  (*       | RECORD _ -> *)
  (*           let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in *)
  (*           let c = binop (build_icmp Icmp.Eq) v *)
  (*             (const_null (int_t Sys.word_size)) in *)
  (*           let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in *)
  (*           nxt c INT *)
  (*       | _ -> *)
  (*           error (exp_p x) "expected expression of record type, found %s" *)
  (*             (describe_type tx)) *)
  (* | Ebinop (_, x, Op_cmp Cne, Enil _) *)
  (* | Ebinop (_, Enil _, Op_cmp Cne, x) -> *)
  (*     exp env x (fun v tx -> *)
  (*       match base_type env tx with *)
  (*       | RECORD _ -> *)
  (*           let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in *)
  (*           let c = binop (build_icmp Icmp.Ne) v *)
  (*             (const_null (int_t Sys.word_size)) in *)
  (*           let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in *)
  (*           nxt c INT *)
  (*       | _ -> *)
  (*           error (exp_p x) "expected expression of record type, found %s" *)
  (*             (describe_type tx)) *)
  (* | Ebinop (p, x, Op_cmp cmp, y) -> *)
  (*     let zext v s b = build_zext v (int_t 32) s b in *)
  (*     let p2i v s b = build_ptrtoint v (int_t Sys.word_size) s b in *)
  (*     exp env x (fun x tx -> *)
  (*     typ_exp env y tx (fun y -> *)
  (*     match base_type env tx, cmp with *)
  (*     | INT, _ -> *)
  (*         let op = match cmp with *)
  (*         | Ceq -> Icmp.Eq | Cle -> Icmp.Sle | Cge -> Icmp.Sge *)
  (*         | Cne -> Icmp.Ne | Clt -> Icmp.Slt | Cgt -> Icmp.Sgt *)
  (*         in *)
  (*         let c = binop (build_icmp op) x y in *)
  (*         let c = unop zext c in *)
  (*         nxt c INT *)
  (*     | STRING, _ -> *)
  (*         let op = match cmp with *)
  (*         | Ceq -> Icmp.Eq | Cle -> Icmp.Sle | Cge -> Icmp.Sge *)
  (*         | Cne -> Icmp.Ne | Clt -> Icmp.Slt | Cgt -> Icmp.Sgt *)
  (*         in *)
  (*         let c = strcmp x y in *)
  (*         let c = binop (build_icmp op) c (const_int 32 0) in *)
  (*         let c = unop zext c in *)
  (*         nxt c INT *)
  (*     | RECORD _, Ceq *)
  (*     | ARRAY _, Ceq -> *)
  (*         let v1 = unop p2i x in *)
  (*         let v2 = unop p2i y in *)
  (*         let c = binop (build_icmp Icmp.Eq) v1 v2 in *)
  (*         let c = unop zext c in *)
  (*         nxt c INT *)
  (*     | RECORD _, Cne *)
  (*     | ARRAY _, Cne -> *)
  (*         let v1 = unop p2i x in *)
  (*         let v2 = unop p2i y in *)
  (*         let c = binop (build_icmp Icmp.Ne) v1 v2 in *)
  (*         let c = unop zext c in *)
  (*         nxt c INT *)
  (*     | VOID, Ceq -> nxt (const_int 32 1) INT (\* FIXME ? *\) *)
  (*     | VOID, Cne -> nxt (const_int 32 0) INT (\* FIXME ? *\) *)
  (*     | NAME _, _ -> assert false *)
  (*     | _, _ -> *)
  (*         error p "comparison operator cannot be applied to type '%s'" *)
  (*           (describe_type tx))) *)
  (* | Eassign (p, Vsimple x, Enil _) -> *)
  (*     let vi = find_var x env in *)
  (*     begin match base_type env vi.vtype with *)
  (*     | RECORD _ -> *)
  (*         store (const_null (transl_typ env vi.vtype)) (VAL vi.v_alloca); *)
  (*         nxt nil VOID *)
  (*     | _ -> *)
  (*         error p "trying to assign 'nil' to a variable of non-record type" *)
  (*     end *)
  (* | Eassign (p, Vsimple x, e) -> *)
  (*     let vi = find_var x env in *)
  (*     if vi.vimm then error p "variable '%s' should not be assigned to" x.s; *)
  (*     typ_exp env e vi.vtype (fun e -> *)
  (*     store e (VAL vi.v_alloca); *)
  (*     nxt nil VOID) *)
  (* | Eassign (p, Vsubscript (p', v, e1), Enil _) -> *)
  (*     array_var env v (fun v t' -> *)
  (*     match base_type env t' with *)
  (*     | RECORD _ -> *)
  (*         let v = save (triggers e1) v in *)
  (*         int_exp env e1 (fun e1 -> *)
  (*         let v = array_index p'.Lexing.pos_lnum v e1 in *)
  (*         store (const_null (transl_typ env t')) v; *)
  (*         nxt nil VOID) *)
  (*     | _ -> *)
  (*         error p "trying to assign 'nil' to a field of non-record type") *)
  (* | Eassign (_, Vsubscript (p, v, e1), e2) -> *)
  (*     array_var env v (fun v t' -> *)
  (*     let v = save (triggers e1) v in *)
  (*     int_exp env e1 (fun e1 -> *)
  (*     let v = array_index p.Lexing.pos_lnum v e1 in *)
  (*     let v = save (triggers e2) v in *)
  (*     typ_exp env e2 t' (fun e2 -> *)
  (*     store e2 v; *)
  (*     nxt nil VOID))) *)
  (* | Eassign (p, Vfield (p', v, x), Enil _) -> *)
  (*     record_var env v (fun v t' -> *)
  (*     let i, tx = find_record_field env t' x in *)
  (*     match base_type env tx with *)
  (*     | RECORD _ -> *)
  (*         let v = record_index p'.Lexing.pos_lnum v i in *)
  (*         store (const_null (transl_typ env t')) v; *)
  (*         nxt nil VOID *)
  (*     | _ -> *)
  (*         error p "trying to assign 'nil' to a field of non-record type") *)
  (* | Eassign (_, Vfield (p, v, x), e) -> *)
  (*     record_var env v (fun v t' -> *)
  (*     let i, tx = find_record_field env t' x in *)
  (*     let v = record_index p.Lexing.pos_lnum v i in *)
  (*     let v = save (triggers e) v in *)
  (*     typ_exp env e tx (fun e -> *)
  (*     store e v; *)
  (*     nxt nil VOID)) *)
  (* | Ecall (p, x, xs) -> *)
  (*     let fi = find_fun x env in *)
  (*     let ts, t = fi.fsign in *)
  (*     if List.length xs <> List.length ts then *)
  (*       error p "bad arity: is %d, should be %d" *)
  (*         (List.length xs) (List.length ts); *)
  (*     let rec bind ys = function *)
  (*       | [], [] -> *)
  (*           let actuals = if fi.f_user then *)
  (*             List.fold_right (fun x ys -> *)
  (*               let vi = find_var { s = x; p = Lexing.dummy_pos } env in *)
  (*               VAL vi.v_alloca :: ys) *)
  (*               (S.elements (M.find x.s env.sols)) (List.rev ys) *)
  (*               else List.rev ys in *)
  (*           nxt (call (Lazy.force fi.f_llvalue) actuals) t *)
  (*       | Enil p :: xs, t :: ts -> *)
  (*           begin match base_type env t with *)
  (*           | RECORD _ -> *)
  (*               bind (const_null (transl_typ env t) :: ys) (xs, ts) *)
  (*           | _ -> *)
  (*               error p "expected record type, found '%s'" (describe_type t) *)
  (*           end *)
  (*       | x :: xs, t :: ts -> *)
  (*           typ_exp env x t (fun x -> *)
  (*           let x = save (structured_type env t && List.exists triggers xs) x in *)
  (*           bind (x :: ys) (xs, ts)) *)
  (*       | _ -> *)
  (*           assert false *)
  (*     in bind [] (xs, ts) *)
  (* | Eseq (_, x1, x2) -> *)
  (*     exp env x1 (fun _ _ -> exp env x2 nxt) *)
  (* | Emakearray (p, x, y, Enil _) -> *)
  (*     let t, t' = find_array_type x env in *)
  (*     begin match base_type env t' with *)
  (*     | RECORD _ -> *)
  (*         int_exp env y (fun y -> *)
  (*         let y = VAL (llvm_value y) in *)
  (*         let a = gc_alloc (add (const_int Sys.word_size 8) *)
  (*           (mul (unop (fun v -> build_zext v (int_t Sys.word_size)) y) (size_of (transl_typ env t')))) in *)
  (*         let a = build_pointercast a (ptr_t (struct_t [| int_t 32; *)
  (*           array_type (transl_typ env t') 0 |])) "" g_builder in *)
  (*         store y (array_length_addr (VAL a)); *)
  (*         (\* FIXME initialisation *\) *)
  (*         nxt (VAL a) t) *)
  (*     | _ -> *)
  (*         error p "array base type must be record type" *)
  (*     end *)
  (* | Emakearray (_, x, y, z) -> *)
  (*     let t, t' = find_array_type x env in *)
  (*     int_exp env y (fun y -> *)
  (*     typ_exp env z t' (fun z -> *)
  (*     let y = VAL (llvm_value y) in *)
  (*     let a = gc_alloc (add (const_int Sys.word_size 8) (mul *)
  (*       (unop (fun v -> build_zext v (int_t Sys.word_size)) y) (size_of *)
  (*       (transl_typ env t')))) in *)
  (*     let a = build_pointercast a (ptr_t (struct_t *)
  (*       [| int_t 32; array_type (transl_typ env t') 0 |])) "" g_builder in *)
  (*     store y (array_length_addr (VAL a)); *)
  (*     (\* FIXME initialisation *\) *)
  (*     nxt (VAL a) t)) *)
  (* | Emakerecord (p, x, xts) -> *)
  (*     let t, ts = find_record_type env x in *)
  (*     let rec bind vs = function *)
  (*       | [], [] -> *)
  (*           let t' = element_type (transl_typ env t) in *)
  (*           debug () "%s" (string_of_lltype t'); *)
  (*           let r = VAL (gc_alloc_type t') in *)
  (*           let rec bind i = function *)
  (*             | [] -> nxt r t *)
  (*             | v :: vs -> *)
  (*                 let f = gep r [ const_int 32 0; const_int 32 i ] in *)
  (*                 store v f; *)
  (*                 bind (i+1) vs *)
  (*           in bind 0 (List.rev vs) *)
  (*       | (x, Enil _) :: xts, (x', t) :: ts -> *)
  (*           if x.s = x' then *)
  (*             bind (const_null (transl_typ env t) :: vs) (xts, ts) *)
  (*           else *)
  (*             if List.exists (fun (x', _) -> x.s = x') ts then *)
  (*               error x.p "field '%s' is in the wrong other" x.s *)
  (*             else *)
  (*               error x.p "field '%s' is unknown" x.s *)
  (*       | (x, e) :: xts, (x', t) :: ts -> *)
  (*           if x.s = x' then *)
  (*             typ_exp env e t (fun e -> *)
  (*             let e = save (structured_type env t) e in *)
  (*             bind (e :: vs) (xts, ts)) *)
  (*           else *)
  (*             if List.exists (fun (x', _) -> x.s = x') ts then *)
  (*               error x.p "field '%s' is in the wrong other" x.s *)
  (*             else *)
  (*               error x.p "unknown field '%s'" x.s *)
  (*       | [], _ -> *)
  (*           error p "some fields missing from initialisation" *)
  (*       | _, [] -> *)
  (*           error p "all fields have already been initialised" *)
  (*     in bind [] (xts, ts) *)
  (* (\* | Pif (_, P.Ecmp (x, op, y), z, None) -> *)
  (*     int_exp tenv venv looping x (fun x -> *)
  (*       int_exp tenv venv looping y (fun y -> *)
  (*         .Sseq (T.Sif (Ebinop (x, op, y), *)
  (*           void_exp tenv venv looping z Sskip, Sskip), *)
  (*           nxt Eundef E.Tvoid))) *\) *)
  (* | Eif (_, x, y, Eunit _) -> *)
  (*     let nextbb = new_block () in *)
  (*     let yesbb  = new_block () in *)
  (*     int_exp env x (fun x -> *)
  (*       let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in *)
  (*       cond_br c yesbb nextbb); *)
  (*     position_at_end yesbb g_builder; *)
  (*     void_exp env y (fun () -> ignore (build_br nextbb g_builder)); *)
  (*     position_at_end nextbb g_builder; *)
  (*     nxt nil VOID *)
  (* | Eif (_, x, y, z) -> *)
  (*     let nextbb = new_block () in *)
  (*     let yesbb  = new_block () in *)
  (*     let naybb  = new_block () in *)
  (*     let tmp    = ref nil in *)
  (*     let typ    = ref VOID in *)
  (*     int_exp env x (fun x -> *)
  (*       let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in *)
  (*       cond_br c yesbb naybb); *)
  (*     position_at_end yesbb g_builder; *)
  (*     exp env y (fun y ty -> *)
  (*       typ := ty; *)
  (*       if ty <> VOID then begin *)
  (*         tmp := VAL (alloca false (transl_typ env ty)); *)
  (*         store y !tmp *)
  (*       end; ignore (build_br nextbb g_builder)); *)
  (*     position_at_end naybb g_builder; *)
  (*     typ_exp env z !typ (fun z -> if !typ <> VOID then store z !tmp; ignore (build_br nextbb g_builder)); *)
  (*     position_at_end nextbb g_builder; *)
  (*     nxt (if !typ = VOID then nil else load !tmp) !typ *)
  (* | Ewhile (_, x, y) -> *)
  (*     let nextbb = new_block () in *)
  (*     let testbb = new_block () in *)
  (*     let bodybb = new_block () in *)
  (*     ignore (build_br testbb g_builder); *)
  (*     position_at_end testbb g_builder; *)
  (*     int_exp env x (fun x -> *)
  (*       let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in *)
  (*       cond_br c bodybb nextbb); *)
  (*     position_at_end bodybb g_builder; *)
  (*     void_exp { env with in_loop = InLoop nextbb } y *)
  (*       (fun () -> ignore (build_br testbb g_builder)); *)
  (*     position_at_end nextbb g_builder; *)
  (*     nxt nil VOID *)
  (* | Efor (_, i, x, y, z) -> *)
  (*     let nextbb = new_block () in *)
  (*     let testbb = new_block () in *)
  (*     let bodybb = new_block () in *)
  (*     int_exp env x (fun x -> *)
  (*     int_exp env y (fun y -> *)
  (*       let a = alloca false (int_t 32) in *)
  (*       let ii = VAL (a) in *)
  (*       set_value_name i.s a; *)
  (*       store x ii; *)
  (*       ignore (build_br testbb g_builder); *)
  (*       position_at_end testbb g_builder; *)
  (*       let iii = load ii in *)
  (*       let c = binop (build_icmp Icmp.Sle) iii y in *)
  (*       cond_br c bodybb nextbb; *)
  (*       position_at_end bodybb g_builder; *)
  (*       void_exp (add_var i ~immutable:true INT (llvm_value iii) env) z (\* M.add i (llvm_value iii) *)
  (*     env) nextbb z (fun _ -> *\) *)
  (*       (fun () -> *)
  (*         let plusone = binop build_add iii (const_int 32 1) in *)
  (*         store plusone ii; *)
  (*         ignore (build_br testbb g_builder)))); *)
  (*     position_at_end nextbb g_builder; *)
  (*     nxt nil VOID *)
  (* | Ebreak p -> *)
  (*     begin match env.in_loop with *)
  (*     | InLoop bb -> ignore (build_br bb g_builder); *)
  (*     | NoLoop    -> error p "illegal use of 'break'" *)
  (*     end *)
  (* | Elet (_, Dvar (x, None, y), z) -> *)
  (*     exp env y (fun y ty -> *)
  (*     let a = alloca (structured_type env ty) (transl_typ env ty) in *)
  (*     set_value_name x.s a; *)
  (*     let env = add_var x ty a env in *)
  (*     store y (VAL a); *)
  (*     exp env z (fun z tz -> *)
  (*     if structured_type env ty then store (const_null (transl_typ env ty)) (VAL a); *)
  (*     nxt z tz)) *)
  (* | Elet (p, Dvar (x, Some t, Enil _), z) -> *)
  (*     let t = find_type t env in *)
  (*     begin match base_type env t with *)
  (*     | RECORD _ -> *)
  (*         let a = alloca true (transl_typ env t) in *)
  (*         set_value_name x.s a; *)
  (*         let env = add_var x t a env in *)
  (*         store (const_null (transl_typ env t)) (VAL a); *)
  (*         exp env z (fun z tz -> *)
  (*         store (const_null (transl_typ env t)) (VAL a); *)
  (*         nxt z tz) *)
  (*     | _ -> *)
  (*         error p "expected record type, found '%s'" (describe_type t) *)
  (*     end *)
  (* | Elet (_, Dvar (x, Some t, y), z) -> *)
  (*     let ty = find_type t env in *)
  (*     typ_exp env y ty (fun y -> *)
  (*     let a = alloca (structured_type env ty) (transl_typ env ty) in *)
  (*     set_value_name x.s a; *)
  (*     let env = add_var x ty a env in *)
  (*     store y (VAL a); *)
  (*     exp env z (fun z tz -> *)
  (*     if structured_type env ty then store (const_null (transl_typ env ty)) (VAL a); *)
  (*     nxt z tz)) *)
  (* | Elet (_, Dtypes tys, e) -> *)
  (*     let env = let_type env tys in *)
  (*     exp env e nxt *)
  (* | Elet (_, Dfuns funs, e) -> *)
  (*     let_funs env funs e nxt *)

let stdtypes =
  [
    "int", INT;
    "string", STRING;
  ]

let stdlib =
  [
    "print" , [STRING], VOID;
    "printi", [INT], VOID;
    "flush", [], VOID;
    "getchar", [], STRING;
    "ord", [STRING], INT;
    "chr", [INT], STRING;
    "size", [STRING], INT;
    "substring", [STRING; INT; INT], STRING;
    "concat", [STRING; STRING], STRING;
    "not", [INT], INT;
    "exit", [INT], VOID;
  ]

let base_tenv =
  List.fold_left (fun m (id, t) -> M.add id t m) M.empty stdtypes

let base_venv =
  M.empty (* FIXME *)
  (* let decl_fun env (x, ts, t) = *)
  (*   let fname = "__tiger__" ^ x in *)
  (*   let fllval = lazy (declare_function fname *)
  (*     (function_type (llvm_return_type env t) *)
  (*       (Array.of_list (List.map (transl_typ env) ts))) *)
  (*     g_module) in *)
  (*   { env with venv = M.add x *)
  (*     (Function {fname = fname; f_user = false; fsign = (ts, t); f_llvalue = *)
  (*       fllval }) env.venv } in *)
  (* List.fold_left decl_fun env stdlib *)

let program e =
  let tenv = base_tenv in
  let venv = base_venv in
  (* let main_fun = define_function "__tiger__main" *)
  (*   (function_type void_t [| |]) g_module in *)
  (* set_gc (Some "shadow-stack") main_fun; *)
  (* position_at_end (entry_block main_fun) g_builder; *)
  (* let startbb = new_block () in *)
  (* position_at_end startbb g_builder; *)
  (* (\* exp env e (fun _ _ -> ignore (build_ret (const_int0 32 0) g_builder)); *\) *)
  let _, e = exp {tenv; venv} e in (* (fun _ _ -> ignore (build_ret_void g_builder));*)
  (* position_at_end (entry_block main_fun) g_builder; *)
  (* ignore (build_br startbb g_builder); *)
  (* g_module *)
  e
