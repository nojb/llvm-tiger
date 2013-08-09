open Parsetree
open Llvm

exception Error of Lexing.position * string

let error p =
  Printf.ksprintf (fun message -> raise (Error (p, message)))

let debug () =
  Printf.ksprintf (fun message -> Printf.fprintf stderr "DEBUG: %s\n%!" message)

let tmp_counter = ref (-1)

let gentmp s =
  incr tmp_counter;
  s ^ "__" ^ (string_of_int !tmp_counter)

type type_spec =
  | VOID
  | INT
  | STRING
  | ARRAY   of string * type_spec
  | RECORD  of string * string (* name, unique name *)
  | PLACE   of string

let rec string_of_type = function
  | VOID -> "void"
  | INT -> "int"
  | STRING -> "string"
  | ARRAY (id, t) -> id ^ " = array of " ^ string_of_type t
  | RECORD (id, _) -> id ^ " = record"
  | PLACE _ -> assert false

let describe_type = function
  | VOID -> "void"
  | INT -> "int"
  | STRING -> "string"
  | ARRAY _ -> "array"
  | RECORD _ -> "record"
  | PLACE _ -> assert false

let type_equal t1 t2 =
  t1 == t2

type var_info = {
  vtype : type_spec;
  vimm : bool;
  v_alloca : llvalue
}

type fun_impl =
  | Internal
  | External

type fun_info = {
  fname : string;
  fsign : type_spec list * type_spec;
  fimpl : fun_impl;
  f_llvalue : llvalue
}

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type loop_flag =
  | NoLoop
  | InLoop of llbasicblock

type env = {
  venv : value_desc M.t;
  tenv : type_spec M.t;
  renv : (string * type_spec) list M.t;

  in_loop : loop_flag;

  (* used for lambda lifting *)
(*  vars : type_spec M.t;
  funs : S.t; *)
  sols : S.t M.t
}

let empty_env = {
  venv = M.empty;
  tenv = M.empty;
  renv = M.empty;
  in_loop = NoLoop;
(*  vars = M.empty;
  funs = S.empty; *)
  sols = M.empty
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
  let vi = { vtype = t; vimm = immut; v_alloca = llv } in
  { env with venv = M.add x.s (Variable vi) env.venv }
      (* vars = M.add x.s t env.vars } *)

let mem_var x env =
  try match M.find x env.venv with
  | Variable _ -> true
  | Function _ -> false
  with Not_found -> false

let add_fun x uid atyps rtyp llv env =
  let fi = {
    fname = uid;
    fsign = atyps, rtyp;
    fimpl = Internal;
    f_llvalue = llv
  } in
  { env with venv = M.add x.s (Function fi) env.venv }

let mem_user_fun x env =
  try match M.find x env.venv with
  | Function fi -> fi.fimpl = Internal
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
  match find_type x env with
  | ARRAY (_, t') as t -> t, t'
  | _ as t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s
        (describe_type t)

let find_record_type env x =
  match find_type x env with
  | RECORD (ts, _) as t -> t, M.find ts env.renv
  | _ as t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s
        (describe_type t)

let find_record_field env t (x : pos_string) =
  let t = match t with RECORD (t, _) -> t | _ -> assert false in
  let ts = M.find t env.renv in
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in loop 0 ts

(* * LLVM Utils *)

type llvm_value =
  | VAL of llvalue
  | LOADVAL of llvalue

let g_context = global_context ()
let g_module  = create_module g_context ""
let g_builder = builder g_context

let getfun n =
  match lookup_function n g_module with
  | Some f -> f
  | None -> assert false

let new_block () =
  (* this assumes that the builder is already set up
   * inside a function *)
  let f = block_parent (insertion_block g_builder) in
  append_block g_context "" f

let llvm_value = function
  | VAL v -> v
  | LOADVAL v -> build_load v "" g_builder

let int_t w =
  integer_type g_context w

let void_t =
  void_type g_context

let ptr_t t =
  pointer_type t

let struct_t fields =
  struct_type g_context fields

let const_int0 w n =
  const_int (int_t w) n

  (* This one shadows Llvm.const_int *)
let const_int w n =
  VAL (const_int (int_t w) n)

let const_null0 =
  const_null

let const_null t =
  VAL (const_null t)

let size_of t = (* shadows Llvm.size_of *)
  VAL (size_of t)

let malloc v =
  build_call (declare_function "malloc"
    (function_type (ptr_t (int_t 8)) [| int_t Sys.word_size  |]) g_module)
    [| llvm_value v |] "" g_builder

let alloca is_ptr ty =
  let b = builder_at_end g_context
    (entry_block (block_parent (insertion_block g_builder))) in
  let a = build_alloca ty "" b in
  if is_ptr then begin
    let v = build_pointercast a (ptr_t (ptr_t (int_t 8))) "" b in
    ignore (build_call (declare_function "llvm.gcroot"
      (function_type void_t [| ptr_t (ptr_t (int_t 8)); ptr_t (int_t 8) |])
      g_module) [| v; const_null0 (ptr_t (int_t 8)) |] "" b)
  end;
  a

let add v1 v2 =
  VAL (build_add (llvm_value v1) (llvm_value v2) "" g_builder)

let mul v1 v2 =
  VAL (build_mul (llvm_value v1) (llvm_value v2) "" g_builder)

let load v =
  VAL (build_load (llvm_value v) "" g_builder)

let nil =
  const_int 32 0

let dump_llvm_value = function
  | VAL v
  | LOADVAL v -> dump_value v

let store v p =
  ignore (build_store (llvm_value v) (llvm_value p) g_builder)

let gep v vs =
  dump_llvm_value v;
  prerr_endline (string_of_lltype (element_type (type_of (llvm_value v))));
  List.iter dump_llvm_value vs;
  VAL (build_gep (llvm_value v)
    (Array.of_list (List.map llvm_value vs)) "" g_builder)

let binop op v1 v2 =
  VAL (op (llvm_value v1) (llvm_value v2) "" g_builder)

let unop op v =
  VAL (op (llvm_value v) "" g_builder)

let call v0 vs =
  VAL (build_call v0 (Array.of_list (List.map llvm_value vs)) "" g_builder)

let phi incoming =
  VAL (build_phi
    (List.map (fun (v, bb) -> llvm_value v, bb) incoming) "" g_builder)

let cond_br c yaybb naybb =
  ignore (build_cond_br (llvm_value c) yaybb naybb g_builder)

let array_length v =
  load (gep v [ const_int 32 0; const_int 32 1 ])

let printf msg =
  ignore (build_call (declare_function "printf"
    (var_arg_function_type (int_t 32) [| ptr_t (int_t 8) |])
    g_module) [| build_global_stringptr msg "" g_builder |] "" g_builder)

let die msg =
  printf msg;
  ignore (build_call (declare_function "exit"
    (function_type void_t [| int_t 32 |]) g_module) [| const_int0 32 2 |] ""
    g_builder);
  ignore (build_unreachable g_builder)

let array_index lnum v x =
  let v = VAL (llvm_value v) in
  let yesbb = new_block () in
  let diebb = new_block () in
  let l = array_length v in
  let c1 = binop (build_icmp Icmp.Sle) x l in
  let c2 = binop (build_icmp Icmp.Sge) x (const_int 32 0) in
  let c = binop build_and c1 c2 in
  cond_br c yesbb diebb;
  position_at_end diebb g_builder;
  die (Printf.sprintf "Runtime error: index out of bounds in line %d\n" lnum);
  position_at_end yesbb g_builder;
  gep v [ const_int 32 0; const_int 32 2; x ]

let record_index lnum v i =
  let v = VAL (llvm_value v) in
  let yesbb = new_block () in
  let diebb = new_block () in
  let ptr = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in
  let c = binop (build_icmp Icmp.Ne) ptr (const_int Sys.word_size 0) in
  cond_br c yesbb diebb;
  position_at_end diebb g_builder;
  die (Printf.sprintf
    "Runtime error: field access to nil record in line %d\n" lnum);
  position_at_end yesbb g_builder;
  gep v [ const_int 32 0; const_int 32 (i+1) ]

let save triggers v =
  if triggers then
    match v with
    | LOADVAL _ -> v
    | VAL v ->
        let a = alloca true (type_of v) in
        ignore (build_store v a g_builder);
        LOADVAL a
  else
    v

let named_structs : (string * Llvm.lltype) list ref = ref []

let rec transl_typ env t =
  let visited : string list ref = ref [] in
  let rec loop t =
    match t with
    | INT   -> int_t 32
    | VOID  -> int_t 32
    | STRING -> pointer_type (int_t 8)
    | ARRAY (_, t) -> (* { i32, i32, [0 x t] }* *)
        pointer_type (struct_type (global_context ())
          [| int_t 32; int_t 32; array_type (loop t) 0 |])
    | RECORD (rname, uid) ->
        if not (List.exists (fun (x, _) -> x = uid) !named_structs)
        && not (List.mem uid !visited)
        then begin
          visited := uid :: !visited;
          let ty = named_struct_type (global_context ()) uid in
          named_structs := (uid, ty) :: !named_structs;
          struct_set_body ty
            (Array.of_list (int_t 32 :: List.map (fun (_, t) -> loop t) (M.find rname
            env.renv))) false;
          (* ()) (Id.to_string uid)) :: !named_structs
            (Tint 32 :: List.map (fun (_, t) -> loop t) (M.find rname
            env.renv))) :: !named_structs *)
        end;
        pointer_type (List.assoc uid !named_structs)
        (* pointer_type (named_struct_type 
        Tpointer (Tnamedstruct (Id.to_string uid)) *)
    | PLACE _ ->
        assert false
  in loop t

let declare_type env (x, t) =
  let find_type y env =
    try M.find y.s env.tenv
    with Not_found -> PLACE y.s in
  match t with
  | PTname y ->
      add_type x (find_type y env) env
  | PTarray y ->
      add_type x (ARRAY (x.s, find_type y env)) env
  | PTrecord xs ->
      add_type x (RECORD (x.s, gentmp x.s)) env

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

let define_type env (x, _) =
  let visited = ref [] in
  let rec loop y =
    if List.mem y !visited then
      error x.p "type declaration cycle does not pass through record type"
    visited := y :: !visited;
    try
      let t = M.find y env.tenv in
      match t with
      | PLACE y -> loop y
      | ARRAY (x, PLACE y') -> ARRAY (x, loop y')
      | _ -> t
    with Not_found ->
      error x.p "unbound type '%s'" y
        (* FIXME x.p != position of y in general *)
  in add_type x (loop x.s) env

let extract_record_type env (x, t) =
  match t with
  | PTrecord (xts) ->
      { env with renv =
          M.add x.s (List.map (fun (x, t) -> (x.s, find_type t env)) xts) env.renv }
  | _ ->
      env

let let_type env tys =
  check_unique_type_names tys;
  let env = List.fold_left declare_type env tys in
  let env = List.fold_left define_type env tys in
  let env = List.fold_left extract_record_type env tys in
  env

(** ----------------------------------------- *)

let rec structured_type t =
  match t with
  | PLACE _ -> assert false
  | STRING
  | ARRAY _
  | RECORD _ -> true
  | _ -> false

let array_exists p a =
  let rec loop i =
    if i >= Array.length a then false
    else if p a.(i) then true
    else loop (i+1)
  in loop 0

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

(* let toplevel : (string, Llvm.lltype, Llvm.lltype * ptr_flag * free_flag, exp) fundef list ref =
  ref [] *)

let tr_return_type env fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t env

let llvm_return_type env = function
  | VOID -> void_t
  | t -> transl_typ env t

let tr_function_header env fn =
  let type_of_var env x =
    match M.find x env.venv with
    | Variable vi -> transl_typ env vi.vtype
    | Function _ -> assert false in
  let free_vars = S.elements (M.find fn.fn_name.s env.sols) in
  let free_vars = List.map (fun x -> (x, pointer_type (type_of_var env x)))
    free_vars in
    (* (x, pointer_type (transl_typ env (M.find x env.vars)))) free_vars in *)
  let rtyp = tr_return_type env fn in
  let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in
  let uid = gentmp fn.fn_name.s in
  let llv = define_function uid
    (function_type (llvm_return_type env rtyp)
      (Array.of_list (List.map snd free_vars @
      (List.map (transl_typ env) argst)))) g_module in
  let env' = add_fun fn.fn_name uid argst
    (* (List.map (fun (_, t) -> find_type t env) fn.fn_args) *)
    rtyp llv env in
  env'

let rec tr_function_body env fundef =
  let type_of_var env x =
    match M.find x env.venv with
    | Variable vi -> vi.vtype
    | Function _ -> assert false in

  let fi = find_fun fundef.fn_name env in
  let ts, t = fi.fsign in

  position_at_end (entry_block fi.f_llvalue) g_builder;
  let startbb = new_block () in
  position_at_end startbb g_builder;
  let count = ref (-1) in

  (* Process arguments *)
  let env = List.fold_left (fun env x ->
    incr count;
    add_var { s = x; p = Lexing.dummy_pos } (type_of_var env x) (param fi.f_llvalue !count) env)
    env (S.elements (M.find fundef.fn_name.s env.sols)) in
  let env = List.fold_left2 (fun env (x, _) t ->
    incr count;
    let a = alloca (structured_type t) (transl_typ env t) in
    store (VAL (param fi.f_llvalue !count)) (VAL a);
    add_var x t a env) env fundef.fn_args ts in

  (* Process the body *)
  typ_exp { env with in_loop = NoLoop } fundef.fn_body t (fun body ->
    if fundef.fn_rtyp = None then
      ignore (build_ret_void g_builder)
    else
      ignore (build_ret (llvm_value body) g_builder));

  position_at_end (entry_block fi.f_llvalue) g_builder;
  ignore (build_br startbb g_builder)

and let_funs env fundefs e nxt =
  let join m1 m2 = M.fold M.add m1 m2 in

  check_unique_fundef_names fundefs;

  Solver.reset ();
  List.iter (fun f ->
    let gs' = S.elements (fc f.fn_body) in
    let gs  = List.filter (fun fundef -> List.mem fundef.fn_name.s gs') fundefs in
    (* debug () "eqn for %s: gs' = %s gs = %s"
      f.fn_name.s
      (String.concat ", " gs')
      (String.concat ", " (List.map (fun g -> g.fn_name.s) gs)); *)
    let sf  = S.filter (fun v -> mem_var v env) (fv f.fn_body) in
    let hs  = List.filter (fun h -> mem_user_fun h env) gs' in
    let sf  = union_list (sf :: List.map (fun h -> M.find h env.sols) hs) in
    Solver.add_equation f.fn_name.s sf (List.map (fun g -> g.fn_name.s) gs))
    fundefs;
  let sols' = Solver.solve () in
  let sols' = join env.sols sols' in
  (* let funs' = List.fold_right S.add (List.map (fun f -> f.fn_name.s) fundefs)
    env.funs in *)
  (* let env' = { env with funs = funs'; sols = sols' } in *)
  let env' = { env with sols = sols' } in

  let curr = insertion_block g_builder in
  let env' = List.fold_left tr_function_header env' fundefs in
  List.iter (tr_function_body env') fundefs;
  position_at_end curr g_builder;

  exp env' e nxt

and array_var env v nxt =
  var env v (fun v' t ->
    match t with
    | ARRAY (_, t') -> nxt v' t'
    | _ ->
        error (var_p v) "expected variable of array type, but type is '%s'"
          (describe_type t))

and record_var env v nxt =
  var env v (fun v' t ->
    match t with
    | RECORD (t', _) -> nxt v' t
    | _ ->
        error (var_p v) "expected variable of record type, but type is '%s'"
          (describe_type t))

and typ_exp env e t' nxt =
  exp env e (fun e' t ->
    if type_equal t t' then nxt e'
    else error (exp_p e)
      "type mismatch: expected type '%s', instead found '%s'"
        (string_of_type t') (string_of_type t))

and int_exp env e nxt =
  typ_exp env e INT nxt

and void_exp env e nxt =
  typ_exp env e VOID (fun _ -> nxt ())

(* Main typechecking/compiling functions *)

and var env v nxt =
  match v with
  | PVsimple x ->
      let vi = find_var x env in
      if vi.vimm then
        nxt (VAL vi.v_alloca) vi.vtype
      else
        nxt (LOADVAL vi.v_alloca) vi.vtype
  | PVsubscript (p, v, x) ->
      array_var env v (fun v t' ->
      let v = save (triggers x) v in
      int_exp env x (fun x ->
      let v = array_index p.Lexing.pos_lnum v x in
      nxt (load v) t'))
  | PVfield (p, v, x) ->
      record_var env v (fun v t' ->
      let i, tx = find_record_field env t' x in
      let v = record_index p.Lexing.pos_lnum v i in
      nxt (load v) tx)

and exp env e (nxt : llvm_value -> type_spec -> unit) =
  match e with
  | Pint (_, n) ->
      nxt (const_int 32 n) INT
  | Pstring (_, s) ->
      assert false
      (* TCstring s, STRING *)
  | Pnil p ->
      error p
        "'nil' should be used in a context where \
        its type can be determined"
  | Pvar (_, v) ->
      var env v nxt
  | Pbinop (_, x, Op_add, y) ->
      int_exp env x (fun x ->
      int_exp env y (fun y ->
      nxt (binop build_add x y) INT))
  | Pbinop (_, x, Op_sub, y) ->
      int_exp env x (fun x ->
      int_exp env y (fun y ->
      nxt (binop build_sub x y) INT))
  | Pbinop (_, x, Op_mul, y) ->
      int_exp env x (fun x ->
      int_exp env y (fun y ->
      nxt (binop build_mul x y) INT))
  | Pbinop (_, x, Op_div, y) ->
      int_exp env x (fun x ->
      int_exp env y (fun y ->
      nxt (binop build_sdiv x y) INT))
  | Pbinop (_, x, Op_cmp Ceq, Pnil _)
  | Pbinop (_, Pnil _, Op_cmp Ceq, x) ->
      exp env x (fun v tx ->
        match tx with
        | RECORD _ ->
            let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in
            let c = binop (build_icmp Icmp.Eq) v
              (const_null (int_t Sys.word_size)) in
            let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in
            nxt c INT
        | _ ->
            error (exp_p x) "expected expression of record type, found %s"
              (describe_type tx))
  | Pbinop (_, x, Op_cmp Cne, Pnil _)
  | Pbinop (_, Pnil _, Op_cmp Cne, x) ->
      exp env x (fun v tx ->
        match tx with
        | RECORD _ ->
            let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in
            let c = binop (build_icmp Icmp.Ne) v
              (const_null (int_t Sys.word_size)) in
            let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in
            nxt c INT
        | _ ->
            error (exp_p x) "expected expression of record type, found %s"
              (describe_type tx))
  | Pbinop (_, x, Op_cmp cmp, y) ->
      let zext v s b = build_zext v (int_t 32) s b in
      let p2i v s b = build_ptrtoint v (int_t Sys.word_size) s b in
      exp env x (fun x tx ->
      typ_exp env y tx (fun y ->
      match tx, cmp with
      | INT, _ ->
          let op = match cmp with
          | Ceq -> Icmp.Eq | Cle -> Icmp.Sle | Cge -> Icmp.Sge
          | Cne -> Icmp.Ne | Clt -> Icmp.Slt | Cgt -> Icmp.Sgt
          in
          let c = binop (build_icmp op) x y in
          let c = unop zext c in
          nxt c INT
      | STRING, _ ->
          assert false
      | RECORD _, Ceq
      | ARRAY _, Ceq ->
          let v1 = unop p2i x in
          let v2 = unop p2i y in
          let c = binop (build_icmp Icmp.Eq) v1 v2 in
          let c = unop zext c in
          nxt c INT
      | RECORD _, Cne
      | ARRAY _, Cne ->
          let v1 = unop p2i x in
          let v2 = unop p2i y in
          let c = binop (build_icmp Icmp.Ne) v1 v2 in
          let c = unop zext c in
          nxt c INT))
  | Pbinop _ ->
      failwith "binop not implemented"
  | Passign (p, PVsimple x, Pnil _) ->
      let vi = find_var x env in
      begin match vi.vtype with
      | RECORD _ ->
          store (const_null (transl_typ env vi.vtype)) (VAL vi.v_alloca);
          nxt nil VOID
      | _ ->
          error p "trying to assign 'nil' to a variable of non-record type"
      end
  | Passign (p, PVsimple x, e) ->
      let vi = find_var x env in
      if vi.vimm then error p "variable '%s' should not be assigned to" x.s;
      typ_exp env e vi.vtype (fun e ->
      store e (VAL vi.v_alloca);
      nxt nil VOID)
  | Passign (p, PVsubscript (p', v, e1), Pnil _) ->
      array_var env v (fun v t' ->
      match t' with
      | RECORD _ ->
          let v = save (triggers e1) v in
          int_exp env e1 (fun e1 ->
          let v = array_index p'.Lexing.pos_lnum v e1 in
          store (const_null (transl_typ env t')) v;
          nxt nil VOID)
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type")
  | Passign (_, PVsubscript (p, v, e1), e2) ->
      array_var env v (fun v t' ->
      let v = save (triggers e1) v in
      int_exp env e1 (fun e1 ->
      let v = array_index p.Lexing.pos_lnum v e1 in
      let v = save (triggers e2) v in
      typ_exp env e2 t' (fun e2 ->
      store e2 v;
      nxt nil VOID)))
  | Passign (p, PVfield (p', v, x), Pnil _) ->
      record_var env v (fun v t' ->
      let i, tx = find_record_field env t' x in
      match tx with
      | RECORD _ ->
          let v = record_index p'.Lexing.pos_lnum v i in
          store (const_null (transl_typ env t')) v;
          nxt nil VOID
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type")
  | Passign (_, PVfield (p, v, x), e) ->
      record_var env v (fun v t' ->
      let i, tx = find_record_field env t' x in
      let v = record_index p.Lexing.pos_lnum v i in
      let v = save (triggers e) v in
      typ_exp env e tx (fun e ->
      store e v;
      nxt nil VOID))
  | Pcall (p, x, xs) ->
      let fi = find_fun x env in
      let ts, t = fi.fsign in
      if List.length xs <> List.length ts then
        error p "bad arity: is %d, should be %d"
          (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            let actuals =
              List.fold_right (fun x ys ->
                let vi = find_var { s = x; p = Lexing.dummy_pos } env in
                VAL vi.v_alloca :: ys)
                (S.elements (M.find x.s env.sols)) (List.rev ys) in
            nxt (call (getfun fi.fname) actuals) t
            (* Tcall (fi.fname, actuals), t *)
        | x :: xs, t :: ts ->
            typ_exp env x t (fun x ->
            let x = save (structured_type t && List.exists triggers xs) x in
            bind (x :: ys) (xs, ts))
            (* bind (ArgExp (x, IsPtr (structured_type t)) :: ys) (xs, ts) *)
        | _ ->
            assert false
      in bind [] (xs, ts)
  | Pseq (_, xs) ->
      let rec bind = function
        | []      ->
            nxt nil VOID
        | [x]     ->
            exp env x nxt
        | x :: xs ->
            exp env x (fun _ _ -> bind xs)
      in bind xs
  | Pmakearray (p, x, y, Pnil _) ->
      let t, t' = find_array_type x env in
      begin match t' with
      | RECORD _ ->
          int_exp env y (fun y ->
          let a = malloc (add (const_int Sys.word_size 8)
            (mul (unop (fun v -> build_zext v (int_t Sys.word_size)) y) (size_of (transl_typ env t')))) in
          (* FIXME initialisation *)
          nxt (VAL (build_pointercast a (ptr_t (struct_t [| int_t 32; int_t 32;
            array_type (transl_typ env t') 0 |])) "" g_builder)) t)
      | _ ->
          error p "array base type must be record type"
      end
  | Pmakearray (_, x, y, z) ->
      let t, t' = find_array_type x env in
      int_exp env y (fun y ->
      typ_exp env z t' (fun z ->
      let a = malloc (add (const_int Sys.word_size 8) (mul
        (unop (fun v -> build_zext v (int_t Sys.word_size)) y) (size_of (transl_typ env t)))) in
      (* FIXME initialisation *)
      nxt (VAL (build_pointercast a (ptr_t (struct_t
        [| int_t 32; int_t 32; array_type (transl_typ env t') 0 |])) "" g_builder)) t))
  | Pmakerecord (p, x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            let t' = element_type (transl_typ env t) in
            let r = VAL (build_malloc t' "" g_builder) in
            let rec bind i = function
              | [] -> nxt r t
              | v :: vs ->
                  let f = gep r [ const_int 32 0; const_int 32 i ] in
                  store v f;
                  bind (i+1) vs
            in bind 1 (List.rev vs)
        | (x, Pnil _) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (const_null (transl_typ env t) :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "field '%s' is unknown" x.s
        | (x, e) :: xts, (x', t) :: ts ->
            if x.s = x' then
              typ_exp env e t (fun e ->
              let e = save (structured_type t) e in
              bind (e :: vs) (xts, ts))
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "unknown field '%s'" x.s
        | [], _ ->
            error p "some fields missing from initialisation"
        | _, [] ->
            error p "all fields have already been initialised"
      in bind [] (xts, ts)
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Pif (_, x, y, None) ->
      let nextbb = new_block () in
      let yesbb  = new_block () in
      int_exp env x (fun x ->
        let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in
        cond_br c yesbb nextbb);
      position_at_end yesbb g_builder;
      void_exp env y (fun () -> ignore (build_br nextbb g_builder));
      position_at_end nextbb g_builder;
      nxt nil VOID
  | Pif (_, x, y, Some z) ->
      let nextbb = new_block () in
      let yesbb  = new_block () in
      let naybb  = new_block () in
      let tmp    = ref nil in (* VAL (alloca false ty) in *)
      let typ    = ref VOID in
      int_exp env x (fun x ->
        let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in
        cond_br c yesbb naybb);
      position_at_end yesbb g_builder;
      exp env y (fun y ty ->
        typ := ty; tmp := VAL (alloca false (transl_typ env ty));
        store y !tmp; ignore (build_br nextbb g_builder));
      position_at_end naybb g_builder;
      typ_exp env z !typ (fun z -> store z !tmp; ignore (build_br nextbb g_builder));
      position_at_end nextbb g_builder;
      nxt (load !tmp) !typ
  | Pwhile (_, x, y) ->
      let nextbb = new_block () in
      let testbb = new_block () in
      let bodybb = new_block () in
      ignore (build_br testbb g_builder);
      position_at_end testbb g_builder;
      int_exp env x (fun x ->
        let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in
        cond_br c bodybb nextbb);
      position_at_end bodybb g_builder;
      void_exp { env with in_loop = InLoop nextbb } y
        (fun () -> ignore (build_br testbb g_builder));
      position_at_end nextbb g_builder;
      nxt nil VOID
  | Pfor (_, i, x, y, z) ->
      let nextbb = new_block () in
      let testbb = new_block () in
      let bodybb = new_block () in
      int_exp env x (fun x ->
      int_exp env y (fun y ->
        let a = alloca false (int_t 32) in
        let ii = VAL (a) in
        store x ii;
        ignore (build_br testbb g_builder);
        position_at_end testbb g_builder;
        let iii = load ii in
        let c = binop (build_icmp Icmp.Sle) iii y in
        cond_br c bodybb nextbb;
        position_at_end bodybb g_builder;
        void_exp (add_var i ~immutable:true INT (llvm_value iii) env) z (* M.add i (llvm_value iii)
      env) nextbb z (fun _ -> *)
        (fun () ->
          let plusone = binop build_add iii (const_int 32 1) in
          store plusone ii;
          ignore (build_br testbb g_builder))));
      position_at_end nextbb g_builder;
      nxt nil VOID
  | Pbreak p ->
      begin match env.in_loop with
      | InLoop bb -> ignore (build_br bb g_builder);
      | NoLoop    -> error p "illegal use of 'break'"
      end
  | Pletvar (_, x, None, y, z) ->
      exp env y (fun y ty ->
      let a = alloca (structured_type ty) (transl_typ env ty) in
      let env = add_var x ty a env in
      store y (VAL a);
      exp env z nxt)
  | Pletvar (p, x, Some t, Pnil _, z) ->
      let t = find_type t env in
      begin match t with
      | RECORD _ ->
          let a = alloca true (transl_typ env t) in
          let env = add_var x t a env in
          store (const_null (transl_typ env t)) (VAL a);
          exp env z nxt
      | _ ->
          error p "expected record type, found '%s'" (describe_type t)
      end
  | Pletvar (_, x, Some t, y, z) ->
      let ty = find_type t env in
      typ_exp env y ty (fun y ->
      let a = alloca (structured_type ty) (transl_typ env ty) in
      let env = add_var x ty a env in
      store y (VAL a);
      exp env z nxt)
  | Plettype (_, tys, e) ->
      let env = let_type env tys in
      exp env e nxt
  | Pletfuns (_, funs, e) ->
      let_funs env funs e nxt

let base_tenv =
  M.add "int" INT (M.add "string" STRING M.empty)

let base_venv =
  M.empty
  (* let stdlib =
    [ "print" , [STRING], VOID;
      "printi", [INT], VOID;
      "flush", [], VOID;
      "getchar", [], STRING;
      "ord", [STRING], INT;
      "chr", [INT], STRING;
      "size", [STRING], INT;
      "substring", [STRING; INT; INT], STRING;
      "concat", [STRING; STRING], STRING;
      "not", [INT], INT;
      "exit", [INT], VOID ] in
  List.fold_left (fun venv (x, ts, t) ->
    M.add x (Function (Id.make x, (ts, t))) venv) M.empty stdlib *)

let program e =
  let empty_env = { empty_env with tenv = base_tenv } in
  let main_fun = define_function "main"
    (function_type (int_t 32) [| |]) g_module in
  position_at_end (entry_block main_fun) g_builder;
  let startbb = new_block () in
  position_at_end startbb g_builder;
  exp empty_env e (fun _ _ -> ignore (build_ret (const_int0 32 0) g_builder));
  position_at_end (entry_block main_fun) g_builder;
  ignore (build_br startbb g_builder);
  dump_module g_module
