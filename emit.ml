open Globals
open Anf
open Llvm

module P = Parsetree

module M = Map.Make (Id)

let debug () =
  Printf.ksprintf (fun msg -> Printf.fprintf stderr "Debug: Emit: %s\n%!" msg)

let dllvm = ref false

(*
type context = {
  ctx_fn : llvalue;
  ctx_build : llbuilder;
  ctx_mod : llmodule;
  ctx_env : llvalue M.t
}
*)

let struct_types : (string * lltype) list ref = ref []

let the_module : llmodule option ref = ref None
let the_builder = builder (global_context ())

let initialize () =
  ( match !the_module with
  | Some m -> dispose_module m
  | None -> () );
  the_module := Some (create_module (global_context ()) "")

let global_module () =
  match !the_module with
  | None -> failwith "global_module: no global module"
  | Some m -> m

(* let strings = Hashtbl.create 10 *)

let int_t w =
  integer_type (global_context ()) w

let ptr_t t =
  pointer_type t

let const_int ?bitwidth:(w=32) n =
  const_int (int_t w) n

let void_t =
  void_type (global_context ())

let rec llvm_type = function
  | Tint w -> int_t w
  | Tstruct ts -> struct_type (global_context ()) (Array.map llvm_type ts)
  | Tarray (n, t) -> array_type (llvm_type t) n
  | Tpointer t -> pointer_type (llvm_type t)
  | Tnamedstruct n -> List.assoc n !struct_types

let op2 = function
  | P.Op_add -> build_add
  | P.Op_sub -> build_sub
  | P.Op_mul -> build_mul
  | P.Op_cmp P.Ceq -> build_icmp Icmp.Eq
  | P.Op_cmp P.Cle -> build_icmp Icmp.Sle
  | P.Op_cmp P.Cne -> build_icmp Icmp.Ne
  (* | A.Bin_and -> build_and
  | A.Bin_or -> build_or *)
  | _ -> assert false

(* let op1 = function
  | A.Un_not -> build_not
  | A.Un_neg -> build_neg
  | A.Un_bitcast t ->
      (fun x s b -> build_bitcast x (typ t) s b)
  | A.Un_inttoptr t ->
      (fun x s b -> build_inttoptr x (typ t) s b)
  | A.Un_ptrtoint w ->
      (fun x s b -> build_ptrtoint x (integer_type c w) s b) *)

let malloc v =
  build_call (declare_function "malloc"
    (function_type (ptr_t (int_t 8)) [| int_t 32 |]) (global_module ()))
    [| v |] "" the_builder

let rec value env v =
  match v with
  | VUNDEF ->
      const_int 0
  | VINT (w, n) ->
      const_int ~bitwidth:w n
  | VNULL t ->
      const_null (llvm_type t)
  | VLOAD id ->
      build_load (M.find id env) "" the_builder
  | VVAR id ->
      M.find id env

let size_of t = (* as a i32 *)
  const_ptrtoint (const_gep (const_null (ptr_t t))
    [| const_int 1 |]) (int_t 32)

let new_block name =
  let f = block_parent (insertion_block the_builder) in
  let bb = append_block (global_context ()) name f in
  bb

let alloca ?build:(b=the_builder) t
  = build_alloca t "" b
let pointercast ?build:(b=the_builder) v t
  = build_pointercast v t "" b
let add v1 v2
  = build_add v1 v2 "" the_builder
let mul v1 v2
  = build_mul v1 v2 "" the_builder
let call ?build:(b=the_builder) f va
  = build_call f va "" b
let load v
  = build_load v "" the_builder
let gep v va
  = build_gep v va "" the_builder
let br bb
  = ignore (build_br bb the_builder)
let cond_br v bb1 bb2
  = ignore (build_cond_br v bb1 bb2 the_builder)
let store v p
  = ignore (build_store v p the_builder)
let ptrtoint v t
  = build_ptrtoint v t "" the_builder

let gcroot ?build:(b=the_builder) v =
  let vb = pointercast ~build:b v (ptr_t (ptr_t (int_t 8))) in
  ignore (call ~build:b (declare_function "llvm.gcroot"
    (function_type void_t [| ptr_t (ptr_t (int_t 8)); ptr_t (int_t 8) |])
  (global_module ())) [| vb; const_null (ptr_t (int_t 8)) |])

let printf msg =
  ignore (call (declare_function "printf"
    (var_arg_function_type (int_t 32) [| ptr_t (int_t 8) |])
    (global_module ())) [| build_global_stringptr msg "" the_builder |])

let builder_at_entry_block () =
  builder_at_end (global_context ())
    (entry_block (block_parent (insertion_block the_builder)))

let rec cexp env e =
  match e with
    VAL (v) ->
      value env v
  | ALLOCA (true, t) ->
      let b = builder_at_entry_block () in
      let v = alloca ~build:b (llvm_type t) in
      gcroot ~build:b v;
      v
  | ALLOCA (false, t) ->
      let b = builder_at_entry_block () in
      alloca ~build:b (llvm_type t)
  | MALLOC t ->
      build_malloc (llvm_type t) "" the_builder
  | ARRAY_MALLOC (sz, init) ->
      let vsz = value env sz in
      let vinit = value env init in
      let v = malloc (add (const_int 8) (mul vsz (size_of (type_of vinit)))) in
      pointercast v (ptr_t (struct_type (global_context ())
        [| int_t 32; int_t 32; array_type (type_of vinit) 0 |]))
  | LOAD e ->
      load (value env e)
  | STORE (e2, e1) ->
      store (value env e1) (value env e2);
      const_int 0
  | BINOP (e1, op, e2) ->
      ((op2 op) (value env e1) (value env e2) "" the_builder)
  | CALL (x, ea) ->
      call (M.find x env) (Array.of_list (List.map (value env) ea))
  | GEP (e, ea) ->
      gep (value env e) (Array.of_list (List.map (value env) ea))
  | PTRTOINT v ->
      ptrtoint (value env v) (int_t 64)

type block_info =
  | Fresh of block_info ref M.t * llvalue M.t * exp * (Id.t * llvm_type) list
  | Emitted of llbasicblock * llvalue list

let rec goto benv venv blk vs =
  let bi = M.find blk benv in
  match !bi with
  | Fresh (benv, venv, e, phis) ->
      let blk' = new_block "" in
      let curr = insertion_block the_builder in
      position_at_end blk' the_builder;
      let phis' = List.map (fun v -> build_phi [value venv v, curr] "" the_builder) vs in
      let venv' = List.fold_left2 (fun venv (phi, _) phi' -> M.add phi phi' venv)
        venv phis phis' in
      bi := Emitted (blk', phis');
      exp (M.add blk bi benv) venv' e;
      position_at_end curr the_builder;
      br blk'
  | Emitted (blk, phis) ->
      List.iter2 (fun v phi ->
        add_incoming (value venv v, insertion_block the_builder) phi) vs
        phis;
      br blk

and if_exp benv venv e =
  let curr = insertion_block the_builder in
  let blk = new_block "" in
  position_at_end blk the_builder;
  exp benv venv e;
  position_at_end curr the_builder;
  blk

and exp benv venv = function
    DIE msg ->
      printf msg;
      ignore (call (declare_function "exit"
        (function_type void_t [| int_t 32 |])
        (global_module ())) [| const_int 2 |])
  | IF (v, e1, e2) ->
      cond_br (value venv v) (if_exp benv venv e1) (if_exp benv venv e2)
  | LET_BLOCK (blk, phis, e1, e2) ->
      let benv' = M.add blk (ref (Fresh (benv, venv, e1, phis))) benv in
      exp benv' venv e2
  | LET (id, _, c, e) ->
      let v = cexp venv c in
      set_value_name (Id.to_string id) v;
      exp benv (M.add id v venv) e
  | LET_REC _ ->
      assert false
  | RETURN c ->
      ignore (build_ret (cexp venv c) the_builder)
  | GOTO (blk, vs) ->
      goto benv venv blk vs

let rtyp fd =
  match fd.fn_rtyp with
  | None -> void_t
  | Some t -> llvm_type t

let fn_header env fd =
  let args = Array.map (fun (_, t) -> llvm_type t) (Array.of_list fd.fn_args) in
  let f = define_function (Id.to_string fd.fn_name)
    (function_type (rtyp fd) args) (global_module ()) in
  set_linkage Linkage.Internal f;
  M.add fd.fn_name f env

let fn_body env fd =
  let f = M.find fd.fn_name env in
  position_at_end (entry_block f) the_builder; (* XXX not needed *)
  let env = List.fold_left2 (fun env (x, _) x' ->
    (* L.set_value_name (Id.to_string x) x'; *)
    M.add x x' env) env fd.fn_args (Array.to_list (params f)) in
  let start = append_block (global_context ()) "start" f in
  position_at_end start the_builder;
  exp M.empty env fd.fn_body;
  position_at_end (entry_block f) the_builder;
  br start

let program fd =
  debug () "in Emit";

  initialize ();

  let env = List.fold_left fn_header M.empty fd.prog_funs in
  List.iter (fn_body env) fd.prog_funs;

  let main = define_function "main"
    (function_type (i32_type (global_context ())) [||]) (global_module ()) in
  let start = append_block (global_context ()) "start" main in
  List.iter (fun (rname, rftyps) ->
    let t = named_struct_type (global_context ()) rname in
    struct_types := (rname, t) :: !struct_types;
    struct_set_body t (Array.of_list (List.map llvm_type rftyps)) false) fd.prog_named;
  position_at_end start the_builder;
  exp M.empty env fd.prog_body;
  position_at_end (entry_block main) the_builder;
  br start;
  global_module ()
