open IL
open Llvm

module M = Map.Make (String)
module LM = Map.Make (Label)
module LS = Set.Make (Label)

let debug () =
  Printf.ksprintf (fun msg ->
    Printf.fprintf stderr "Debug: EmitIL: %s\n%!" msg)

let fatal () =
  Printf.ksprintf (fun msg ->
    failwith (Printf.sprintf "Fatal: EmitIL: %s\n%!" msg))

let dllvm = ref false

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

let malloc v =
  build_call (declare_function "malloc"
    (function_type (ptr_t (int_t 8)) [| int_t 32 |]) (global_module ()))
    [| v |] "" the_builder

let value env = function
  | Undef ->
      const_int ~bitwidth:32 0
  | Int (w, n) ->
      const_int ~bitwidth:w n
  | Null t ->
      const_null (llvm_type t)
  | Global n ->
      begin match lookup_global n (global_module ()) with
      | Some v -> v
      | None -> assert false
      end
  | Function f ->
      begin match lookup_function f (global_module ()) with
      | Some v -> v
      | None -> assert false
      end
  | Var id ->
      M.find id env
  | Loadvar id ->
      build_load (M.find id env) "" the_builder

let mem_value v env =
  match v with
  | Undef
  | Int _
  | Null _
  | Global _
  | Function _ -> true
  | Var id
  | Loadvar id -> M.mem id env

let size_of t = (* as a i32 *)
  const_ptrtoint (const_gep (const_null (ptr_t t))
    [| const_int 1 |]) (int_t 32)

let gcroot ?build:(b=the_builder) v =
  let vb = build_pointercast v (ptr_t (ptr_t (int_t 8))) "" b in
  ignore (build_call (declare_function "llvm.gcroot"
    (function_type void_t [| ptr_t (ptr_t (int_t 8)); ptr_t (int_t 8) |])
  (global_module ())) [| vb; const_null (ptr_t (int_t 8)) |] "" b)

let printf msg =
  ignore (build_call (declare_function "printf"
    (var_arg_function_type (int_t 32) [| ptr_t (int_t 8) |])
    (global_module ())) [| build_global_stringptr msg "" the_builder |] ""
    the_builder)

let builder_at_entry_block () =
  builder_at_end (global_context ())
    (entry_block (block_parent (insertion_block the_builder)))

let llvm_binary = function
  | Add -> build_add
  | Sub -> build_sub
  | Mul -> build_mul
  | Div -> build_sdiv
  | Icmp Eq -> build_icmp Icmp.Eq
  | Icmp Ne -> build_icmp Icmp.Ne
  | Icmp Le -> build_icmp Icmp.Sle
  | Icmp Lt -> build_icmp Icmp.Slt
  | Icmp Ge -> build_icmp Icmp.Sge
  | Icmp Gt -> build_icmp Icmp.Sgt

let llvm_unary = function
  | Ptrtoint ty ->
      (fun v dst build -> build_ptrtoint v (llvm_type ty) dst build)

type env = {
  lenv : llbasicblock LM.t;
  venv : llvalue M.t;
  phis : (llvalue * label * value) list
}

let rec block env b =
  let add x v env =
    { env with venv = M.add x v env.venv } in
  let value env v =
    value env.venv v in
  let add_phi phi lbl v env =
    { env with phis = (phi, lbl, v) :: env.phis } in
  match b with
  | Binary (dst, op, v1, v2, nxt) ->
      block (add dst
        (llvm_binary op
        (value env v1) (value env v2) dst the_builder) env) nxt
  | Unary (dst, op, v, nxt) ->
      block (add dst (llvm_unary op (value env v) dst the_builder) env) nxt
  | Alloca (dst, ty, true, nxt) ->
      let build = builder_at_entry_block () in
      let v = build_alloca (llvm_type ty) dst build in
      gcroot ~build:build v;
      block (add dst v env) nxt
  | Alloca (dst, ty, false, nxt) ->
      let build = builder_at_entry_block () in
      block (add dst (build_alloca (llvm_type ty) dst build) env) nxt
  | Malloc (dst, ty, nxt) ->
      block (add dst (build_malloc (llvm_type ty) dst the_builder) env) nxt
  | Load (dst, v, nxt) ->
      block (add dst (build_load (value env v) dst the_builder) env) nxt
  | Gep (dst, v, vs, nxt) ->
      block (add dst (build_gep (value env v)
        (Array.of_list (List.map (value env) vs)) dst the_builder) env) nxt
  | Phi (dst, lvs, nxt) ->
      let good, bad = List.partition (fun (_, v) -> mem_value v env.venv) lvs in
      if List.length good = 0 then
        fatal () "phi 'good' incoming values has no good ones";
      let phi = build_phi (List.map (fun (lbl, v) ->
          (value env v, LM.find lbl env.lenv)) good) dst the_builder in
      let env = List.fold_left (fun env (lbl, v) ->
        add_phi phi lbl v env) env bad in
      block env nxt
      (* block (add dst (build_phi 
        (List.map (fun (lbl, v) -> (value env v, M.find lbl env.lenv)) good) dst
        the_builder) env) nxt (* XXX *) *)
  | Call (dst, v, vs, nxt) ->
      block (add dst (build_call (value env v)
        (Array.of_list (List.map (value env) vs)) dst the_builder) env) nxt
  | Store (v1, v2, nxt) ->
      ignore (build_store (value env v1) (value env v2) the_builder);
      block env nxt
  | Condbr (v, lbl1, lbl2) ->
      ignore (build_cond_br (value env v)
        (LM.find lbl1 env.lenv) (LM.find lbl2 env.lenv) the_builder);
      env, [lbl1; lbl2]
  | Br (lbl) ->
      ignore (build_br (LM.find lbl env.lenv) the_builder);
      env, [lbl]
  | Ret (None) ->
      ignore (build_ret_void the_builder);
      env, []
  | Ret (Some v) ->
      ignore (build_ret (value env v) the_builder);
      env, []

(* let die msg =
  let blk = new_block "" in
  let curr = insertion_block the_builder in
  position_at_end blk the_builder;
  printf msg;
  ignore (call (declare_function "exit"
    (function_type void_t [| int_t 32 |])
    (global_module ())) [| const_int 2 |]);
  position_at_end curr the_builder;
  blk *)

let fn_header fd =
  let args_ty = List.map snd fd.args in
  let args_ty = List.map llvm_type args_ty in
  let args_ty = Array.of_list args_ty in
  let ret_ty = match fd.rtyp with None -> void_t | Some t -> llvm_type t in
  let f = define_function fd.name (function_type ret_ty args_ty) (global_module ()) in
  set_linkage Linkage.Internal f

let get_function n =
  match lookup_function n (global_module ()) with
  | Some v -> v
  | None -> assert false

let fn_body fundef =
  let f = get_function fundef.name in
  let env =
    let count = ref (-1) in
    List.fold_left (fun env (x, _) ->
      incr count;
      M.add x (param f !count) env) M.empty fundef.args in
  let lenv = LM.fold (fun (L n as lbl) _ lenv ->
    let blk = append_block (global_context ()) n f in
    LM.add lbl blk lenv) fundef.body LM.empty in
  let rec loop visited env lbl =
    if LS.mem lbl visited then ()
    else begin
      let visited = LS.add lbl visited in
      position_at_end (LM.find lbl lenv) the_builder;
      let env, follow = block env (LM.find lbl fundef.body) in
      (* let follow = List.filter (fun lbl -> not (LS.mem lbl visited)) follow in
  * *)
      let good, bad = List.partition (fun (_, lbl', _) ->
        LS.mem lbl' visited && List.mem lbl' follow) env.phis in
      List.iter (fun (phi, lbl, v) ->
        add_incoming (value env.venv v, LM.find lbl lenv) phi) good;
      let env = { env with phis = bad } in
      List.iter (fun n -> loop visited env n) follow
    end
  in
  loop LS.empty { lenv = lenv; venv = env; phis = [] } fundef.main;
  position_at_end (entry_block f) the_builder;
  ignore (build_br (LM.find fundef.main lenv) the_builder)

let program fundefs =
  initialize ();

  List.iter fn_header fundefs;
  List.iter fn_body fundefs;

  global_module ()
