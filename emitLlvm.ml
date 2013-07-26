open Globals
open Typedtree2
open Llvm

module P = Parsetree

module M = Map.Make (Id)

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

let strings = Hashtbl.create 10

let int_t w =
  integer_type (global_context ()) w

let ptr_t t =
  pointer_type t

let const_int ?bitwidth:(w=32) n =
  const_int (int_t w) n

let void_t =
  void_type (global_context ())

let rec typ = function
  | Tint w -> int_t w
  | Tstruct ts -> struct_type (global_context ()) (Array.map typ ts)
  | Tarray (n, t) -> array_type (typ t) n
  | Tpointer t -> pointer_type (typ t)
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
  | Vundef ->
      const_int 0
  | Vint (w, n) ->
      const_int ~bitwidth:w n
  | Vstring s -> begin
      try Hashtbl.find strings s
      with Not_found -> begin
        let ss = build_global_stringptr s "" the_builder in
        Hashtbl.add strings s ss; ss
      end
    end
  | Vnull t ->
      const_null (typ t)
  | Vload id ->
      build_load (M.find id env) "" the_builder
  | Vvar id ->
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

let rec exp env e =
  match e with
  | Ealloca (true, t) ->
      let b = builder_at_entry_block () in
      let v = alloca ~build:b (typ t) in
      gcroot ~build:b v;
      v
  | Ealloca (false, t) ->
      let b = builder_at_entry_block () in
      alloca ~build:b (typ t)
  | Emalloc t ->
      build_malloc (typ t) "" the_builder
  | Earraymalloc (sz, init) ->
      let vsz = value env sz in
      let vinit = value env init in
      let v = malloc (add (const_int 8) (mul vsz (size_of (type_of vinit)))) in
      pointercast v (ptr_t (struct_type (global_context ())
        [| int_t 32; int_t 32; array_type (type_of vinit) 0 |]))
  | Eload e ->
      load (value env e)
  | Ebinop (e1, op, e2) ->
      ((op2 op) (value env e1) (value env e2) "" the_builder)
  | Ecall (x, ea) ->
      call (M.find x env) (Array.map (value env) ea)
  | Egep (e, ea) ->
      gep (value env e) (Array.map (value env) ea)
  | Eassert (v, e, msg) ->
      let bb1 = new_block "yay" in
      let bb2 = new_block "nay" in
      cond_br (value env v) bb1 bb2;
      position_at_end bb2 the_builder;
      printf ("Runtime error: " ^ msg ^ "\n");
      ignore (call (declare_function "exit"
        (function_type void_t [| int_t 32 |])
        (global_module ())) [| const_int 2 |]);
      position_at_end bb1 the_builder;
      exp env e
  | Optrtoint v ->
      ptrtoint (value env v) (int_t 64)

type next_t =
  | Nstmt of next_t * stm
  | Ngoto of llbasicblock

let next_is_stm = function
  | Nstmt _ -> true
  | _ -> false

let rec next env lbreak = function
  | Nstmt (nxt, s) -> stm env lbreak nxt s
  | Ngoto lnext -> ignore (build_br lnext the_builder)

and stm env lbreak nxt s =
  match s with
  | Sskip ->
      next env lbreak nxt
  | Sseq (s1, s2) ->
      stm env lbreak (Nstmt (nxt, s2)) s1;
  | Sstore (e2, e1) ->
      store (value env e1) (value env e2);
      next env lbreak nxt
  | Sif (e, s1, s2) when next_is_stm nxt ->
      let bb1 = new_block "if.yay" in
      let bb2 = new_block "if.nay" in
      let bb3 = new_block "if.done" in
      cond_br (value env e) bb1 bb2;
      position_at_end bb1 the_builder;
      stm env lbreak (Ngoto bb3) s1;
      position_at_end bb2 the_builder;
      stm env lbreak (Ngoto bb3) s2;
      position_at_end bb3 the_builder;
      next env lbreak nxt
  | Sif (e, s1, s2) ->
      let bb1 = new_block "if.yay" in
      let bb2 = new_block "if.nay" in
      cond_br (value env e) bb1 bb2;
      position_at_end bb1 the_builder;
      stm env lbreak nxt s1;
      position_at_end bb2 the_builder;
      stm env lbreak nxt s2
  | Sloop (s) ->
      let bb = new_block "loop" in
      br bb;
      position_at_end bb the_builder;
      begin match nxt with
      | Ngoto lnext -> stm env lnext (Ngoto bb) s
      | Nstmt (nxt, s2) ->
          let bbdone = new_block "done" in
          stm env bbdone (Ngoto bb) s;
          position_at_end bbdone the_builder;
          stm env lbreak nxt s2
      end
  | Sbreak ->
      br lbreak;
  | Slet (id, _, e, s) ->
      let v = exp env e in
      set_value_name (Id.to_string id) v;
      stm (M.add id v env) lbreak nxt s
  | Sletrec _ ->
      assert false
  | Sreturn (None) ->
      ignore (build_ret_void the_builder)
  | Sreturn (Some e) ->
      ignore (build_ret (value env e) the_builder)

let rtyp fd =
  match fd.fn_rtyp with
  | None -> void_t
  | Some t -> typ t

let fn_header env fd =
  let args = Array.map (fun (_, t) -> typ t) (Array.of_list fd.fn_args) in
  let f = define_function (Id.to_string fd.fn_name)
    (function_type (rtyp fd) args) (global_module ()) in
  set_linkage Linkage.Internal f;
  M.add fd.fn_name f env

(* let add_var (id, _, t) env =
  M.add id (build_alloca (typ t) (Id.to_string id) the_builder) env *)

let fn_body env fd =
  let f = M.find fd.fn_name env in
  (* let b = L.builder_at_end (L.global_context ()) (L.entry_block f) in *)
  (* let env = List.fold_left2 (fun env (x, _) x' ->
    L.set_value_name (Id.to_string x) x';
    M.add x x' env) env fun_args (Array.to_list (L.params f)) in *)
  position_at_end (entry_block f) the_builder;
  stm env (entry_block f) (Ngoto (entry_block f)) fd.fn_body (* both
  L.entry_blocks's are just dummys *)

let program fd =
  initialize ();
  (* let env = List.fold_left (fn_body m) env fd in *)
  (* let env = fn_header M.empty fd in *)
  (* fn_body env fd; *)
  (* List.iter (fundec2 m env) fs;*)

  let main = define_function "main"
    (function_type (i32_type (global_context ())) [||]) (global_module ()) in
  let start = append_block (global_context ()) "start" main in
  List.iter (fun (rname, rftyps) ->
    let t = named_struct_type (global_context ()) rname in
    struct_types := (rname, t) :: !struct_types;
    struct_set_body t (Array.map typ rftyps) false) fd.prog_named;
  position_at_end start the_builder;
  ignore (stm M.empty (entry_block main) (Ngoto (entry_block main))
    fd.prog_body);
  position_at_end (entry_block main) the_builder;
  br start;
  global_module ()
