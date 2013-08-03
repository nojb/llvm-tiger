open Globals
open Parsetree
open Typedtree
open Llvm

module M = Map.Make (String)

let fatal () =
  Printf.ksprintf (fun message -> failwith (Printf.sprintf "Fatal: %s\n%!" message))

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

  (* order matters *)
let const_int0 w n =
  const_int (int_t w) n

  (* This one shadows Llvm.const_int *)
let const_int w n =
  VAL (const_int (int_t w) n)

let const_null0 =
  const_null

let const_null t =
  VAL (const_null t)

(* let named_structs : (string * llvm_type list) list ref = ref [] *)

let rec transl_typ t =
  match t with
  | INT -> int_t 32
  | VOID -> int_t 32
  | ARRAY (_, t) ->
      pointer_type (struct_type g_context
        [| int_t 32; int_t 32; array_type (transl_typ t) 0 |])
  | _ -> assert false
  (* let visited : string list ref = ref [] in
  let rec loop t =
    match t with
    | INT -> Tint 32
    | VOID -> Tint 32
    | STRING -> Tpointer (Tint 8)
    | ARRAY (_, t) -> (* { i32, i32, [0 x t] }* *)
        Tpointer (Tstruct [| Tint 32; Tint 32; Tarray (0, transl_typ t) |])
    | RECORD (rname, uid) ->
        if not (List.exists (fun (x, _) -> x = Id.to_string uid) !named_structs)
        && not (List.mem (Id.to_string uid) !visited)
        then begin
          visited := (Id.to_string uid) :: !visited;
          named_structs := (Id.to_string uid,
            (Tint 32 :: List.map (fun (_, t) -> loop t) (M.find rname renv))) :: !named_structs
        end;
        Tpointer (Tnamedstruct (Id.to_string uid))
    | PLACE _ ->
        assert false
  in loop t *)

(* let rec structured_type t =
  match t with
  | PLACE _ -> assert false
  | STRING
  | ARRAY _
  | RECORD _ -> true
  | _ -> false *)

let array_exists p a =
  let rec loop i =
    if i >= Array.length a then false
    else if p a.(i) then true
    else loop (i+1)
  in loop 0

let rec triggers (e : Typedtree.exp) : bool =
  match e with
  | TCint _
  | TCstring _
  | TCnil _ -> false
  | Tvar (v) -> triggers_var v
  | Tbinop (e1, _, e2) -> triggers e1 || triggers e2
  | Tassign (v, e) -> triggers_var v || triggers e
  | Tcall _ -> true
  | Tseq (es) -> List.exists triggers es
  | Tmakearray _
  | Tmakerecord _ -> true
  | Tif (e1, e2, e3, _) -> triggers e1 || triggers e2 || triggers e3
  | Twhile (e1, e2) -> triggers e1 || triggers e2
  | Tfor (_, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Tbreak -> false
  | Tletvar (_, _, _, _, e1, e2) -> triggers e1 || triggers e2
  | Tletfuns (_, e) -> triggers e

and triggers_var = function
  | TVlocal _
  | TVnonLocal _ -> false
  | TVsubscript (_, v, e) -> triggers_var v || triggers e
  | TVfield (_, v, _) -> triggers_var v

  (*
let rec pure = function
  | Eundef
  | Eint _
  | T.Vstring _
  | T.Enull _
  | T.Eaddr _
  | T.Evar _ -> true
  | T.Eload e -> pure e
  | T.Ebinop (e1, _, e2) ->
      pure e1 && pure e2
  | T.Ecall (_, _, ea)
  | T.Ebuiltin (_, ea) ->
      array_exists pure ea
  | T.Egep (e, ea) ->
      pure e && array_exists pure ea
      *)

(* These utility functions are used in the processing of function definitions *)

(* Memory layout of arrays
 *
 * -----------------------------------------------
 * | i32 (gc tag) | i32 (no of elems) | elements |
 * -----------------------------------------------
 * 
 * This means that the type [T = array of t] is represented
 * by the following LLVM type:
 * 
 * %T = type { i32, i32, [0 x t] }*
 *
 * Thus given an llvm variable of type %T named a, in order
 * to reference its i-th element we need to use the gep
 * instruction as follows
 *
 * %a_i = getelementptr T %a, 0, 2, 0, i ; has type t*
 * *)

let size_of t = (* as a i32 *)
  const_ptrtoint (const_gep (const_null0 (ptr_t t))
    [| const_int0 32 1 |]) (int_t 32)

let malloc v =
  build_call (declare_function "malloc"
    (function_type (ptr_t (int_t 8)) [| int_t 32 |]) g_module)
    [| v |] "" g_builder

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

(* let add v1 v2 =
  VAL (build_add (llvm_value v1) (llvm_value v2) "" g_builder)

let mul v1 v2 =
  VAL (build_mul (llvm_value v1) (llvm_value v2) "" g_builder) *)

let load v nxt =
  nxt (VAL (build_load (llvm_value v) "" g_builder))

let nil =
  const_int 32 0

let store v p nxt =
  ignore (build_store (llvm_value v) (llvm_value p) g_builder);
  nxt (const_int 32 0)

let gep v vs nxt =
  nxt (VAL (build_gep (llvm_value v)
    (Array.of_list (List.map llvm_value vs)) "" g_builder))

let binop op v1 v2 nxt =
  nxt (VAL (op (llvm_value v1) (llvm_value v2) "" g_builder))

let call v0 vs =
  VAL (build_call v0 (Array.of_list (List.map llvm_value vs)) "" g_builder)

let phi incoming nxt =
  nxt (VAL (build_phi
    (List.map (fun (v, bb) -> llvm_value v, bb) incoming) "" g_builder))

let cond_br c yaybb naybb =
  ignore (build_cond_br (llvm_value c) yaybb naybb g_builder)

let array_length v (nxt : llvm_value -> unit) =
  gep v [ const_int 32 0; const_int 32 1 ] (fun l -> load l nxt)

let printf msg =
  ignore (build_call (declare_function "printf"
    (var_arg_function_type (int_t 32) [| ptr_t (int_t 8) |])
    g_module) [| build_global_stringptr msg "" g_builder |] "" g_builder)

let die msg =
  printf msg;
  ignore (build_call (declare_function "exit"
    (function_type void_t [| int_t 32 |]) g_module) [| const_int0 32 2 |] ""
    g_builder)

let array_index lnum v x nxt =
  let yesbb = new_block () in
  let diebb = new_block () in
  array_length v (fun l ->
  (* dump_value (llvm_value x);
  dump_value (llvm_value l); *)
  binop (build_icmp Icmp.Sle) x l (fun c1 ->
  binop (build_icmp Icmp.Sge) x (const_int 32 0) (fun c2 ->
  binop build_and c1 c2 (fun c -> cond_br c yesbb diebb)));
  position_at_end diebb g_builder;
  die (Printf.sprintf "Runtime error: index out of bounds in line %d\n" lnum);
  position_at_end yesbb g_builder;
  gep v [ const_int 32 0; const_int 32 2; x ] nxt)

let record_index lnum v i nxt =
  assert false
  (* insert_let (PTRTOINT v) (Tint 64) (fun ptr ->
  insert_let (BINOP (ptr, Op_cmp Cne, VINT (64, 0))) (Tint 1) (fun c ->
  CHECK (c, insert_let (GEP (v, [ VINT (32, 0); VINT (32, i+1) ])) tx nxt,
    Printf.sprintf "field access to nil record in line %d"
    p.Lexing.pos_lnum))) *)

(* Main typechecking/compiling functions *)

let save triggers v (nxt : llvm_value -> unit) =
  if triggers then
    match v with
    | LOADVAL _ -> nxt v
    | VAL v ->
        let a = alloca true (type_of v) in
        ignore (build_store v a g_builder);
        nxt (LOADVAL a)
  else
    nxt v

let rec var env breakbb v (nxt : llvm_value -> unit) =
  match v with
  | TVlocal (x, true) ->
      nxt (VAL (M.find x env))
  | TVlocal (x, false) ->
      nxt (LOADVAL (M.find x env))
  | TVnonLocal (dlvl, idx) ->
      assert false
  | TVsubscript (lnum, v, x) ->
      var env breakbb v (fun v ->
      save (triggers x) v (fun v ->
      exp env breakbb x (fun x ->
      array_index lnum v x (fun v ->
      load v nxt))))
  | TVfield (lnum, v, i) ->
      var env breakbb v (fun v ->
      record_index lnum v i (fun v ->
      load v nxt))

and exp env breakbb e (nxt : llvm_value -> unit) =
  match e with
  | TCint (n) ->
      nxt (const_int 32 n)
  (* | Pstring (_, s) ->
      nxt (Vstring s) STRING *)
  | TCnil t ->
      nxt (const_null (transl_typ t))
  | Tvar (v) ->
      var env breakbb v nxt
  | Tbinop (x, Op_add, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      binop build_add x y nxt))
  | Tbinop (x, Op_sub, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      binop build_sub x y nxt))
  | Tbinop (x, Op_mul, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      binop build_mul x y nxt))
  | Tbinop (x, Op_div, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      binop build_sdiv x y nxt))
  | Tbinop (x, Op_cmp Ceq, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      binop (build_icmp Icmp.Eq) x y nxt))
  | Tbinop _ ->
      failwith "binop not implemented"
  | Tassign (TVlocal (_, true), _) ->
      assert false
  | Tassign (TVlocal (x, false), e) ->
      exp env breakbb e (fun e ->
      store e (VAL (M.find x env)) nxt)
  | Tassign (TVnonLocal (dlvl, fp), e) ->
      assert false
      (* exp env lbreak e (fun e -> store e (Var x, M.find x env) nxt) *)
  | Tassign (TVsubscript (lnum, v, e1), e2) ->
      var env breakbb v (fun v ->
      save (triggers e1 || triggers e2) v (fun v ->
      exp env breakbb e1 (fun e1 ->
      array_index lnum v e1 (fun v ->
      exp env breakbb e2 (fun e2 -> store e2 v nxt)))))
  | Tassign (TVfield (lnum, v, i), e) ->
      var env breakbb v (fun v ->
      save (triggers e) v (fun v ->
      record_index lnum v i (fun v ->
      exp env breakbb e (fun e -> store e v nxt))))
  | Tcall (x, xs) ->
      let rec bind ys = function
        | [] ->
            nxt (call (getfun x) (List.rev ys))
        | (x, is_ptr) :: xs ->
            exp env breakbb x (fun x ->
              let triggersfst (x, _) = triggers x in
              save (is_ptr && List.exists triggersfst xs) x (fun x ->
              bind (x :: ys) xs))
      in bind [] xs
  | Tseq (xs) ->
      let rec bind = function
        | []      -> nxt nil
        | [x]     -> exp env breakbb x nxt
        | x :: x' -> exp env breakbb x (fun _ -> bind x')
      in
      bind xs
  | Tmakearray (t, y, z) ->
      exp env breakbb y (fun y ->
      exp env breakbb z (fun z ->
      let a = malloc (build_add (const_int0 32 8)
        (build_mul (llvm_value y) (size_of (transl_typ t)) "" g_builder)
        "" g_builder) in
       dump_value a;
      nxt (VAL (build_pointercast a (ptr_t (struct_type g_context
        [| int_t 32; int_t 32; array_type (transl_typ t) 0 |])) "" g_builder))))
  | Tmakerecord (t, xts) ->
      let rec bind vs = function
        | [] ->
            let t' = element_type (transl_typ t) in
            let r = VAL (build_malloc t' "" g_builder) in
            let rec bind i = function
              | [] -> nxt r
              | v :: vs ->
                  gep r [ const_int 32 0; const_int 32 i]
                    (fun f -> store v f (fun _ -> bind (i+1) vs))
            in bind 1 (List.rev vs)
        | (x, is_ptr) :: xts ->
            exp env breakbb x (fun x ->
              save is_ptr x (fun x ->
                bind (x :: vs) xts))
      in bind [] xts
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Tif (x, y, z, true) -> (* result is void *)
      let nextbb = new_block () in
      let yesbb  = new_block () in
      let naybb  = new_block () in
      exp env breakbb x (fun x ->
        binop (build_icmp Icmp.Ne) x (const_int 32 0) (fun c ->
        ignore (cond_br c yesbb naybb)));
      position_at_end yesbb g_builder;
      exp env breakbb y (fun _ -> ignore (build_br nextbb g_builder));
      position_at_end naybb g_builder;
      exp env breakbb z (fun _ -> ignore (build_br nextbb g_builder));
      position_at_end nextbb g_builder;
      nxt nil
  | Tif (x, y, z, false) ->
      let nextbb = new_block () in
      let yesbb  = new_block () in
      let naybb  = new_block () in
      let yy     = ref nil in
      let zz     = ref nil in
      exp env breakbb x (fun x ->
        binop (build_icmp Icmp.Ne) x (const_int 32 0) (fun c ->
        ignore (cond_br c yesbb nextbb)));
      position_at_end yesbb g_builder;
      exp env breakbb y (fun y -> yy := y; ignore (build_br nextbb g_builder));
      let yesbb = insertion_block g_builder in
      position_at_end naybb g_builder;
      exp env breakbb z (fun z -> zz := z; ignore (build_br nextbb g_builder));
      let naybb = insertion_block g_builder in
      position_at_end nextbb g_builder;
      phi [!yy, yesbb; !zz, naybb] nxt
  | Twhile (x, y) ->
      let nextbb = new_block () in
      let testbb = new_block () in
      let bodybb = new_block () in
      ignore (build_br testbb g_builder);
      position_at_end testbb g_builder;
      exp env breakbb x (fun x ->
        binop (build_icmp Icmp.Ne) x (const_int 32 0) (fun c ->
        ignore (cond_br c bodybb nextbb)));
      position_at_end bodybb g_builder;
      exp env nextbb y (fun _ -> ignore (build_br testbb g_builder));
      position_at_end nextbb g_builder;
      nxt nil
  | Tfor (i, x, y, z) ->
      let nextbb = new_block () in
      let testbb = new_block () in
      let bodybb = new_block () in
      let ir     = ref nil in
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
        let curr = insertion_block g_builder in
        ignore (build_br testbb g_builder);
        position_at_end testbb g_builder;
        phi [x, curr] (fun ii ->
          ir := ii;
          binop (build_icmp Icmp.Sle) ii y (fun c ->
          cond_br c bodybb nextbb));
        position_at_end bodybb g_builder;
        exp (M.add i (llvm_value !ir) env) nextbb z (fun _ ->
          binop build_add !ir (const_int 32 1) (fun plusone ->
          let curr = insertion_block g_builder in
          add_incoming (llvm_value plusone, curr) (llvm_value !ir);
          ignore (build_br testbb g_builder)))));
      position_at_end nextbb g_builder;
      nxt nil
  | Tbreak ->
      ignore (build_br breakbb g_builder) (* ignore nxt *)
  | Tletvar (x, acc, is_ptr, ty, y, z) ->
      begin match !acc with
      | Local ->
          let a = alloca is_ptr (transl_typ ty) in
          exp env breakbb y (fun y ->
          store y (VAL a) (fun _ ->
          exp (M.add x a env) breakbb z nxt))
      | NonLocal _ ->
          assert false
      end
  | Tletfuns (fundefs, e) ->
      let curr = insertion_block g_builder in
      let_funs env fundefs;
      position_at_end curr g_builder;
      exp env breakbb e nxt

and let_funs env fundefs =

  let declare_fundef fundef =
    ignore (define_function fundef.fn_name
      (function_type (transl_typ fundef.fn_rtyp)
        (Array.of_list (List.map (fun (_, (t, _, _)) -> transl_typ t)
        fundef.fn_args)))
    g_module) in

  let define_fundef fundef =
    let f = getfun fundef.fn_name in
    position_at_end (entry_block f) g_builder;
    let startbb = new_block () in
    position_at_end startbb g_builder;
    let count = ref (-1) in
    let env = List.fold_left (fun env (n, (t, _, is_ptr)) ->
      incr count;
      let a = alloca is_ptr (transl_typ t) in
      store (VAL (param f !count)) (VAL a) (fun _ -> ());
      M.add n a env) env fundef.fn_args in
    exp env (entry_block f) fundef.fn_body
      (fun x -> ignore (build_ret (llvm_value x) g_builder));
    position_at_end (entry_block f) g_builder;
    ignore (build_br startbb g_builder) in

  List.iter declare_fundef fundefs;
  List.iter define_fundef fundefs

  (*
let base_venv =
  let stdlib =
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
    M.add x (Function (Id.make x, (ts, t))) venv) M.empty stdlib
    *)

let program e =
  let main = define_function "main" (function_type (int_t 32) [| |]) g_module in
  position_at_end (entry_block main) g_builder; (* this is necessary so that neW_block works! *)
  let startbb = new_block () in
  position_at_end startbb g_builder;
  exp M.empty (entry_block main) e
    (fun _ -> ignore (build_ret (const_int0 32 0) g_builder));
  position_at_end (entry_block main) g_builder;
  ignore (build_br startbb g_builder);
  dump_module g_module
