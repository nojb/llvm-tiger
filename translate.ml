open Globals
open Parsetree
open Typedtree
open Llvm

module M = Map.Make (String)

let debug () =
  Printf.ksprintf (fun message -> Printf.fprintf stderr "Debug: %s\n%!" message)

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
  VAL (build_gep (llvm_value v)
    (Array.of_list (List.map llvm_value vs)) "" g_builder)

let binop op v1 v2 =
  VAL (op (llvm_value v1) (llvm_value v2) "" g_builder)

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
  assert false
  (* insert_let (PTRTOINT v) (Tint 64) (fun ptr ->
  insert_let (BINOP (ptr, Op_cmp Cne, VINT (64, 0))) (Tint 1) (fun c ->
  CHECK (c, insert_let (GEP (v, [ VINT (32, 0); VINT (32, i+1) ])) tx nxt,
    Printf.sprintf "field access to nil record in line %d"
    p.Lexing.pos_lnum))) *)

(* Main typechecking/compiling functions *)

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

let rec var env breakbb v (nxt : llvm_value -> unit) =
  match v with
  | TVsimple (x, IsImm true) ->
      nxt (VAL (M.find x env))
  | TVsimple (x, IsImm false) ->
      nxt (LOADVAL (M.find x env))
  | TVsubscript (lnum, v, x) ->
      var env breakbb v (fun v ->
        let v = save (triggers x) v in
        exp env breakbb x (fun x ->
          let v = array_index lnum v x in
          nxt (load v)))
  | TVfield (lnum, v, i) ->
      var env breakbb v (fun v ->
        let v = record_index lnum v i in
        nxt (load v))

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
      nxt (binop build_add x y)))
  | Tbinop (x, Op_sub, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      nxt (binop build_sub x y)))
  | Tbinop (x, Op_mul, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      nxt (binop build_mul x y)))
  | Tbinop (x, Op_div, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      nxt (binop build_sdiv x y)))
  | Tbinop (x, Op_cmp Ceq, y) ->
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
      nxt (binop (build_icmp Icmp.Eq) x y)))
  | Tbinop _ ->
      failwith "binop not implemented"
  | Tassign (TVsimple (_, IsImm true), _) ->
      assert false
  | Tassign (TVsimple (x, IsImm false), e) ->
      exp env breakbb e (fun e ->
        store e (VAL (M.find x env));
        nxt nil)
  | Tassign (TVsubscript (lnum, v, e1), e2) ->
      var env breakbb v (fun v ->
        let v = save (triggers e1 || triggers e2) v in
        exp env breakbb e1 (fun e1 ->
        let v = array_index lnum v e1 in
        exp env breakbb e2 (fun e2 -> store e2 v; nxt nil)))
  | Tassign (TVfield (lnum, v, i), e) ->
      var env breakbb v (fun v ->
        let v = save (triggers e) v in
        let v = record_index lnum v i in
        exp env breakbb e (fun e -> store e v; nxt nil))
  | Tcall (x, xs) ->
      let rec bind ys = function
        | [] ->
            nxt (call (getfun x) (List.rev ys))
        | (ArgExp (x, IsPtr is_ptr)) :: xs ->
            exp env breakbb x (fun x ->
              let triggers = function ArgExp (x, _) -> triggers x | _ -> false in
              let x = save (is_ptr && List.exists triggers xs) x in
              bind (x :: ys) xs)
        | (ArgNonLocal x) :: xs ->
            bind (VAL (M.find x env) :: ys) xs
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
                  let f = gep r [ const_int 32 0; const_int 32 i] in
                  store v f;
                  bind (i+1) vs
            in bind 1 (List.rev vs)
        | (x, IsPtr is_ptr) :: xts ->
            exp env breakbb x (fun x ->
              let x = save is_ptr x in
              bind (x :: vs) xts)
      in bind [] xts
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Tif (x, y, z, IsVoid true, _) -> (* result is void *)
      let nextbb = new_block () in
      let yesbb  = new_block () in
      let naybb  = new_block () in
      exp env breakbb x (fun x ->
        let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in
        cond_br c yesbb naybb);
      position_at_end yesbb g_builder;
      exp env breakbb y (fun _ -> ignore (build_br nextbb g_builder));
      position_at_end naybb g_builder;
      exp env breakbb z (fun _ -> ignore (build_br nextbb g_builder));
      position_at_end nextbb g_builder;
      nxt nil
  | Tif (x, y, z, IsVoid false, ty) ->
      let nextbb = new_block () in
      let yesbb  = new_block () in
      let naybb  = new_block () in
      let tmp    = VAL (alloca false (transl_typ ty)) in
      exp env breakbb x (fun x ->
        let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in
        cond_br c yesbb naybb);
      position_at_end yesbb g_builder;
      exp env breakbb y (fun y -> store y tmp; ignore (build_br nextbb g_builder));
      position_at_end naybb g_builder;
      exp env breakbb z (fun z -> store z tmp; ignore (build_br nextbb g_builder));
      position_at_end nextbb g_builder;
      nxt (load tmp)
  | Twhile (x, y) ->
      let nextbb = new_block () in
      let testbb = new_block () in
      let bodybb = new_block () in
      ignore (build_br testbb g_builder);
      position_at_end testbb g_builder;
      exp env breakbb x (fun x ->
        let c = binop (build_icmp Icmp.Ne) x (const_int 32 0) in
        cond_br c bodybb nextbb);
      position_at_end bodybb g_builder;
      exp env nextbb y (fun _ -> ignore (build_br testbb g_builder));
      position_at_end nextbb g_builder;
      nxt nil
  | Tfor (i, x, y, z) ->
      let nextbb = new_block () in
      let testbb = new_block () in
      let bodybb = new_block () in
      exp env breakbb x (fun x ->
      exp env breakbb y (fun y ->
        let curr = insertion_block g_builder in
        ignore (build_br testbb g_builder);
        position_at_end testbb g_builder;
        let ii = phi [x, curr] in 
        let c = binop (build_icmp Icmp.Sle) ii y in
        cond_br c bodybb nextbb;
        position_at_end bodybb g_builder;
        exp (M.add i (llvm_value ii) env) nextbb z (fun _ ->
          let plusone = binop build_add ii (const_int 32 1) in
          let curr = insertion_block g_builder in
          add_incoming (llvm_value plusone, curr) (llvm_value ii);
          ignore (build_br testbb g_builder))));
      position_at_end nextbb g_builder;
      nxt nil
  | Tbreak ->
      ignore (build_br breakbb g_builder) (* ignore nxt *)
  | Tletvar (x, IsPtr is_ptr, ty, y, z) ->
      let a = alloca is_ptr (transl_typ ty) in
      exp env breakbb y (fun y ->
        store y (VAL a);
        exp (M.add x a env) breakbb z nxt)
  (* | Tletfuns (fundefs, e) ->
      let curr = insertion_block g_builder in
      let_funs env fundefs;
      position_at_end curr g_builder;
      exp env breakbb e nxt *)

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

let program fundefs =
  (* let main = define_function "main" (function_type (int_t 32) [| |]) g_module in
  position_at_end (entry_block main) g_builder; (* this is necessary so that neW_block works! *)
  let startbb = new_block () in
  position_at_end startbb g_builder;
  exp M.empty (entry_block main) e
    (fun _ -> ignore (build_ret (const_int0 32 0) g_builder));
  position_at_end (entry_block main) g_builder;
  ignore (build_br startbb g_builder);
  dump_module g_module *)

  let declare_fundef fundef =
    ignore (define_function fundef.fn_name
      (function_type (transl_typ fundef.fn_rtyp)
        (Array.of_list (List.map (fun (_, (t, _, IsFree is_free)) ->
          if is_free then pointer_type (transl_typ t) else (transl_typ t))
        fundef.fn_args)))
    g_module) in

  let define_fundef fundef =
    let f = getfun fundef.fn_name in
    position_at_end (entry_block f) g_builder;
    let startbb = new_block () in
    position_at_end startbb g_builder;
    let count = ref (-1) in
    let env = List.fold_left (fun env (n, (t, IsPtr is_ptr, IsFree is_free)) ->
      incr count;
      if not is_free then begin
        let a = alloca is_ptr (transl_typ t) in
        store (VAL (param f !count)) (VAL a);
        M.add n a env
      end else
        M.add n (param f !count) env) M.empty fundef.fn_args in
    exp env (entry_block f) fundef.fn_body
      (fun x -> ignore (build_ret (llvm_value x) g_builder));
    position_at_end (entry_block f) g_builder;
    ignore (build_br startbb g_builder) in

  List.iter declare_fundef fundefs;
  List.iter define_fundef fundefs;

  dump_module g_module
