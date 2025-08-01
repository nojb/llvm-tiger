open Llvm

type ty =
  | Tvoid
  | Tstruct of ty array
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer
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
  | Pcmpint of comparison
  | Ialloca of ty
  | Iapply of string
  | Iexternal of string * signature

module Label = struct
  type t = int
  type state = int ref
  let create () = ref 0
  let next state = incr state; !state
  module Map = Map.Make(Int)
end

module Ident = struct
  type t = int
  type state = int ref
  let create () = ref 0
  let next state = incr state; !state
  module Map = Map.Make(Int)
end

type ident = Ident.t

type label = Label.t

type instruction =
  | Iop of operation * ident list * ident * instruction
  | Iload of ty * ident * ident * instruction
  | Istore of ident * ident * instruction
  | Iifthenelse of ident * label * label
  | Igoto of label
  | Ireturn of ident option

type program =
  {
    name: string;
    vars: unit Ident.Map.t;
    code: instruction Label.Map.t;
    entrypoint: instruction;
  }

let rec print_typ ppf ty =
  let open Format in
  match ty with
  | Tint w -> fprintf ppf "i%i" w
  | Tpointer -> fprintf ppf "ptr"
  | Tarray (t, n) -> fprintf ppf "a%i%a" n print_typ t
  | Tnamed s -> fprintf ppf "%s" s
  | Tvoid -> fprintf ppf "void"
  | Tstruct _ -> assert false

let print_args ppf args =
  let open Format in
  List.iteri (fun i arg ->
      if i > 0 then fprintf ppf ", ";
      fprintf ppf "x%i" arg
    ) args

let print_operation ppf op args _res =
  let open Format in
  match op, args with
  | Pconstint n, _ ->
      fprintf ppf "%li" n
  | Paddint, [arg1; arg2] ->
      fprintf ppf "x%i + x%i" arg1 arg2
  | Psubint, [arg1; arg2] ->
      fprintf ppf "x%i - x%i" arg1 arg2
  | Pmulint, [arg1; arg2] ->
      fprintf ppf "x%i * x%i" arg1 arg2
  | Pdivint, [x1; x2] ->
      fprintf ppf "x%i / x%i" x1 x2
  | Pgep, [x] ->
      fprintf ppf "gep x%i, ..." x
  | Pcmpint _, _ ->
      fprintf ppf "cmp"
  | Ialloca ty, [x] ->
      fprintf ppf "x%i = alloca %a" x print_typ ty
  | Iapply (f), [x]
  | Iexternal (f, _), [x] ->
      fprintf ppf "x%i = %s(%a)" x f print_args args
  | _ ->
      assert false

let rec print_instruction ppf i =
  let open Format in
  let next =
    match i with
    | Iop (op, args, res, next) ->
        print_operation ppf op args res;
        Some next
    | Iload (_ty, arg, res, next) ->
        fprintf ppf "x%i = !x%i" res arg;
        Some next
    | Istore (src, dst, next) ->
        fprintf ppf "x%i := x%i" dst src;
        Some next
    | Iifthenelse (cond, ifso, ifnot) ->
        fprintf ppf "if x%i then goto L%i else goto L%i" cond ifso ifnot;
        None
    | Igoto lbl ->
        fprintf ppf "goto L%i" lbl;
        None
    | Ireturn None ->
        fprintf ppf "ret";
        None
    | Ireturn (Some arg) ->
        fprintf ppf "ret x%i" arg;
        None
  in
  match next with
  | None -> ()
  | Some next -> fprintf ppf "@,%a" print_instruction next

let _print_instruction ppf i =
  Format.fprintf ppf "@[<v>%a@]@." print_instruction i

  (*
type fundecl =
  {
    name: string;
    args: ident list;
    signature: signature;
    code: instruction Label.Map.t;
    entrypoint: instruction;
  }

let print_fundecl ppf f =
  let open Format in
  fprintf ppf "@[<v>%s(%a):@,%a@]@." f.name print_args f.args print_instruction f.entrypoint *)

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
  | Tpointer ->
      pointer_type (module_context m)
  | Tint width ->
      integer_type c width

let transl_operation m b op args =
  match op, args with
  | Pconstint n, [] ->
      let c = module_context m in
      const_of_int64 (i32_type c) (Int64.of_int32 n) false
  | Paddint, [arg1; arg2] ->
      build_add arg1 arg2 "" b
  | Psubint, [arg1; arg2] ->
      build_sub arg1 arg2 "" b
  | Pmulint, [arg1; arg2] ->
      build_mul arg1 arg2 "" b
  | Pdivint, [arg1; arg2] ->
      build_sdiv arg1 arg2 "" b
  | Pgep, _ ->
      assert false
  (* [|build_gep _ arg.(0) (Array.sub arg 1 (Array.length arg - 1)) "" b|] *)
  | Ialloca ty, [] ->
      build_alloca (transl_ty m ty) "" b
  | Iapply f, _ ->
      let _f =
        match lookup_function f m with
        | None -> assert false
        | Some f -> f
      in
      assert false
  (* [|build_call _ f arg "" b|] *)
  | Iexternal (f, (tys, ty)), _ ->
      let _f =
        declare_function f (function_type (transl_ty m ty) (Array.map (transl_ty m) tys)) m
      in
      assert false
  (* [|build_call _ f arg "" b|] *)
  | _ ->
      assert false

let rec transl_instr env m b i lgoto =
  match i with
  | Iop (op, args, res, next) ->
      let args = List.map (fun id -> Ident.Map.find id env) args in
      let vres = transl_operation m b op args in
      let env = Ident.Map.add res vres env in
      transl_instr env m b next lgoto
  | Iload (ty, arg, res, next) ->
      let v = build_load (transl_ty m ty) (Ident.Map.find arg env) "" b in
      transl_instr (Ident.Map.add res v env) m b next lgoto
  | Istore (src, dst, next) ->
      ignore (build_store (Ident.Map.find src env) (Ident.Map.find dst env) b);
      transl_instr env m b next lgoto
  | Iifthenelse (cond, ifso, ifnot) ->
      let lifso = Label.Map.find ifso lgoto in
      let lifnot = Label.Map.find ifnot lgoto in
      ignore (build_cond_br (Ident.Map.find cond env) lifso lifnot b)
  | Igoto lbl ->
      ignore (build_br (Label.Map.find lbl lgoto) b)
  | Ireturn (Some arg) ->
      ignore (build_ret (Ident.Map.find arg env) b)
  | Ireturn None ->
      ignore (build_ret_void b)
(*
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
  let _, env =
    let aux (n, env) arg = n + 1, Ident.Map.add arg (param v n) env in
    List.fold_left aux (0, Ident.Map.empty) f.args
  in
  let lgoto = Label.Map.map (fun _ -> append_block c "" v) f.code in
  let transl_block block i = position_at_end block b; transl_instr env m b i lgoto in
  transl_block (entry_block v) f.entrypoint;
  Label.Map.iter (fun lbl i -> transl_block (Label.Map.find lbl lgoto) i) f.code *)

let transl_program (p : program) =
  let c = global_context () in
  let m = create_module c p.name in
  let v = define_function "TIG_main" (function_type (void_type c) [||]) m in
  let b = builder c in
  let env = Ident.Map.empty in
  let lgoto = Label.Map.map (fun _ -> append_block c "" v) p.code in
  let transl_block block i = position_at_end block b; transl_instr env m b i lgoto in
  transl_block (entry_block v) p.entrypoint;
  Label.Map.iter (fun lbl i -> transl_block (Label.Map.find lbl lgoto) i) p.code;
  m
