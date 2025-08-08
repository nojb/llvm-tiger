open Llvm

type ty =
  | Tvoid
  | Tstruct of ty array
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer
  | Tint of int

type signature = ty array * ty

type array_kind =
  | Int | Pointer

type operation =
  | Pconstint of int64
  | Pnull
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep of ty
  | Pcmpint of Tabs.comparison
  | Pzext
  | Ialloca of ty * bool
  | Iapply of string
  | Iexternal of string * signature
  | Imakearray of array_kind
  | Imakerecord of int
  | Imakestring of string

module Reg = struct
  type t = int
  type state = int ref
  let create () = ref 0
  let next state = incr state; !state
  module Map = Map.Make(Int)
end

module Label = struct
  type t = int
  type state = int ref
  let create () = ref 0
  let next state = incr state; !state
  module Map = Map.Make(Int)
  module Tbl = Hashtbl.Make(Int)
end

type reg = Reg.t

type label = Label.t

type instruction =
  | Iop of operation * reg list * reg * instruction
  | Iload of ty * reg * reg * instruction
  | Istore of reg * reg * instruction
  | Iifthenelse of reg * label * label
  | Igoto of label
  | Ireturn of reg option
  | Iunreachable

type program =
  {
    name: string;
    code: instruction Label.Map.t;
    entrypoint: instruction;
  }

let intptr_type c =
  assert (Sys.word_size = 64);
  i64_type c

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
      fprintf ppf "%Li" n
  | Paddint, [arg1; arg2] ->
      fprintf ppf "x%i + x%i" arg1 arg2
  | Psubint, [arg1; arg2] ->
      fprintf ppf "x%i - x%i" arg1 arg2
  | Pmulint, [arg1; arg2] ->
      fprintf ppf "x%i * x%i" arg1 arg2
  | Pdivint, [x1; x2] ->
      fprintf ppf "x%i / x%i" x1 x2
  | Pgep _, [x] ->
      fprintf ppf "gep x%i, ..." x
  | Pcmpint _, _ ->
      fprintf ppf "cmp"
  | Ialloca (ty, _), [x] ->
      fprintf ppf "x%i = alloca %a" x print_typ ty
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
    | Iunreachable ->
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
    args: reg list;
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

let gcroot m b v =
  let c = module_context m in
  let lltype = function_type (void_type c) [|pointer_type c; pointer_type c|] in
  let f = declare_function "llvm.gcroot" lltype m in
  ignore (build_call lltype f [|v; const_null (pointer_type c)|] "" b)

let transl_operation m b op args =
  match op, args with
  | Pconstint n, [] ->
      let c = module_context m in
      const_of_int64 (intptr_type c) n false
  | Pnull, [] ->
      const_null (pointer_type (module_context m))
  | Paddint, [arg1; arg2] ->
      build_add arg1 arg2 "" b
  | Psubint, [arg1; arg2] ->
      build_sub arg1 arg2 "" b
  | Pmulint, [arg1; arg2] ->
      build_mul arg1 arg2 "" b
  | Pdivint, [arg1; arg2] ->
      build_sdiv arg1 arg2 "" b
  | Pcmpint c, [r1; r2] ->
      let c =
        match c with
        | Ceq -> Icmp.Eq | Cne -> Icmp.Ne | Cle -> Icmp.Sle
        | Clt -> Icmp.Slt | Cge -> Icmp.Sge | Cgt -> Icmp.Sgt
      in
      build_icmp c r1 r2 "" b
  | Pzext, [r] ->
      build_zext r (intptr_type (module_context m)) "" b
  | Pgep ty, (r0 :: rl) ->
      build_gep (transl_ty m ty) r0 (Array.of_list rl) "" b
  | Ialloca (ty, root), [] ->
      let v = build_alloca (transl_ty m ty) "" b in
      if root then begin
        ignore (build_store (const_null (pointer_type (module_context m))) v b);
        gcroot m b v;
      end;
      v
  | Iapply f, _ ->
      let _f =
        match lookup_function f m with
        | None -> assert false
        | Some f -> f
      in
      assert false
  (* [|build_call _ f arg "" b|] *)
  | Iexternal (f, (tys, ty)), args ->
      let lltype = function_type (transl_ty m ty) (Array.map (transl_ty m) tys) in
      let f = declare_function f lltype m in
      build_call lltype f (Array.of_list args) "" b
  | Imakearray ty, [size; init] ->
      let fname, argty =
        match ty with
        | Int -> "TIG_makeintarray", Tint 64
        | Pointer -> "TIG_makeptrarray", Tpointer
      in
      let c = module_context m in
      let ty = function_type (pointer_type c) [|intptr_type c; transl_ty m argty|] in
      let f = declare_function fname ty m in
      build_call ty f [|size; init|] "" b
  | Imakerecord n, [] ->
      let c = module_context m in
      let ty = function_type (pointer_type c) [|i32_type c|] in
      let f = declare_function "TIG_makerecord" ty m in
      build_call ty f [|const_int (i32_type c) n|] "" b
  | Imakestring s, [] ->
      let c = module_context m in
      let ty = function_type (pointer_type c) [|transl_ty m Tpointer|] in
      let f = declare_function "TIG_makestring" ty m in
      build_call ty f [|build_global_stringptr s "" b|] "" b
  | (Pconstint _ | Pnull | Paddint | Psubint | Pmulint | Pdivint | Pcmpint _ |
     Pzext | Pgep _ | Ialloca _ | Imakearray _ |
     Imakerecord _ | Imakestring _), _ ->
      assert false

type env =
  {
    f: llvalue;
    code: instruction Label.Map.t;
    blocks: llbasicblock Label.Tbl.t;
    regs: llvalue Reg.Map.t;
  }

let add_var env reg v =
  {env with regs = Reg.Map.add reg v env.regs}

let find_var env reg =
  Reg.Map.find reg env.regs

let find_code env lbl =
  Label.Map.find lbl env.code

let rec transl_instr env m b i =
  match i with
  | Iop (op, args, res, next) ->
      let args = List.map (find_var env) args in
      let vres = transl_operation m b op args in
      transl_instr (add_var env res vres) m b next
  | Iload (ty, arg, res, next) ->
      let v = build_load (transl_ty m ty) (find_var env arg) "" b in
      transl_instr (add_var env res v) m b next
  | Istore (src, dst, next) ->
      ignore (build_store (find_var env src) (find_var env dst) b);
      transl_instr env m b next
  | Iifthenelse (cond, ifso, ifnot) ->
      let bbyay = transl_block env m ifso in
      let bbnay = transl_block env m ifnot in
      ignore (build_cond_br (find_var env cond) bbyay bbnay b)
  | Igoto lbl ->
      let bb = transl_block env m lbl in
      ignore (build_br bb b)
  | Ireturn (Some arg) ->
      ignore (build_ret (find_var env arg) b)
  | Ireturn None ->
      ignore (build_ret_void b)
  | Iunreachable ->
      ignore (build_unreachable b)

and transl_block env m lbl =
  match Label.Tbl.find_opt env.blocks lbl with
  | Some bb -> bb
  | None ->
      let c = module_context m in
      let bb = append_block c "" env.f in
      Label.Tbl.add env.blocks lbl bb;
      let b = builder c in
      position_at_end bb b;
      transl_instr env m b (find_code env lbl);
      bb

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
    let aux (n, env) arg = n + 1, Reg.Map.add arg (param v n) env in
    List.fold_left aux (0, Reg.Map.empty) f.args
  in
  let lgoto = Label.Map.map (fun _ -> append_block c "" v) f.code in
  let transl_block block i = position_at_end block b; transl_instr env m b i lgoto in
  transl_block (entry_block v) f.entrypoint;
  Label.Map.iter (fun lbl i -> transl_block (Label.Map.find lbl lgoto) i) f.code *)

let transl_program (p : program) =
  let c = global_context () in
  let m = create_module c p.name in
  let f = define_function "TIG_main" (function_type (void_type c) [||]) m in
  set_gc (Some "shadow-stack") f;
  let env = {f; code = p.code; blocks = Label.Tbl.create 0; regs = Reg.Map.empty} in
  let b = builder c in
  position_at_end (entry_block f) b;
  transl_instr env m b p.entrypoint;
  m
