open Llvm

type ty =
  | Tvoid
  | Tstruct of ty list
  | Tarray of ty * int
  | Tnamed of string
  | Tpointer
  | Tint of int

type signature = ty list * ty

type array_kind =
  | Int | Pointer

type operation =
  | Pconstint of int64
  | Pconststring of string
  | Pnull
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pgep of ty
  | Pcmpint of Tabs.comparison
  | Pand
  | Pzext
  | Ialloca of ty * bool
  | Iapply of string
  | Iexternal of string * signature
  | Imakearray of array_kind
  | Imakerecord of int

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

type env =
  {
    c: llcontext;
    m: llmodule;
    b: llbuilder;
    f: llvalue;
    strings: (string, llvalue) Hashtbl.t;
    code: instruction Label.Map.t;
    blocks: llbasicblock Label.Tbl.t;
    regs: llvalue Reg.Map.t;
  }

let rec transl_ty env ty =
  match ty with
  | Tvoid ->
      void_type env.c
  | Tarray (ty, len) ->
      array_type (transl_ty env ty) len
  | Tstruct tys ->
      struct_type env.c (Array.of_list (List.map (transl_ty env) tys))
  | Tnamed name ->
      named_struct_type env.c name
  | Tpointer ->
      pointer_type env.c
  | Tint width ->
      integer_type env.c width

let gcroot env v =
  let lltype = function_type (void_type env.c) [|pointer_type env.c; pointer_type env.c|] in
  let f = declare_function "llvm.gcroot" lltype env.m in
  ignore (build_call lltype f [|v; const_null (pointer_type env.c)|] "" env.b)

let transl_operation env op args =
  match op, args with
  | Pconstint n, [] ->
      const_of_int64 (intptr_type env.c) n false
  | Pconststring s, [] ->
      begin match Hashtbl.find_opt env.strings s with
      | Some v -> v
      | None ->
          let v = build_global_stringptr s "" env.b in
          Hashtbl.replace env.strings s v;
          v
      end
  | Pnull, [] ->
      const_null (pointer_type env.c)
  | Paddint, [arg1; arg2] ->
      build_add arg1 arg2 "" env.b
  | Psubint, [arg1; arg2] ->
      build_sub arg1 arg2 "" env.b
  | Pmulint, [arg1; arg2] ->
      build_mul arg1 arg2 "" env.b
  | Pdivint, [arg1; arg2] ->
      build_sdiv arg1 arg2 "" env.b
  | Pcmpint c, [r1; r2] ->
      let c =
        match c with
        | Ceq -> Icmp.Eq | Cne -> Icmp.Ne | Cle -> Icmp.Sle
        | Clt -> Icmp.Slt | Cge -> Icmp.Sge | Cgt -> Icmp.Sgt
      in
      build_icmp c r1 r2 "" env.b
  | Pand, [r1; r2] ->
      build_and r1 r2 "" env.b
  | Pzext, [r] ->
      build_zext r (intptr_type env.c) "" env.b
  | Pgep ty, (r0 :: rl) ->
      build_gep (transl_ty env ty) r0 (Array.of_list rl) "" env.b
  | Ialloca (ty, root), [] ->
      let v = build_alloca (transl_ty env ty) "" env.b in
      if root then begin
        ignore (build_store (const_null (pointer_type env.c)) v env.b);
        gcroot env v;
      end;
      v
  | Iapply f, _ ->
      let _f =
        match lookup_function f env.m with
        | None -> assert false
        | Some f -> f
      in
      assert false
  (* [|build_call _ f arg "" b|] *)
  | Iexternal (f, (tys, ty)), args ->
      let lltype = function_type (transl_ty env ty) (Array.of_list (List.map (transl_ty env) tys)) in
      let f = declare_function f lltype env.m in
      build_call lltype f (Array.of_list args) "" env.b
  | Imakearray _ty, [size; init] ->
      let ty = function_type (pointer_type env.c) [|intptr_type env.c; intptr_type env.c|] in
      let f = declare_function "TIG_makearray" ty env.m in
      build_call ty f [|size; init|] "" env.b
  | Imakerecord n, [] ->
      let ty = function_type (pointer_type env.c) [|i32_type env.c|] in
      let f = declare_function "TIG_makerecord" ty env.m in
      build_call ty f [|const_int (i32_type env.c) n|] "" env.b
  | (Pconstint _ | Pconststring _ | Pnull | Paddint | Psubint | Pmulint | Pdivint | Pcmpint _ |
     Pand | Pzext | Pgep _ | Ialloca _ | Imakearray _ |
     Imakerecord _ ), _ ->
      assert false

let add_var env reg v =
  {env with regs = Reg.Map.add reg v env.regs}

let find_var env reg =
  Reg.Map.find reg env.regs

let find_code env lbl =
  Label.Map.find lbl env.code

let rec transl_instr env i =
  match i with
  | Iop (op, args, res, next) ->
      let args = List.map (find_var env) args in
      let vres = transl_operation env op args in
      transl_instr (add_var env res vres) next
  | Iload (ty, arg, res, next) ->
      let v = build_load (transl_ty env ty) (find_var env arg) "" env.b in
      transl_instr (add_var env res v) next
  | Istore (src, dst, next) ->
      ignore (build_store (find_var env src) (find_var env dst) env.b);
      transl_instr env next
  | Iifthenelse (cond, ifso, ifnot) ->
      let bbyay = transl_block env ifso in
      let bbnay = transl_block env ifnot in
      ignore (build_cond_br (find_var env cond) bbyay bbnay env.b)
  | Igoto lbl ->
      let bb = transl_block env lbl in
      ignore (build_br bb env.b)
  | Ireturn (Some arg) ->
      ignore (build_ret (find_var env arg) env.b)
  | Ireturn None ->
      ignore (build_ret_void env.b)
  | Iunreachable ->
      ignore (build_unreachable env.b)

and transl_block env lbl =
  match Label.Tbl.find_opt env.blocks lbl with
  | Some bb -> bb
  | None ->
      let bb = append_block env.c "" env.f in
      Label.Tbl.add env.blocks lbl bb;
      let b = builder env.c in
      position_at_end bb b;
      transl_instr {env with b} (find_code env lbl);
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
  let b = builder c in
  let env =
    { c; m; b; f; strings = Hashtbl.create 0;
      code = p.code; blocks = Label.Tbl.create 0;
      regs = Reg.Map.empty }
  in
  position_at_end (entry_block f) b;
  transl_instr env p.entrypoint;
  m
