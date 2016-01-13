(* The MIT License (MIT)

   Copyright (c) 2013-2016 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

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
  }

type fun_info =
  {
    fname : string;
    fsign : type_spec list * type_spec;
    f_user : bool;
  }

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type env =
  {
    venv : value_desc M.t;
    tenv : type_spec M.t;
    in_loop : bool;
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
    in_loop = false;
  }

let find_var id env =
  try
    match M.find id.s env.venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with
    Not_found ->
      error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?immutable:(immut=false) t env =
  let vi = {vtype = t; vimm = immut} in
  {env with venv = M.add x.s (Variable vi) env.venv}

let mem_var x env =
  try
    match M.find x env.venv with
    | Variable _ -> true
    | Function _ -> false
  with Not_found ->
    false

let add_fun x uid atyps rtyp env =
  let fi =
    {
      fname = uid;
      fsign = atyps, rtyp;
      f_user = true;
    }
  in
  {env with venv = M.add x.s (Function fi) env.venv}

let mem_user_fun x env =
  try
    match M.find x env.venv with
    | Function fi -> fi.f_user
    | Variable _ -> false
  with Not_found ->
    false

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
  {env with tenv = M.add x.s t env.tenv}

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

(* let rec structured_type env t = *)
(*   match t with *)
(*   | NAME y -> structured_type env (M.find y env.tenv) *)
(*   | STRING *)
(*   | ARRAY _ *)
(*   | RECORD _ -> true *)
(*   | _ -> false *)

(* These utility functions are used in the processing of function definitions *)

let check_unique_fundef_names fundefs =
  let rec bind = function
    | [] -> ()
    | fundef :: fundefs ->
        let matches =
          List.filter (fun fundef' -> fundef.fn_name.s = fundef'.fn_name.s)
            fundefs
        in
        if List.length matches > 0 then
          let fundef' = List.hd matches in
          error fundef'.fn_name.p
            "function name '%s' can only be defined once in each type declaration"
            fundef'.fn_name.s
        else
          bind fundefs
  in
  bind fundefs

let tr_return_type env fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t env

let tr_function_header env fn =
  let rtyp = tr_return_type env fn in
  let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in
  let uid = gentmp fn.fn_name.s in
  add_fun fn.fn_name uid argst rtyp env

let rec tr_function_body env fundef =
  let fi = find_fun fundef.fn_name env in
  let ts, t = fi.fsign in
  (* Process arguments *)
  let env =
    List.fold_left2 (fun env (x, _) t -> add_var x t env) env fundef.fn_args ts
  in
  (* Process the body *)
  let body = typ_exp {env with in_loop = false} fundef.fn_body t in
  let args = List.map (fun (id, _) -> id.s) fundef.fn_args in
  fundef.fn_name.s, args, body

and let_funs env fundefs e =
  check_unique_fundef_names fundefs;
  let env = List.fold_left tr_function_header env fundefs in
  let funs = List.map (tr_function_body env) fundefs in
  let t, e = exp env e in
  t, Lletrec (funs, e)

and array_var env v =
  let t, v' = var env v in
  match base_type env t with
  | ARRAY (_, t') ->
      t', v'
  | _ ->
      error v.vpos "expected variable of array type, but type is '%s'"
        (describe_type t)

and record_var env v =
  let t, v' = var env v in
  match base_type env t with
  | RECORD _ ->
      t, v'
  | _ ->
      error v.vpos "expected variable of record type, but type is '%s'"
        (describe_type t)

and typ_exp env e t' =
  let t, e' = exp env e in
  if type_equal env t t' then
    e'
  else
    error e.epos
      "type mismatch: expected type '%s', instead found '%s'"
      (string_of_type t') (string_of_type t)

and int_exp env e =
  typ_exp env e INT

and void_exp env e =
  typ_exp env e VOID

(* Main typechecking/compiling functions *)

and var env v =
  match v.vdesc with
  | Vsimple x ->
      let vi = find_var x env in
      vi.vtype, Lvar x.s
  | Vsubscript (v, e) ->
      let t', v = array_var env v in
      let e = int_exp env e in
      t', Lprim (Parrayrefs Paddrarray (* FIXME *), [v; e])
  | Vfield (v, x) ->
      let t', v = record_var env v in
      let i, tx = find_record_field env t' x in
      tx, Lprim (Pfield i, [v])

and exp env e =
  match e.edesc with
  | Eunit ->
      VOID, Lconst 0n
  | Eint n ->
      INT, Lconst (Nativeint.of_int n)
  | Estring s ->
      failwith "not implemented"
      (* nxt (VAL (build_global_stringptr s "" g_builder)) STRING *)
  | Enil ->
      error e.epos
        "'nil' should be used in a context where \
        its type can be determined"
  | Evar v ->
      var env v
  | Ebinop (e1, Op_add, e2) ->
      let e1 = int_exp env e1 in
      let e2 = int_exp env e2 in
      INT, Lprim (Paddint, [e1; e2])
  | Ebinop (e1, Op_sub, e2) ->
      let e1 = int_exp env e1 in
      let e2 = int_exp env e2 in
      INT, Lprim (Psubint, [e1; e2])
  | Ebinop (e1, Op_mul, e2) ->
      let e1 = int_exp env e1 in
      let e2 = int_exp env e2 in
      INT, Lprim (Pmulint, [e1; e2])
  (* | Ebinop (_, x, Op_div, y) -> *)
  (*     int_exp env x (fun x -> *)
  (*     int_exp env y (fun y -> *)
  (*     nxt (binop build_sdiv x y) INT)) *)
  | Ebinop (x, Op_cmp Ceq, {edesc = Enil})
  | Ebinop ({edesc = Enil}, Op_cmp Ceq, x) ->
      let tx, v = exp env x in
      begin match base_type env tx with
        | RECORD _ ->
            INT, Lprim (Pintcomp Ceq, [Lconst 0n; v])
        | _ ->
            error x.epos "expected expression of record type, found %s"
              (describe_type tx)
      end
  | Ebinop (x, Op_cmp Cne, {edesc = Enil})
  | Ebinop ({edesc = Enil}, Op_cmp Cne, x) ->
      let tx, v = exp env x in
      begin match base_type env tx with
        | RECORD _ ->
            INT, Lprim (Pintcomp Cneq, [Lconst 0n; v])
        | _ ->
            error x.epos "expected expression of record type, found %s"
              (describe_type tx)
      end
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
  | Eassign ({vdesc = Vsimple x}, {edesc = Enil}) ->
      let vi = find_var x env in
      begin match base_type env vi.vtype with
      | RECORD _ ->
          VOID, Lassign (x.s, Lconst 0n)
      | _ ->
          error e.epos "trying to assign 'nil' to a variable of non-record type"
      end
  | Eassign ({vdesc = Vsimple x}, e) ->
      let vi = find_var x env in
      if vi.vimm then error e.epos "variable '%s' should not be assigned to" x.s;
      let e = typ_exp env e vi.vtype in
      VOID, Lassign (x.s, e)
  | Eassign ({vdesc = Vsubscript (v, e)}, {edesc = Enil}) ->
      let t', v = array_var env v in
      begin match base_type env t' with
      | RECORD _ ->
          let e = int_exp env e in
          VOID, Lprim (Parraysets Paddrarray, [v; e; Lconst 0n])
      | _ ->
          error e.epos "trying to assign 'nil' to a field of non-record type"
      end
  | Eassign ({vdesc = Vsubscript (v, e1)}, e2) ->
      let t', v = array_var env v in
      let e1 = int_exp env e1 in
      let e2 = typ_exp env e2 t' in
      VOID, Lprim (Parraysets Paddrarray, [v; e1; e2])
  | Eassign ({vdesc = Vfield (v, x)}, {edesc = Enil}) ->
      let t', v = record_var env v in
      let i, tx = find_record_field env t' x in
      begin match base_type env tx with
      | RECORD _ ->
          VOID, Lprim (Psetfield i, [v; Lconst 0n])
      | _ ->
          error e.epos "trying to assign 'nil' to a field of non-record type"
      end
  | Eassign ({vdesc = Vfield (v, x)}, e) ->
      let t', v = record_var env v in
      let i, tx = find_record_field env t' x in
      let e = typ_exp env e tx in
      VOID, Lprim (Psetfield i, [v; e])
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
  | Eseq (e1, e2) ->
      let _, e1 = exp env e1 in
      let t, e2 = exp env e2 in
      t, Lsequence (e1, e2)
  | Emakearray (x, y, {edesc = Enil}) ->
      let t, t' = find_array_type x env in
      begin match base_type env t' with
      | RECORD _ ->
          let y = int_exp env y in
          t, Lprim (Pmakearray Paddrarray, [y; Lconst 0n])
      | _ ->
          error e.epos "array base type must be record type"
      end
  | Emakearray (x, y, z) ->
      let t, t' = find_array_type x env in
      let y = int_exp env y in
      let z = typ_exp env z t' in
      t, Lprim (Pmakearray Paddrarray (* FIXME *), [y; z])
  | Emakerecord (x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            t, Lprim (Pmakeblock 0 (* FIXME *), List.rev vs)
        | (x, {edesc = Enil}) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (Lconst 0n :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "field '%s' is unknown" x.s
        | (x, e) :: xts, (x', t) :: ts ->
            if x.s = x' then
              let e = typ_exp env e t in
              bind (e :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "unknown field '%s'" x.s
        | [], _ ->
            error e.epos "some fields missing from initialisation"
        | _, [] ->
            error e.epos "all fields have already been initialised"
      in bind [] (xts, ts)
  | Eif (e1, e2, e3) ->
      let e1 = int_exp env e1 in
      let t2, e2 = exp env e2 in
      let e3 = typ_exp env e3 t2 in
      t2, Lifthenelse (e1, e2, e3)
  | Ewhile (e1, e2) ->
      let e1 = int_exp env e1 in
      let e2 = void_exp {env with in_loop = true} e2 in
      VOID, Lwhile (e1, e2)
  | Efor (i, e1, e2, e3) ->
      let e1 = int_exp env e1 in
      let e2 = int_exp env e2 in
      let e3 = void_exp (add_var i ~immutable:true INT {env with in_loop = true}) e3 in
      VOID, Lfor (i.s, e1, e2, e3)
  | Ebreak ->
      if env.in_loop then
        VOID, Lbreak (* TODO FIX TYPE *)
      else
        error e.epos "illegal use of 'break'"
  | Elet (Dvar (x, None, e1), e2) ->
      let t1, e1 = exp env e1 in
      let env = add_var x t1 (* a *) env in
      let t2, e2 = exp env e2 in
      t2, Llet (x.s, e1, e2)
  | Elet (Dvar (x, Some t, {edesc = Enil}), e2) ->
      let t = find_type t env in
      begin match base_type env t with
      | RECORD _ ->
          let env = add_var x t (* a *) env in
          let t2, e2 = exp env e2 in
          t2, Llet (x.s, Lconst 0n, e2)
      | _ ->
          error e.epos "expected record type, found '%s'" (describe_type t)
      end
  | Elet (Dvar (x, Some t, e1), e2) ->
      let ty = find_type t env in
      let e1 = typ_exp env e1 ty in
      let env = add_var x ty (* a *) env in
      let t2, e2 = exp env e2 in
      t2, Llet (x.s, e1, e2)
  | Elet (Dtypes tys, e) ->
      let env = let_type env tys in
      exp env e
  | Elet (Dfuns funs, e) ->
      let_funs env funs e

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
  let _, e = exp {tenv; venv; in_loop = false} e in (* (fun _ _ -> ignore (build_ret_void g_builder));*)
  (* position_at_end (entry_block main_fun) g_builder; *)
  (* ignore (build_br startbb g_builder); *)
  (* g_module *)
  e
