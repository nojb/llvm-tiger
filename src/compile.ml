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
open Typedtree
open Lambda

type error =
  | Expected_record of Lexing.position * string * type_expr
  | Expected_array of Lexing.position * string * type_expr
  | Expected_record_type of Lexing.position * type_expr
  | Field_not_found of Lexing.position * type_expr * string
  | Redefined_function of Lexing.position * string
  | Redefined_variable of Lexing.position * string
  | Redefined_type of Lexing.position * string
  | Variable_not_found of Lexing.position * string
  | Function_not_found of Lexing.position * string
  | Type_not_found of Lexing.position * string
  | Variable_expected of Lexing.position * string
  | Function_expected of Lexing.position * string

exception Error of error

module Env : sig
  type t
  val empty: t
  val enter_scope: t -> t
  val loop: t -> t
  val no_loop: t -> t
  val looping: t -> bool
  type variable = ident * type_expr * bool
  type external_flag = External | Defined
  type signature = type_expr list * type_expr
  type function_ = ident * external_flag * signature
  val find_variable: Tabs.ident -> t -> variable
  val find_function: Tabs.ident -> t -> function_
  val find_type: Tabs.ident -> t -> type_expr
  val find_type_local: Tabs.ident -> t -> type_expr
  val add_variable: Tabs.ident -> ?immutable:bool -> type_expr -> t -> t * ident
  val add_function: Tabs.ident -> external_flag -> type_expr list -> type_expr -> t -> t
  val add_type: Tabs.ident -> type_expr -> t -> t
  val find_array_type: Tabs.ident -> t -> type_expr * type_expr
  val find_record_type: Tabs.ident -> t -> type_expr * (string * type_expr) list
  val find_record_field: type_expr -> Tabs.ident -> t -> int * type_expr
end = struct

  module StringMap = Map.Make (String)

  type variable = ident * type_expr * bool

  type external_flag = External | Defined

  type signature = type_expr list * type_expr

  type function_ = ident * external_flag * signature

  type value =
    | Variable of variable
    | Function of function_

  type t =
    {
      values: value StringMap.t list;
      types: type_expr StringMap.t list;
      looping: bool;
      level: int;
    }

  let looping env = env.looping

  let find_variable id env =
    let rec aux = function
      | [] ->
          raise (Error (Variable_not_found (id.pid_pos, id.pid_text)))
      | env :: rest ->
          begin match StringMap.find id.pid_text env with
            | Variable v ->
                v
            | Function _ ->
                raise (Error (Variable_expected (id.pid_pos, id.pid_text)))
            | exception Not_found ->
                aux rest
          end
    in
    aux env.values

  let find_function id env =
    let rec aux = function
      | [] ->
          raise (Error (Function_not_found (id.pid_pos, id.pid_text)))
      | env :: rest ->
          begin match StringMap.find id.pid_text env with
            | Variable _ ->
                raise (Error (Function_expected (id.pid_pos, id.pid_text)))
            | Function f ->
                f
            | exception Not_found ->
                aux rest
          end
    in
    aux env.values

  let find_type id env =
    let rec aux = function
      | [] ->
          raise (Error (Type_not_found (id.pid_pos, id.pid_text)))
      | env :: rest ->
          begin match StringMap.find id.pid_text env with
            | ty ->
                ty
            | exception Not_found ->
                aux rest
          end
    in
    aux env.types

  let find_type_local id env =
    match env.types with
    | [] ->
        raise Not_found
    | env :: _ ->
        StringMap.find id.pid_text env

  let add_variable {pid_text; pid_pos} ?(immutable = false) t env =
    let id = new_ident pid_text in
    let v = Variable (id, t, immutable) in
    match env.values with
    | env0 :: _ when StringMap.mem pid_text env0 ->
        raise (Error (Redefined_variable (pid_pos, pid_text)))
    | env0 :: rest ->
        {env with values = StringMap.add pid_text v env0 :: rest}, id
    | [] ->
        assert false

  let add_function {pid_text; pid_pos} eflag argty rety env =
    let id = new_ident pid_text in
    let f = Function (id, eflag, (argty, rety)) in
    match env.values with
    | env0 :: _ when StringMap.mem pid_text env0 ->
        raise (Error (Redefined_function (pid_pos, pid_text)))
    | env0 :: rest ->
        {env with values = StringMap.add pid_text f env0 :: rest}
    | [] ->
        assert false

  let add_type {pid_text; pid_pos} t env =
    match env.types with
    | env0 :: _ when StringMap.mem pid_text env0 ->
        raise (Error (Redefined_type (pid_pos, pid_text)))
    | env0 :: rest ->
        {env with types = StringMap.add pid_text t env0 :: rest}
    | [] ->
        assert false

  let empty =
    {
      values = [];
      types = [];
      looping = false;
      level = 0;
    }

  let loop env = {env with looping = true}

  let no_loop env = {env with looping = false}

  let enter_scope env =
    {
      env with values = StringMap.empty :: env.values;
               types = StringMap.empty :: env.types;
               level = env.level + 1;
    }

  let find_array_type ({pid_text; pid_pos} as id) env =
    match find_type id env with
    | {tdesc = ARRAY t'} as t ->
        t, t'
    | t ->
        raise (Error (Expected_array (pid_pos, pid_text, t)))

  let find_record_type ({pid_text; pid_pos} as id) env =
    match find_type id env with
    | {tdesc = RECORD xts} as t ->
        t, xts
    | t ->
        raise (Error (Expected_record (pid_pos, pid_text, t)))

  let find_record_field t ({pid_text; pid_pos} as id) env =
    let xts =
      match t.tdesc with
      | RECORD xts -> xts
      | _ -> raise (Error (Expected_record_type (pid_pos, t)))
    in
    let rec loop i = function
      | [] ->
          raise (Error (Field_not_found (pid_pos, t, pid_text)))
      | (x, t) :: xs when x = pid_text ->
          i, t
      | _ :: xs ->
          loop (i+1) xs
    in
    loop 0 xts
end

let declare_type env (x, t) =
  let get_type y =
    try
      Env.find_type y env
    with Not_found ->
      {tid = next_tid (); tname = y.pid_text; tdesc = REF (ref None)}
  in
  let aux = function
    | Tname y ->
        get_type y
    | Tarray y ->
        {tid = next_tid (); tname = x.pid_text; tdesc = ARRAY (get_type y)}
    | Trecord xs ->
        let xts = List.map (fun (x, t) -> x.pid_text, get_type t) xs in
        {tid = next_tid (); tname = x.pid_text; tdesc = RECORD xts}
  in
  match Env.find_type_local x env with
  | {tdesc = REF ({contents = None} as r)} ->
      r := Some (aux t);
      env
  | {tdesc = REF {contents = Some _}} ->
      failwith "redefined"
  | t1 ->
      failwith "redefined"
  | exception Not_found ->
      Env.add_type x (aux t) env

let check_unique_type_names xts =
  let rec bind = function
    | [] -> ()
    | (x, _) :: xts ->
        let matches = List.filter (fun (x', _) -> x.pid_text = x'.pid_text) xts in
        if List.length matches > 0 then
          let (x', _) = List.hd matches in
          error x'.pid_pos
            "type name '%s' can only be defined once in each type declaration"
            x.pid_text
        else
          bind xts
  in
  bind xts

let check_type env (x, _) =
  let visited = ref [] in
  let rec shorten t t1 =
    if List.memq t1.tid !visited then failwith "does not go through structured type"
    else visited := t1.tid :: !visited;
    match t1.tdesc with
    | REF {contents = None} ->
        failwith "undefined type"
    | REF {contents = Some t1} ->
        shorten t t1
    | _ ->
        if t.tid != t1.tid then begin
          t.tid <- t1.tid;
          t.tdesc <- t1.tdesc
        end
  in
  let t = Env.find_type x env in
  shorten t t

let let_type env tys =
  check_unique_type_names tys;
  let env = List.fold_left declare_type env tys in
  List.iter (check_type env) tys;
  env

(** ----------------------------------------- *)

let rec structured_type env t =
  match t.tdesc with
  | STRING
  | ARRAY _
  | RECORD _ -> true
  | _ -> false

(* These utility functions are used in the processing of function definitions *)

let check_unique_fundef_names fundefs =
  let rec bind = function
    | [] -> ()
    | fundef :: fundefs ->
        let matches =
          List.filter (fun fundef' -> fundef.fn_name.pid_text = fundef'.fn_name.pid_text)
          fundefs in
        if List.length matches > 0 then
          let fundef' = List.hd matches in
          error fundef'.fn_name.pid_pos
            "function name '%s' can only be defined once in each type declaration"
            fundef'.fn_name.pid_text
        else
          bind fundefs
  in bind fundefs

let tr_return_type env fn =
  match fn.fn_rtyp with
  | None ->
      void_ty
  | Some t ->
      Env.find_type t env

let tr_function_header env fn =
  let rtyp = tr_return_type env fn in
  let argst = List.map (fun (_, t) -> Env.find_type t env) fn.fn_args in
  Env.add_function fn.fn_name Env.Defined argst rtyp env

let rec tr_function_body env fundef =
  let (_, _, (ts, t)) = Env.find_function fundef.fn_name env in
  let env, args =
    List.fold_right2 (fun (x, _) t (env, args) ->
        let env, x = Env.add_variable x t env in
        env, x :: args
      ) fundef.fn_args ts (env, [])
  in
  let body = typ_exp (Env.no_loop env) fundef.fn_body t in
  let id = new_ident fundef.fn_name.pid_text in
  id, args, body

and let_funs env fundefs e =
  check_unique_fundef_names fundefs;
  let env = List.fold_left tr_function_header env fundefs in
  let fundefs = List.map (tr_function_body env) fundefs in
  let e, t = exp (Env.enter_scope env) e in
  Lletrec (fundefs, e), t

and array_var env v =
  let v', t' = var env v in
  match t'.tdesc with
  | ARRAY t' ->
      v', t'
  | _ ->
      error v.pvar_pos "expected variable of array type, but type is '%s'"
        (name_of_type t')

and record_var env v =
  let v', t' = var env v in
  match t'.tdesc with
  | RECORD _ ->
      v', t'
  | _ ->
      error v.pvar_pos "expected variable of record type, but type is '%s'"
        (name_of_type t')

and typ_exp env e t' =
  let e', t = exp env e in
  if type_equal t' t then
    e'
  else
    error e.pexp_pos
      "type mismatch: expected type '%s', instead found '%s'"
      (name_of_type t') (name_of_type t)

and int_exp env e =
  typ_exp env e int_ty

and void_exp env e =
  typ_exp env e void_ty

(* Main typechecking/compiling functions *)

and var env v : lambda * type_expr =
  match v.pvar_desc with
  | Vsimple x ->
      let id, t, _ = Env.find_variable x env in
      Lvar id, t
  | Vsubscript (v, x) ->
      let v, t = array_var env v in
      let x = int_exp env x in
      Lprim (Parrayget, [v; x]), t
  | Vfield (v, id) ->
      let v, t = record_var env v in
      let i, tx = Env.find_record_field t id env in
      Lprim (Pgetfield i, [v]), tx

and exp env e : lambda * type_expr =
  match e.pexp_desc with
  | Eunit ->
      Lconst (Const_int 0), void_ty
  | Eint n ->
      Lconst (Const_int n), int_ty
  (* | Estring (_, s) -> *)
  (*     nxt (VAL (build_global_stringptr s "" g_builder)) STRING *)
  | Enil ->
      error e.pexp_pos
        "'nil' should be used in a context where \
        its type can be determined"
  | Evar v ->
      var env v
  | Ebinop (x, Op_add, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      Lprim (Paddint, [x; y]), int_ty
  | Ebinop (x, Op_sub, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      Lprim (Psubint, [x; y]), int_ty
  | Ebinop (x, Op_mul, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      Lprim (Pmulint, [x; y]), int_ty
  (* | Ebinop (_, x, Op_div, y) -> *)
  (*     int_exp env x (fun x -> *)
  (*     int_exp env y (fun y -> *)
  (*     nxt (binop build_sdiv x y) INT)) *)
  (* | Ebinop (_, x, Op_cmp Ceq, Enil _) *)
  (* | Ebinop (_, Enil _, Op_cmp Ceq, x) -> *)
  (*     let v = exp env x in *)
  (*     begin match base_type env tx with *)
  (*     | RECORD _ -> *)
  (*         let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in *)
  (*         let c = binop (build_icmp Icmp.Eq) v *)
  (*             (const_null (int_t Sys.word_size)) in *)
  (*         let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in *)
  (*         nxt c INT *)
  (*     | _ -> *)
  (*         error (exp_p x) "expected expression of record type, found %s" *)
  (*           (describe_type tx) *)
  (*     end *)
  (* | Ebinop (_, x, Op_cmp Cne, Enil _) *)
  (* | Ebinop (_, Enil _, Op_cmp Cne, x) -> *)
  (*     exp env x (fun v tx -> *)
  (*       match base_type env tx with *)
  (*       | RECORD _ -> *)
  (*           let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in *)
  (*           let c = binop (build_icmp Icmp.Ne) v *)
  (*             (const_null (int_t Sys.word_size)) in *)
  (*           let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in *)
  (*           nxt c INT *)
  (*       | _ -> *)
  (*           error (exp_p x) "expected expression of record type, found %s" *)
  (*             (describe_type tx)) *)
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
  (* | Eassign (v, {pexp_desc = Enil}) -> *)
  (*     let v = var env v in *)
  (*     begin match v.tvar_type.tdesc with *)
  (*       | RECORD _ -> *)
  (*           mkexp (Tassign (v, mkexp Tnil v.tvar_type)) void_ty *)
  (*       | _ -> *)
  (*           error e.pexp_pos "trying to assign 'nil' to a variable of non-record type" *)
  (*     end *)
  (* | Eassign (v, e) -> *)
  (*     let v = var env v in *)
  (*     let e = typ_exp env e v.tvar_type in *)
  (*     mkexp (Tassign (v, e)) void_ty *)
  | Eassign ({pvar_desc = Vsimple x}, e) ->
      let x, t, _ = Env.find_variable x env in
      let e = typ_exp env e t in
      Lassign (x, e), void_ty
  | Ecall (id, es) ->
      let id, eflag, (ts, t) = Env.find_function id env in
      if List.length es <> List.length ts then
        error e.pexp_pos "bad arity: is %d, should be %d"
          (List.length es) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            Lapply (id, List.rev ys), t
        | {pexp_desc = Enil; pexp_pos = p} :: xs, t :: ts ->
            begin match t.tdesc with
            | RECORD _ ->
                bind (Lconst (Const_int 0) :: ys) (xs, ts)
            | _ ->
                error p "expected record type, found '%s'" (name_of_type t)
            end
        | x :: xs, t :: ts ->
            let x = typ_exp env x t in
            bind (x :: ys) (xs, ts)
        | _ ->
            assert false
      in
      bind [] (es, ts)
  | Eseq (x1, x2) ->
      let e1, _ = exp env x1 in
      let e2, t2 = exp env x2 in
      Lsequence (e1, e2), t2
  (* | Emakearray (id, y, {pexp_desc = Enil}) -> *)
  (*     let t, t' = Env.find_array_type id env in *)
  (*     begin match t'.tdesc with *)
  (*     | RECORD _ -> *)
  (*         let y = int_exp env y in *)
  (*         Lprim (Pmakearray, [mkexp (Tmakearray (y, mkexp Tnil t')) t *)
  (*     | _ -> *)
  (*         error e.pexp_pos "array base type must be record type" *)
  (*     end *)
  | Emakearray (x, y, z) ->
      let t, t' = Env.find_array_type x env in
      let y = int_exp env y in
      let z = typ_exp env z t' in
      Lprim (Pmakearray, [y; z]), t
  | Emakerecord (x, xts) ->
      let t, ts = Env.find_record_type x env in
      let rec bind vs = function
        | [], [] ->
            Lprim (Pmakeblock 0, List.rev vs), t
        | (x, {pexp_desc = Enil}) :: xts, (x', t) :: ts ->
            if x.pid_text = x' then
              bind (Lconst (Const_int 0) :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.pid_text = x') ts then
                error x.pid_pos "field '%s' is in the wrong other" x.pid_text
              else
                error x.pid_pos "field '%s' is unknown" x.pid_text
        | (x, e) :: xts, (x', t) :: ts ->
            if x.pid_text = x' then
              let e = typ_exp env e t in
              bind (e :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.pid_text = x') ts then
                error x.pid_pos "field '%s' is in the wrong other" x.pid_text
              else
                error x.pid_pos "unknown field '%s'" x.pid_text
        | [], _ ->
            error e.pexp_pos "some fields missing from initialisation"
        | _, [] ->
            error e.pexp_pos "all fields have already been initialised"
      in
      bind [] (xts, ts)
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  (* | Eif (x, y, {pexp_desc = Eunit}) -> *)
  (*     let x = int_exp env x in *)
  (*     let y = void_exp env y in *)
  (*     mkexp (Tif (x, y, mkexp Tunit void_ty)) void_ty *)
  | Eif (x, y, z) ->
      let x = int_exp env x in
      let y, t = exp env y in
      let z = typ_exp env z t in
      Lifthenelse (x, y, z), t
  | Ewhile (x, y) ->
      let x = int_exp env x in
      let y = void_exp (Env.loop env) y in
      Lstaticcatch (Lwhile (x, y)), void_ty
  | Efor (i, x, y, z) ->
      let x = int_exp env x in
      let y = int_exp env y in
      let env = Env.enter_scope env in
      let env, i = Env.add_variable i ~immutable:true int_ty (Env.loop env) in
      let z = void_exp env z in
      Lstaticcatch (Lfor (i, x, y, z)), void_ty
  | Ebreak when Env.looping env ->
      Lstaticfail, any_ty
  | Ebreak ->
      error e.pexp_pos "illegal use of 'break'"
  | Elet (Dvar (x, None, y), z) ->
      let y, t = exp env y in
      let env, x = Env.add_variable x t env in
      let env = Env.enter_scope env in
      let z, t = exp env z in
      Llet (x, y, z), t
  (* | Elet (Dvar (x, Some t, {pexp_desc = Enil}), z) -> *)
  (*     let t = Env.find_type t env in *)
  (*     begin match t.tdesc with *)
  (*     | RECORD _ -> *)
  (*         let env, x = Env.add_variable x t env in *)
  (*         let env = Env.enter_scope env in *)
  (*         let z = exp env z in *)
  (*         mkexp (Tlet (x, mkexp Tnil t, z)) z.texp_type *)
  (*     | _ -> *)
  (*         error e.pexp_pos "expected record type, found '%s'" (name_of_type t) *)
  (*     end *)
  | Elet (Dvar (x, Some t, y), z) ->
      let ty = Env.find_type t env in
      let y = typ_exp env y ty in
      let env, x = Env.add_variable x ty env in
      let z, t = exp (Env.enter_scope env) z in
      Llet (x, y, z), t
  | Elet (Dtypes tys, e) ->
      let env = let_type env tys in
      exp (Env.enter_scope env) e
  | Elet (Dfuns funs, e) ->
      let_funs env funs e

let base_env =
  Env.add_type (makeghost "int") int_ty
    (Env.add_type (makeghost "string") string_ty Env.empty)

(*   let stdlib = *)
(*     [ "print" , [STRING], VOID; *)
(*       "printi", [INT], VOID; *)
(*       "flush", [], VOID; *)
(*       "getchar", [], STRING; *)
(*       "ord", [STRING], INT; *)
(*       "chr", [INT], STRING; *)
(*       "size", [STRING], INT; *)
(*       "substring", [STRING; INT; INT], STRING; *)
(*       "concat", [STRING; STRING], STRING; *)
(*       "not", [INT], INT; *)
(*       "exit", [INT], VOID; *)
(*       "gc_collect", [], VOID ] in *)
(*   let decl_fun env (x, ts, t) = *)
(*     let fname = "__tiger__" ^ x in *)
(*     let fllval = lazy (declare_function fname *)
(*       (function_type (llvm_return_type env t) *)
(*         (Array.of_list (List.map (transl_typ env) ts))) *)
(*       g_module) in *)
(*     { env with venv = M.add x *)
(*       (Function {fname = fname; f_user = false; fsign = (ts, t); f_llvalue = *)
(*         fllval }) env.venv } in *)
(*   List.fold_left decl_fun env stdlib *)

let program e =
  exp base_env e
  (* let env = { empty_env with tenv = base_tenv } in *)
  (* let env = base_venv env in *)
  (* let main_fun = define_function "__tiger__main" *)
  (*   (function_type void_t [| |]) g_module in *)
  (* set_gc (Some "shadow-stack") main_fun; *)
  (* position_at_end (entry_block main_fun) g_builder; *)
  (* let startbb = new_block () in *)
  (* position_at_end startbb g_builder; *)
  (* (\* exp env e (fun _ _ -> ignore (build_ret (const_int0 32 0) g_builder)); *\) *)
  (* exp env e (fun _ _ -> ignore (build_ret_void g_builder)); *)
  (* position_at_end (entry_block main_fun) g_builder; *)
  (* ignore (build_br startbb g_builder); *)
  (* g_module *)
