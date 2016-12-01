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
open Irep

let last_id = ref (-1)
let fresh () = incr last_id; !last_id

let gentmp s =
  let id = fresh () in
  Printf.sprintf "__tiger_%s_%i" s id

type type_desc =
  | VOID
  | INT
  | STRING
  | ARRAY of string * type_desc
  | RECORD of string * (string * type_desc) list
  | REF of type_desc option ref

let void_ty = VOID
let int_ty = INT
let string_ty = STRING
let any_ty () = REF (ref None)

type var_info =
  {
    id: int;
    vtype: type_desc;
    vimm: bool;
  }

type fun_info =
  {
    fname: string;
    fsign: type_desc list * type_desc;
    f_user: bool;
  }

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type env =
  {
    venv: value_desc M.t;
    tenv: type_desc M.t;
    in_loop: bool;
  }

let rec base_type = function
  | REF {contents = Some t} -> base_type t
  | t -> t

let type_equal t1 t2 =
  base_type t1 == base_type t2

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
  with Not_found ->
    error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?(immutable = false) t env =
  let vi = {id = fresh (); vtype = t; vimm = immutable} in
  {env with venv = M.add x.s (Variable vi) env.venv}

let mem_var x env =
  match M.find x env.venv with
  | Variable _ -> true
  | Function _ -> false
  | exception Not_found -> false

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
  match M.find x env.venv with
  | Function fi -> fi.f_user
  | Variable _ -> false
  | exception Not_found -> false

let find_fun x env =
  try
    match M.find x.s env.venv with
    | Variable _ -> raise Not_found
    | Function fi -> fi
  with Not_found ->
    error x.p "unbound function '%s'" x.s

let find_type x env =
  try
    M.find x.s env.tenv
  with Not_found ->
    error x.p "unbound type '%s'" x.s

let add_type x t env =
  {env with tenv = M.add x.s t env.tenv}

let rec print_type = function
  | INT -> "int"
  | VOID -> "void"
  | STRING -> "string"
  | RECORD (s, _) | ARRAY (s, _) -> s
  | REF {contents = Some t} -> print_type t
  | REF {contents = None} -> "<a type>"

let find_array_type x env =
  match base_type (find_type x env) with
  | ARRAY (_, t') as t -> t, t'
  | t -> error x.p "expected '%s' to be of array type, but is '%s'" x.s (print_type t)

let find_record_type env x =
  match base_type (find_type x env) with
  | RECORD (_, xts) as t -> t, xts
  | t -> error x.p "expected '%s' to be of record type, but is '%s'" x.s (print_type t)

let find_record_field env t (x : pos_string) =
  let xts = match base_type t with RECORD (_, xts) -> xts | _ -> assert false in
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" (print_type t) x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in
  loop 0 xts

let unify_ty pos ty1 ty2 =
  match ty1, ty2 with
  | REF ({contents = None} as t), _ -> t := Some ty2
  | _, REF ({contents = None} as t) -> t := Some ty1
  | _ ->
      if not (type_equal ty1 ty2) then
        error pos "type mismatch: expected type '%s', instead found '%s'" (print_type ty1) (print_type ty2)

let declare_types env xts =
  let env =
    List.fold_left (fun env (x, t) -> add_type x (any_ty ()) env) env xts
  in
  List.iter (fun (x, t) ->
      let tx = find_type x env in
      let pos = x.p in
      match t with
      | Tname y ->
          let ty = find_type y env in
          unify_ty pos tx ty
      | Tarray y ->
          let name = x.s in
          unify_ty pos tx (ARRAY (name, find_type y env))
      | Trecord xs ->
          let name = x.s in
          unify_ty pos tx (RECORD (name, List.map (fun (x, t) -> x.s, find_type t env) xs))
    ) xts;
  env

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
  in
  bind xts

let let_type env tys =
  check_unique_type_names tys;
  declare_types env tys

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
  | None -> void_ty
  | Some t -> find_type t env

let tr_function_header env fn =
  let rtyp = tr_return_type env fn in
  let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in
  let uid = gentmp fn.fn_name.s in
  add_fun fn.fn_name uid argst rtyp env

let rec tr_function_body env fundef =
  let fi = find_fun fundef.fn_name env in
  let ts, t = fi.fsign in
  let env, args =
    List.fold_left2 (fun (env, args) (x, _) t ->
        let env = add_var x t env in
        env, x.s :: args
      ) (env, []) fundef.fn_args ts
  in
  let body = exp {env with in_loop = false} fundef.fn_body t in
  fi.fname, {name = fi.fname; args = List.rev args; body}

and let_funs env fundefs e ty =
  check_unique_fundef_names fundefs;
  let env = List.fold_left tr_function_header env fundefs in
  let v = exp env e ty in
  Lletrec (List.map (tr_function_body env) fundefs, v)

and array_var env v =
  let pos = v.vpos in
  let r = ref None in
  let v = var env v (REF r) in
  match r.contents with
  | Some (ARRAY (_, t')) -> t', v
  | Some t -> error pos "expected variable of array type, but type is '%s'" (print_type t)
  | None -> assert false

and record_var env v =
  let pos = v.vpos in
  let r = ref None in
  let v = var env v (REF r) in
  match r.contents with
  | Some (RECORD _ as t) -> t, v
  | Some t -> error pos "expected variable of record type, but type is '%s'" (print_type t)
  | None -> assert false

and var env v ty =
  let pos = v.vpos in
  match v.vdesc with
  | Vsimple x ->
      let vi = find_var x env in
      unify_ty pos vi.vtype ty;
      Lvar x.s
  | Vsubscript (v, x) ->
      let t', v = array_var env v in
      let x = exp env x int_ty in
      unify_ty pos t' ty;
      Lprim (Parrayref, [v; x])
  | Vfield (v, x) ->
      let t', v = record_var env v in
      let i, tx = find_record_field env t' x in
      unify_ty pos tx ty;
      Lprim (Pgetfield i, [v])

and assign env v e =
  match v.vdesc with
  | Vsimple x ->
      let vi = find_var x env in
      let e = exp env e vi.vtype in
      Lassign (x.s, e)
  | Vsubscript (v, x) ->
      let t', v = array_var env v in
      let x = exp env x int_ty in
      let e = exp env e t' in
      Lprim (Parrayset, [v; x; e])
  | Vfield (v, x) ->
      let t', v = record_var env v in
      let i, tx = find_record_field env t' x in
      let e = exp env e tx in
      Lprim (Psetfield i, [v; e])

and exp env e ty =
  let unify_ty = unify_ty e.epos in
  match e.edesc with
  | Eunit ->
      unify_ty void_ty ty;
      Lconst 0L
  | Eint n ->
      unify_ty int_ty ty;
      Lconst (Int64.of_int32 n)
  | Estring s ->
      error e.epos "String literals not implemented"
  | Enil ->
      begin match base_type ty with
      | RECORD _ ->
          Lconst 0L
      | REF {contents = None} ->
          error e.epos
            "'nil' should be used in a context where its type can be determined"
      | _ ->
          error e.epos "expected record type, found '%s'" (print_type ty)
      end
  | Evar v ->
      var env v ty
  | Ebinop (x, Op_add, y) ->
      let x = exp env x int_ty in
      let y = exp env y int_ty in
      unify_ty int_ty ty;
      Lprim (Paddint, [x; y])
  | Ebinop (x, Op_sub, y) ->
      let x = exp env x int_ty in
      let y = exp env y int_ty in
      unify_ty int_ty ty;
      Lprim (Psubint, [x; y])
  | Ebinop (x, Op_mul, y) ->
      let x = exp env x int_ty in
      let y = exp env y int_ty in
      unify_ty int_ty ty;
      Lprim (Pmulint, [x; y])
  | Ebinop (x, Op_div, y) ->
      let x = exp env x int_ty in
      let y = exp env y int_ty in
      unify_ty int_ty ty;
      Lprim (Pdivint, [x; y])
  (* | Ebinop (_, x, Op_cmp Ceq, Enil _) *)
  (* | Ebinop (_, Enil _, Op_cmp Ceq, x) -> *)
  (*     exp env x (fun v tx -> *)
  (*       match base_type env tx with *)
  (*       | RECORD _ -> *)
  (*           let v = unop (fun v -> build_ptrtoint v (int_t Sys.word_size)) v in *)
  (*           let c = binop (build_icmp Icmp.Eq) v *)
  (*             (const_null (int_t Sys.word_size)) in *)
  (*           let c = unop (fun v s b -> build_zext v (int_t 32) s b) c in *)
  (*           nxt c INT *)
  (*       | _ -> *)
  (*           error (exp_p x) "expected expression of record type, found %s" *)
  (*             (describe_type tx)) *)
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
  | Eassign (v, e) ->
      let v = assign env v e in
      unify_ty void_ty ty;
      Lsequence (v, Lconst 0L)
  | Ecall (x, xs) ->
      let fi = find_fun x env in
      let ts, t = fi.fsign in
      let rec bind ys = function
        | [], [] ->
            let actuals = List.rev ys in
            unify_ty t ty;
            if fi.f_user then Lapply (fi.fname, actuals) else Lprim (Pccall fi.fname, actuals);
        | x :: xs, t :: ts ->
            let x = exp env x t in
            bind (x :: ys) (xs, ts)
        | _ ->
            error e.epos "bad arity: is %d, should be %d" (List.length xs) (List.length ts);
      in
      bind [] (xs, ts)
  | Eseq (e1, e2) ->
      let l1 = exp env e1 (any_ty ()) in
      let l2 = exp env e2 ty in
      Lsequence (l1, l2)
  (* | Emakearray (x, y, {edesc = Enil}) -> *)
  (*     let t, t' = find_array_type x env in *)
  (*     begin match t' with *)
  (*       | {tdesc = {contents = RECORD _}} -> *)
  (*           let y = int_exp env y in *)
  (*           let sg = [|Tint 32; transl_typ t'|], transl_typ t in *)
  (*           s#insert_op (Ialloca (transl_typ t)) [||] [|id2|]; *)
  (*           s#insert_op (Iexternal ("tiger_make_array", sg)) [|y s; C.null (transl_typ t') s|] [|id1|]; *)
  (*           s#insert_op Istore [|id1; id2|] [||]; *)
  (*           t, C.load (C.var id2) *)
  (*     | _ -> *)
  (*         error e.epos "array base type must be record type" *)
  (*     end *)
  (* | Emakearray (x, y, z) -> *)
  (*     let t, t' = find_array_type x env in *)
  (*     let y = int_exp env y in *)
  (*     let z = typ_exp env z t' in *)
  (*     let id1 = fresh () in *)
  (*     let id2 = fresh () in *)
  (*     let sg = [|Tint 32; transl_typ t'|], transl_typ t in *)
  (*     s#insert_op (Ialloca (transl_typ t)) [||] [|id2|]; *)
  (*     s#insert_op (Iexternal ("tiger_make_array", sg)) [|y s; z s|] [|id1|]; *)
  (*     s#insert_op Istore [|id1; id2|] [||]; *)
  (*     t, C.load (C.var id2) *)
  | Emakerecord (x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            let r = gentmp "rec" in
            let rec bind i = function
              | [] ->
                  unify_ty t ty;
                  Lvar r
              | v :: vs ->
                  Lsequence (Lprim (Psetfield i, [Lvar r; v]), bind (i+1) vs)
            in
            let v = bind 0 (List.rev vs) in
            Llet (r, Lprim (Pccall "tiger_make_record", [Lconst (Int64.of_int (List.length vs))]), v)
        | (x, e) :: xts, (x', t) :: ts ->
            if x.s = x' then
              let e = exp env e t in
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
      in
      bind [] (xts, ts)
  | Eif (e1, e2, e3) ->
      let e1 = exp env e1 int_ty in
      let e2 = exp env e2 ty in
      let e3 = exp env e3 ty in
      Lifthenelse (e1, e2, e3)
  | Ewhile (e1, e2) ->
      let e1 = exp env e1 int_ty in
      let e2 = exp env e2 void_ty in
      unify_ty void_ty ty;
      Lsequence (Lcatch (Lloop (Lifthenelse (e1, e2, Lexit 0))), Lconst 0L)
  | Efor (i, x, y, z) ->
      let x = exp env x int_ty in
      let y = exp env y int_ty in
      let env = add_var i ~immutable:true int_ty env in
      let iend = gentmp "for" in
      let z = exp env z void_ty in
      unify_ty void_ty ty;
      let body =
        Llet
          (i.s, x, Llet
             (iend, y, Lcatch
                (Lloop
                   (Lifthenelse
                      (Lprim (Pintcomp Cle, [Lvar i.s; Lvar iend]),
                       Lsequence (z, Lassign (i.s, Lprim (Paddint, [Lvar i.s; Lconst 1L]))), Lexit 0)))))
      in
      Lsequence (body, Lconst 0L)
  | Ebreak ->
      if env.in_loop then
        Lexit 0
      else
        error e.epos "illegal use of 'break'"
  | Elet (Dvar (x, None, y), z) ->
      let r = ref None in
      let y = exp env y (REF r) in
      let t = match r.contents with Some t -> t | None -> assert false in
      let env = add_var x t env in
      let z = exp env z ty in
      Llet (x.s, y, z)
  | Elet (Dvar (x, Some t, y), z) ->
      let t = find_type t env in
      let y = exp env y t in
      let env = add_var x t env in
      let z = exp env z ty in
      Llet (x.s, y, z)
  | Elet (Dtypes tys, e) ->
      exp (let_type env tys) e ty
  | Elet (Dfuns funs, e) ->
      let_funs env funs e ty

let base_tenv =
  M.add "int" int_ty (M.add "string" string_ty M.empty)

let base_venv =
  let stdlib =
    [
      "print" , [string_ty], void_ty;
      "printi", [int_ty], void_ty;
      "flush", [], void_ty;
      "getchar", [], string_ty;
      "ord", [string_ty], int_ty;
      "chr", [int_ty], string_ty;
      "size", [string_ty], int_ty;
      "substring", [string_ty; int_ty; int_ty], string_ty;
      "concat", [string_ty; string_ty], string_ty;
      "not", [int_ty], int_ty;
      "exit", [int_ty], void_ty;
      "gc_collect", [], void_ty;
    ]
  in
  let decl_fun venv (x, ts, t) =
    let fname = "__tiger__" ^ x in
    M.add x (Function {fname = fname; f_user = false; fsign = (ts, t)}) venv
  in
  List.fold_left decl_fun M.empty stdlib

let program e =
  let env = {tenv = base_tenv; venv = base_venv; in_loop = false} in
  exp env e (any_ty ())
