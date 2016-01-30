(* The MIT License (MIT)

   Copyright (c) 2013-2014 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

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

let tmp_counter = ref (-1)

let gentmp s =
  incr tmp_counter;
  s ^ "__" ^ (string_of_int !tmp_counter)

let last_id = ref (-1)
let fresh () = incr last_id; !last_id

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
  { id: int;
    vtype : type_spec;
    vimm : bool }

type fun_info =
  { fname: string;
    fsign: type_spec list * type_spec;
    f_user: bool }

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type env =
  { venv: value_desc M.t;
    tenv: type_spec M.t;
    in_loop: bool;
    sols: S.t M.t }

let rec base_type env = function
  | NAME x -> base_type env (M.find x env.tenv)
  | _ as t -> t

let type_equal env t1 t2 =
  base_type env t1 == base_type env t2

let empty_env =
  { venv = M.empty;
    tenv = M.empty;
    in_loop = false;
    sols = M.empty }

let find_var id env =
  try
    match M.find id.s env.venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with Not_found ->
    error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?immutable:(immut=false) t env =
  let vi = {id = fresh (); vtype = t; vimm = immut} in
  {env with venv = M.add x.s (Variable vi) env.venv}, vi

let mem_var x env =
  try
    match M.find x env.venv with
    | Variable _ -> true
    | Function _ -> false
  with Not_found ->
    false

let add_fun x uid atyps rtyp env =
  let fi =
    { fname = uid; fsign = atyps, rtyp;
      f_user = true }
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
  with Not_found ->
    error x.p "unbound function '%s'" x.s

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
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in
  loop 0 xts

let rec transl_typ env t =
  let rec loop t =
    match t with
    | VOID    -> Tvoid
    | INT     -> Tint 32
    | STRING  -> Tpointer (Tint 8)
    | ARRAY (_, t) -> (* { i32, [0 x t] }* *)
        Tpointer (loop t) (*  (Tstruct [Tint 32; Tarray (loop t, 0)]) *)
    | RECORD (x, xts) -> Tpointer (Tnamed x)
        (* if not (List.mem_assq t !named_structs) then begin *)
        (*   let ty = named_struct_type g_context x in *)
        (*   named_structs := (t, ty) :: !named_structs; *)
        (*   struct_set_body ty *)
        (*     (Array.of_list (List.map (fun (_, t) -> loop t) xts)) *)
        (*     false *)
        (* end; *)
        (* pointer_type (List.assq t !named_structs) *)
    | NAME y ->
        loop (M.find y env.tenv)
  in
  loop t

type code =
  | Cvar of ident
  | Cnull of ty
  | Cprim of primitive * code list

let rec insert_code = function
  | Cvar id -> id
  | Cnull ty ->
      assert false (* FIXME *)
  | Cprim (p, args) ->
      let id = fresh () in
      let args = List.map insert_code args in
      insert_instr (Ilet (id, p, args));
      id

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

let rec structured_type env t =
  match t with
  | NAME y -> structured_type env (M.find y env.tenv)
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
          List.filter (fun fundef' -> fundef.fn_name.s = fundef'.fn_name.s)
          fundefs in
        if List.length matches > 0 then
          let fundef' = List.hd matches in
          error fundef'.fn_name.p
            "function name '%s' can only be defined once in each type declaration"
            fundef'.fn_name.s
        else
          bind fundefs
  in bind fundefs

let tr_return_type env fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t env

let fundecls = ref []

let tr_function_header env fn =
  let rtyp = tr_return_type env fn in
  let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in
  let uid = gentmp fn.fn_name.s in
  add_fun fn.fn_name uid argst rtyp env

let rec tr_function_body env fundef =
  let type_of_free_var x =
    match M.find x env.venv with
    | Variable vi -> Tpointer (transl_typ env vi.vtype)
    | Function _ -> assert false
  in
  let find_free_var x =
    match M.find x env.venv with
    | Variable vi ->
        vi
    | Function _ ->
        assert false
  in
  let fi = find_fun fundef.fn_name env in
  let ts, t = fi.fsign in
  let fvs = S.elements (M.find fundef.fn_name.s env.sols) in
  let args1 = List.map find_free_var fvs in
  let tys1 = List.map type_of_free_var fvs in
  let env =
    List.fold_left2 (fun env x vi ->
        let venv = M.add x (Variable vi) env.venv in
        {env with venv}
      ) env fvs args1
  in
  let args1 = List.map (fun vi -> vi.id) args1 in
  let env =
    List.fold_left2 (fun env (x, _) t ->
        let env, _ = add_var x t (* a *) env in
        env
      ) env fundef.fn_args ts
  in
  let args2 = List.map (fun (arg, _) -> (find_var arg env).id) fundef.fn_args in
  let tys2 = List.map (transl_typ env) ts in
  let body =
    extract_instr_seq (fun () ->
        let e = typ_exp {env with in_loop = false} fundef.fn_body t in
        if fundef.fn_rtyp = None then
          insert_instr (Ireturn None)
        else
          insert_instr (Ireturn (Some (insert_code e)))
      )
  in
  let rty = transl_typ env (tr_return_type env fundef) in
  let signature = (tys1 @ tys2), rty in
  fundecls := {name = fi.fname; args = args1 @ args2; signature; body} :: !fundecls

and let_funs env fundefs =
  check_unique_fundef_names fundefs;
  let sols' =
    List.fold_left
      (fun s f ->
         let ffv =
           List.fold_left (fun s (x, _) -> S.remove x.s s) (fv f.fn_body) f.fn_args
         in
         S.union ffv s
      ) S.empty fundefs
  in
  let sols' = List.fold_left (fun sols f -> M.add f.fn_name.s sols' sols) env.sols fundefs in
  let env' = {env with sols = sols'} in
  let env' = List.fold_left tr_function_header env' fundefs in
  List.iter (tr_function_body env') fundefs;
  env'

and array_var env v =
  let t, v' = var env v in
  match base_type env t with
  | ARRAY (_, t') -> t', v'
  | _ ->
      error v.vpos "expected variable of array type, but type is '%s'"
        (describe_type t)

and record_var env v =
  let t, v' = var env v in
  match base_type env t with
  | RECORD _ -> t, v'
  | _ ->
      error v.vpos "expected variable of record type, but type is '%s'"
        (describe_type t)

and typ_exp env e t' =
  let t, e' = exp env e in
  if type_equal env t t' then e'
  else
    error e.epos
      "type mismatch: expected type '%s', instead found '%s'"
      (string_of_type t') (string_of_type t)

and int_exp env e =
  typ_exp env e INT

and void_exp env e =
  ignore (typ_exp env e VOID)

(* Main typechecking/compiling functions *)

and var env v =
  match v.vdesc with
  | Vsimple x ->
      let vi = find_var x env in
      vi.vtype, Cvar vi.id
  | Vsubscript (v, x) ->
      let t', v = array_var env v in
      let x = int_exp env x in
      t', Cprim (Pgep, [Cprim (Pload, [v]); x])
  | Vfield (v, x) ->
      let t', v = record_var env v in
      let i, tx = find_record_field env t' x in
      tx, Cprim (Pgep, [Cprim (Pload, [v]); Cprim (Pconstint 0l, []); Cprim (Pconstint (Int32.of_int i), [])])

and exp env e =
  match e.edesc with
  | Eunit ->
      VOID, Cprim (Pconstint 0l, [])
  | Eint n ->
      INT, Cprim (Pconstint n, [])
  | Estring s ->
      failwith "Estring not implemented"
      (* nxt (VAL (build_global_stringptr s "" g_builder)) STRING *)
  | Enil ->
      error e.epos
        "'nil' should be used in a context where \
         its type can be determined"
  | Evar v ->
      let t, v = var env v in
      t, Cprim (Pload, [v])
  | Ebinop (x, Op_add, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      INT, Cprim (Paddint, [x; y])
  | Ebinop (x, Op_sub, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      INT, Cprim (Psubint, [x; y])
  | Ebinop (x, Op_mul, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      INT, Cprim (Pmulint, [x; y])
  | Ebinop (x, Op_div, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      INT, Cprim (Pdivint, [x; y])
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
  | Eassign (v, {edesc = Enil}) ->
      let t, v = var env v in
      begin match base_type env t with
        | RECORD _ ->
            insert_instr (Istore (insert_code (Cprim (Pconstint 0l, [])), insert_code v));
            VOID, Cprim (Pconstint 0l, [])
        | _ ->
            error e.epos "trying to assign 'nil' to a field of non-record type"
      end
  | Eassign (v, e) ->
      let t, v = var env v in
      let e = typ_exp env e t in
      insert_instr (Istore (insert_code e, insert_code v));
      VOID, Cprim (Pconstint 0l, [])
  | Ecall (x, xs) ->
      let fi = find_fun x env in
      let ts, t = fi.fsign in
      if List.length xs <> List.length ts then
        error e.epos "bad arity: is %d, should be %d" (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            let actuals =
              if fi.f_user then
                List.fold_right (fun x ys ->
                    let vi = find_var {s = x; p = Lexing.dummy_pos} env in
                    Cvar vi.id :: ys
                  ) (S.elements (M.find x.s env.sols)) (List.rev ys)
              else
                List.rev ys
            in
            let id = fresh () in
            insert_instr (Iapply (id, fi.fname, List.map insert_code actuals));
            t, Cvar id
        | {edesc = Enil; epos = p} :: xs, t :: ts ->
            begin match base_type env t with
              | RECORD _ ->
                  bind (Cnull (transl_typ env t) :: ys) (xs, ts)
              | _ ->
                  error p "expected record type, found '%s'" (describe_type t)
            end
        | x :: xs, t :: ts ->
            let x = typ_exp env x t in
            (* let x = save (structured_type env t && List.exists triggers xs) x in *)
            bind (x :: ys) (xs, ts)
        | _ ->
            assert false
      in
      bind [] (xs, ts)
  | Eseq (e1, e2) ->
      let _ = exp env e1 in
      exp env e2
  | Emakearray (x, y, {edesc = Enil}) ->
      let t, t' = find_array_type x env in
      begin match base_type env t' with
        | RECORD _ ->
            let y = int_exp env y in
            let id1 = fresh () in
            let id2 = fresh () in
            let sg = [Tint 32; transl_typ env t'], transl_typ env t in
            insert_instr (Ialloca (id2, transl_typ env t));
            insert_instr (Iexternal (id1, "tiger_make_array", sg, [insert_code y; insert_code (Cnull (transl_typ env t'))]));
            insert_instr (Istore (id1, id2));
            t, Cprim (Pload, [Cvar id2])
      | _ ->
          error e.epos "array base type must be record type"
      end
  | Emakearray (x, y, z) ->
      let t, t' = find_array_type x env in
      let y = int_exp env y in
      let z = typ_exp env z t' in
      let id1 = fresh () in
      let id2 = fresh () in
      let sg = [Tint 32; transl_typ env t'], transl_typ env t in
      insert_instr (Ialloca (id2, transl_typ env t));
      insert_instr (Iexternal (id1, "tiger_make_array", sg, [insert_code y; insert_code z]));
      insert_instr (Istore (id1, id2));
      t, Cprim (Pload, [Cvar id2])
  | Emakerecord (x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            (* let t' = element_type (transl_typ env t) in *)
            (* debug () "%s" (string_of_lltype t'); *)
            (* let r = VAL (gc_alloc_type t') in *)
            let id1 = fresh () in
            let id2 = fresh () in
            insert_instr (Ialloca (id2, transl_typ env t));
            insert_instr (Iexternal (id1, "tiger_make_record", assert false, [])); (* FIXME *)
            insert_instr (Istore (id1, id2));
            let f i = Cprim (Pgep, [Cvar id2; Cprim (Pconstint 0l, []); Cprim (Pconstint (Int32.of_int i), [])]) in
            let rec bind i = function
              | [] -> t, Cprim (Pload, [Cvar id2])
              | v :: vs ->
                  insert_instr (Istore (insert_code v, insert_code (f i)));
                  bind (i+1) vs
            in
            bind 0 (List.rev vs)
        | (x, {edesc = Enil}) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (Cnull (transl_typ env t) :: vs) (xts, ts)
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
      in
      bind [] (xts, ts)
  | Eif (e1, e2, e3) ->
      let e1 = int_exp env e1 in
      let t = ref VOID in
      let id = fresh () in
      let ifso =
        extract_instr_seq (fun () ->
            let t2, e2 = exp env e2 in
            t := t2;
            insert_instr (Istore (insert_code e2, id))
        )
      in
      let ifnot =
        extract_instr_seq (fun () ->
            let e3 = typ_exp env e3 !t in
            insert_instr (Istore (insert_code e3, id))
          )
      in
      insert_instr (Iifthenelse (insert_code e1, ifso, ifnot));
      !t, Cprim (Pload, [Cvar id])
  | Ewhile (e1, e2) ->
      let ifso = extract_instr_seq (fun () -> ignore (exp env e2)) in
      let ifnot = extract_instr_seq (fun () -> insert_instr (Iexit 0)) in
      let body =
        extract_instr_seq (fun () ->
            insert_instr (Iifthenelse (insert_code (int_exp env e1), ifso, ifnot))
          )
      in
      insert_instr (Icatch body);
      VOID, Cprim (Pconstint 0l, [])
  | Efor (i, x, y, z) ->
      let x = int_exp env x in
      let y = int_exp env y in
      let env, i = add_var i ~immutable:true INT env in
      insert_instr (Ialloca (i.id, Tint 32));
      insert_instr (Istore (insert_code x, i.id));
      let body =
        extract_instr_seq (fun () ->
            void_exp env z;
            insert_instr (Istore (insert_code (Cprim (Paddint, [Cprim (Pconstint 1l, []); Cprim (Pload, [Cvar i.id])])), i.id))
          )
      in
      let test =
        extract_instr_seq (fun () ->
            let ifso = body in
            let ifnot = extract_instr_seq (fun () -> insert_instr (Iexit 0)) in
            insert_instr (Iifthenelse (insert_code (Cprim (Pcmpint Cleq, [Cprim (Pload, [Cvar i.id]); y])), ifso, ifnot))
          )
      in
      insert_instr (Icatch (extract_instr_seq (fun () -> insert_instr (Iloop test))));
      VOID, Cprim (Pconstint 0l, [])
  | Ebreak ->
      if env.in_loop then begin
        insert_instr (Iexit 0);
        VOID, Cprim (Pconstint 0l, []) (* FIXME FIXME *)
      end else
        error e.epos "illegal use of 'break'"
  | Elet (Dvar (x, None, y), z) ->
      let ty, y = exp env y in
      let env, x = add_var x ty env in
      insert_instr (Ialloca (x.id, transl_typ env ty));
      insert_instr (Istore (insert_code y, x.id));
      exp env z
  | Elet (Dvar (x, Some t, {edesc = Enil}), z) ->
      let t = find_type t env in
      begin match base_type env t with
      | RECORD _ ->
          let env, x = add_var x t env in
          insert_instr (Ialloca (x.id, transl_typ env t));
          insert_instr (Istore (insert_code (Cprim (Pconstint 0l, [])), x.id));
          exp env z
      | _ ->
          error e.epos "expected record type, found '%s'" (describe_type t)
      end
  | Elet (Dvar (x, Some t, y), z) ->
      let ty = find_type t env in
      let y = typ_exp env y ty in
      let env, x = add_var x ty env in
      insert_instr (Ialloca (x.id, transl_typ env ty));
      insert_instr (Istore (insert_code y, x.id));
      exp env z
  | Elet (Dtypes tys, e) ->
      let env = let_type env tys in
      exp env e
  | Elet (Dfuns funs, e) ->
      exp (let_funs env funs) e

let base_tenv =
  M.add "int" INT (M.add "string" STRING M.empty)

let base_venv =
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
      "gc_collect", [], VOID;
    ]
  in
  let decl_fun venv (x, ts, t) =
    let fname = "__tiger__" ^ x in
    M.add x (Function {fname = fname; f_user = false; fsign = (ts, t)}) venv
  in
  List.fold_left decl_fun M.empty stdlib

let program e =
  fundecls := [];
  let env = {tenv = base_tenv; venv = base_venv; in_loop = false; sols = M.empty} in
  let i =
    extract_instr_seq (fun () ->
        let _ = exp env e in
        insert_instr (Ireturn (Some (insert_code (Cprim (Pconstint 0l, [])))))
      )
  in
  {name = "_tiger_main"; args = []; signature = ([], Tint 32); body = i} :: !fundecls
