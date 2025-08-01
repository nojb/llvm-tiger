open Error
open Tabs
open Typing

let seq s1 s2 =
  match s1, s2 with
  | Sskip, s | s, Sskip -> s
  | _ -> Sseq (s1, s2)

type value =
  | Var of type_id * string
  | Fun of (type_id list * type_id option) * string

module M = Map.Make(String)

type env =
  {
    vars: (string, type_id) Hashtbl.t;
    funs: (string, fundef) Hashtbl.t;
    cstr: (string, type_structure) Hashtbl.t;
    venv: value M.t;
    tenv: type_id M.t;
    loop: bool;
    cntr: int ref;
  }

let fresh env s =
  incr env.cntr;
  Printf.sprintf "%s.%i" s !(env.cntr)

let type_eq tid1 tid2 =
  match tid1, tid2 with
  | Tint, Tint
  | Tstring, Tstring -> true
  | Tconstr s1, Tconstr s2 -> String.equal s1 s2
  | _ -> false

let empty_env venv tenv =
  { vars = Hashtbl.create 0;
    funs = Hashtbl.create 0;
    cstr = Hashtbl.create 0;
    venv;
    tenv;
    loop = false;
    cntr = ref 0 }

type error =
  | Unbound_variable of string
  | Wrong_arity of int * int

exception Error of Lexing.position * error

let find_var id env =
  match M.find_opt id.s env.venv with
  | Some (Var (tid, id)) -> tid, id
  | Some (Fun _) | None -> raise (Error (id.p, Unbound_variable id.s))

let find_fun id env =
  match M.find_opt id.s env.venv with
  | Some (Fun (sign, impl)) -> sign, impl
  | Some (Var _) | None -> raise (Error (id.p, Unbound_variable id.s))

let add_var env (x : pos_string) tid =
  let id = fresh env x.s in
  Hashtbl.add env.vars id tid;
  id, {env with venv = M.add x.s (Var (tid, id)) env.venv}

let add_fresh_var env tid =
  let id = fresh env "tmp" in
  Hashtbl.add env.vars id tid;
  id

(* let mem_var x env =
   try
    match M.find x env.venv with
    | Variable _ -> true
    | Function _ -> false
   with Not_found ->
    false *)

(* let add_fun x uid atyps rtyp free_vars env =
   let fi = { name = uid; sign = atyps, rtyp } in
   {env with venv = M.add x.s (Function fi) env.venv} *)

(* let find_fun x env =
   try
    match M.find x.s env.venv with
    | Variable _ -> raise Not_found
    | Function fi -> fi
   with Not_found ->
    error x.p "unbound function '%s'" x.s *)

(* let find_type x env =
   try
    M.find x.s env.tenv
   with Not_found ->
    error x.p "unbound type '%s'" x.s *)

(* let find_array_type x env =
   match find_type x env with
   | {tdesc = {contents = ARRAY t'}; _} as t -> t, t'
   | _ as t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s t.tname

   let find_record_type env x =
   match find_type x env with
   | {tdesc = {contents = RECORD xts}; _} as t -> t, xts
   | _ as t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s t.tname *)

let has_duplicate (type a) (f : a -> 'b) (l : a list) =
  let exception Found of a in
  let h = Hashtbl.create 0 in
  match
    List.iter (fun x ->
        let y = f x in
        match Hashtbl.find_opt h y with Some () -> raise (Found x) | None -> Hashtbl.add h y ()
      ) l
  with
  | () -> None
  | exception Found x -> Some x

let check_unique f xts s =
  match has_duplicate f xts with
  | None -> ()
  | Some (x, _) -> error x.p "duplicate %s: %s" s x.s

let add_types env xts =
  check_unique fst xts "type name";
  let add_constr name (cstr : type_structure) =
    let s = fresh env name in
    Hashtbl.add env.cstr s cstr;
    Tconstr s
  in
  let f tenv' (name, _ty) =
    let name = name.s in
    let rec loop visited name' =
      if Hashtbl.mem visited name' then failwith "recursive loop";
      Hashtbl.add visited name' ();
      match (List.find_map (fun (x, ty) -> if x.s = name' then Some ty else None) xts : typ option) with
      | None ->
          begin match M.find_opt name' env.tenv with
          | None -> failwith "type not found"
          | Some tid -> tid
          end
      | Some Tarray elt ->
          add_constr name (Tarray (loop (Hashtbl.create 0) elt.s))
      | Some Trecord fields ->
          let fields =
            List.map (fun (x, ty) -> x.s, loop (Hashtbl.create 0) ty.s) fields
          in
          add_constr name (Trecord fields)
      | Some Tname s ->
          loop visited s.s
    in
    M.add name (loop (Hashtbl.create 0) name) tenv'
  in
  {env with tenv = List.fold_left f env.tenv xts}

let rec statement env e =
  let s, e = expression env e in
  match e with
  | None -> s
  | Some _ -> failwith "type error"

and variable env v : statement * type_id * variable =
  match v.vdesc with
  | Vsimple x ->
      let tid, id = find_var x env in
      Sskip, tid, Vsimple id
  | Vsubscript (v, x) ->
      let s1, ty, v' = variable env v in
      let t' =
        match ty with
        | Tconstr tid ->
            begin match Hashtbl.find env.cstr tid with
            | Tarray tid -> tid
            | Trecord _ -> error v.vpos "expected variable of array type"
            end
        | _ ->
            error v.vpos "expected variable of array type"
      in
      let s2, x = expression' env x Tint in
      seq s1 s2, t', Vsubscript (v', x)
  | Vfield (v, x) ->
      let s, ty, v' = variable env v in
      let xts =
        match ty with
        | Tconstr tid ->
            begin match Hashtbl.find env.cstr tid with
            | Trecord fields -> fields
            | Tarray _ -> error v.vpos "expected variable of record type"
            end
        | _ ->
            error v.vpos "expected variable of record type"
      in
      let i, tx =
        let rec loop i = function
          | [] -> error x.p "record type does not contain field"
          | (x', t') :: _xs when x' = x.s -> i, t'
          | _ :: xs -> loop (i+1) xs
        in
        loop 0 xts
      in
      s, tx, Vfield (v', i)

and expression' env e (ty : type_id) : statement * expression =
  match e.edesc with
  | Enil ->
      assert false
  | Eseq (e1, e2) ->
      let s1, _ = expression env e1 in
      let s2, e2 = expression' env e2 ty in
      seq s1 s2, e2
  | Eif (e1, e2, e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 ty in
      let s3, e3 = expression' env e3 ty in
      let r = add_fresh_var env ty in
      let v = Vsimple r in
      seq s1 (Sifthenelse (e1, seq s2 (Sassign (v, e2)), seq s3 (Sassign (v, e3)))), Evar (ty, v)
  | Elet (Dvar (x, xty, init), body) ->
      let sinit, tid', einit =
        match xty with
        | None -> expression'' env init
        | Some _ ->
            assert false
            (* expression' env init xty *)
      in
      let id, env = add_var env x tid' in
      let sbody, ebody = expression' env body ty in
      seq sinit (seq (Sassign (Vsimple id, einit)) sbody), ebody
  | Elet (Dtypes tys, e) ->
      expression' (add_types env tys) e ty
  | Elet (Dfuns _, _) ->
      assert false
  (* expression' (add_funs env funs) e ty *)
  | _ ->
      let s, e = expression env e in
      match e with
      | None -> s, failwith "type error"
      | Some (ty', e') -> if ty = ty' then s, e' else failwith "type error"

and expression'' env e : statement * type_id * expression =
  match expression env e with
  | s, Some (ty, e) -> s, ty, e
  | _, None -> failwith "type error"

and expression env e : statement * (type_id * expression) option =
  match e.edesc with
  | Eunit ->
      Sskip, None
  | Eint n ->
      Sskip, Some (Tint, Eint n)
  | Estring s ->
      Sskip, Some (Tstring, Estring s)
  | Enil ->
      error e.epos
        "'nil' should be used in a context where \
         its type can be determined"
  | Evar v ->
      let s, t, v = variable env v in
      s, Some (t, Evar (t, v))
  | Ebinop (e1, Op_add, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some (Tint, Ebinop (e1, Op_add, e2))
  | Ebinop (e1, Op_sub, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some (Tint, Ebinop (e1, Op_sub, e2))
  | Ebinop (e1, Op_mul, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some (Tint, Ebinop (e1, Op_mul, e2))
  | Ebinop (e1, Op_div, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some (Tint, Ebinop (e1, Op_div, e2))
  | Ebinop _ ->
      failwith "not implemented"
  | Eassign (v, e) ->
      let s1, ty, v = variable env v in
      let s2, e = expression' env e ty in
      seq s1 (seq s2 (Sassign (v, e))), None
  | Ecall (fn, params) ->
      let (args, res) as sign, impl = find_fun fn env in
      let num_expected = List.length args in
      let num_actual = List.length params in
      if num_expected <> num_actual then raise (Error (fn.p, Wrong_arity (num_expected, num_actual)));
      let s, params =
        List.fold_left2 (fun (s, el) arg param -> let s', e' = expression' env param arg in seq s s', e' :: el)
          (Sskip, []) args params
      in
      begin match res with
      | None -> seq s (Scall (impl, List.rev params, sign)), None
      | Some _ -> assert false
      end
  | Eseq (e1, e2) ->
      let s1, _ = expression env e1 in
      let s2, e2 = expression env e2 in
      seq s1 s2, e2
  | Emakearray _
  (* let s1, size = expression' env size Tint in
     let s2, init = expression env init in
     seq s1 s2, Some (x, Earray (x, size, init)) *)
  | Emakerecord _ ->
      assert false
  | Eif (e1, e2, e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression env e2 in
      let s3, e3 = expression env e3 in
      begin match e2, e3 with
      | None, None -> seq s1 (Sifthenelse (e1, s2, s3)), None
      | Some _, None | None, Some _ -> failwith "type error"
      | Some (t2, e2), Some (t3, e3) ->
          if not (type_eq t2 t3) then failwith "type error";
          let r = add_fresh_var env t2 in
          let v = Vsimple r in
          seq s1 (Sifthenelse (e1, seq s2 (Sassign (v, e2)), seq s3 (Sassign (v, e3)))), Some (t2, Evar (t2, v))
      end
  | Ewhile (e1, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2 = statement env e2 in
      seq s1 (Sloop (seq s1 (Sifthenelse (e1, s2, Sbreak)))), None
  | Efor (i, e1, e2, e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      let i, env = add_var env i Tint in
      let s3 = statement env e3 in
      let loop =
        Sloop (Sifthenelse
                 (Ebinop(e2, Op_cmp Clt, Evar (Tint, Vsimple i)),
                  Sbreak, seq s3 (Sassign (Vsimple i, Ebinop (Evar (Tint, Vsimple i), Op_add, Eint 1l)))))
      in
      seq s1 (seq s2 (seq (Sassign (Vsimple i, e1)) loop)), None
  | Ebreak ->
      if not env.loop then error e.epos "illegal use of 'break'";
      Sbreak, None
  | Elet (Dvar (x, ty, init), body) ->
      let sinit, ty, einit =
        match ty with
        | None -> expression'' env init
        | Some _ ->
            assert false
            (* expression' env init ty *)
      in
      let x, env = add_var env x ty in
      let sbody, ebody = expression env body in
      seq sinit (seq (Sassign (Vsimple x, einit)) sbody), ebody
  | Elet (Dtypes tys, body) ->
      expression (add_types env tys) body
  | Elet (Dfuns _, _) ->
      assert false
(* expression (add_funs env fns) body *)

let base_tenv =
  M.add "int" Tint (M.add "string" Tstring M.empty)

let stdlib =
  [
    "printi", [Tint], None, "TIG_printi";
  ]

(* let stdlib =
   [
    "print" , [Tstring], None;
    "printi", [Tint], None;
    "flush", [], None;
    "getchar", [], Some Tstring;
    "ord", [Tstring], Some Tint;
    "chr", [Tint], Some Tstring;
    "size", [Tstring], Some Tint;
    "substring", [Tstring; Tint; Tint], Some Tstring;
    "concat", [Tstring; Tstring], Some Tstring;
    "not", [Tint], Some Tint;
    "exit", [Tint], None;
   ] *)

let base_venv =
  let f venv (name, args, res, impl) = M.add name (Fun ((args, res), impl)) venv in
  List.fold_left f M.empty stdlib

let program (p : Tabs.program) =
  let env = empty_env base_venv base_tenv in
  let body = statement env p.body in
  {p_name = p.name; p_cstr = env.cstr; p_funs = env.funs; p_vars = env.vars; p_body = body}
