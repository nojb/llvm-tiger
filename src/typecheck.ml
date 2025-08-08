open Error
open Typing
open Tabs

let seq s1 s2 =
  match s1, s2 with
  | Sskip, s | s, Sskip -> s
  | _ -> Sseq (s1, s2)

type value =
  | Var of type_id * Typing.ident
  | Fun of (type_id list * type_id option) * string

module StringMap = Map.Make(String)

type env =
  {
    vars: (Typing.ident, type_id) Hashtbl.t;
    cstr: (Typing.ident, type_structure) Hashtbl.t;
    venv: value StringMap.t;
    tenv: type_id StringMap.t;
    loop: bool;
    next_ident: Ident.state;
  }

let type_eq tid1 tid2 =
  match tid1, tid2 with
  | Tint, Tint
  | Tstring, Tstring -> true
  | Tconstr s1, Tconstr s2 -> Ident.equal s1 s2
  | _ -> false

let empty_env venv tenv =
  { vars = Hashtbl.create 0;
    cstr = Hashtbl.create 0;
    venv;
    tenv;
    loop = false;
    next_ident = Ident.new_state () }

type error =
  | Unbound_variable of string
  | Unknown_function of string
  | Unknown_type_name of string
  | Wrong_arity of int * int

exception Error of Lexing.position * error

let find_var id env =
  match StringMap.find_opt id.desc env.venv with
  | Some (Var (tid, id)) -> tid, id
  | Some (Fun _) | None -> raise (Error (id.loc, Unbound_variable id.desc))

let find_fun id env =
  match StringMap.find_opt id.desc env.venv with
  | Some (Fun (sign, impl)) -> sign, impl
  | Some (Var _) | None -> raise (Error (id.loc, Unknown_function id.desc))

let find_type env id =
  match StringMap.find_opt id.desc env.tenv with
  | Some tid -> tid
  | None -> raise (Error (id.loc, Unknown_type_name id.desc))

let add_var env (x : ident) tid =
  let id = Ident.create env.next_ident x.desc in
  Hashtbl.add env.vars id tid;
  Typing.Vsimple id, {env with venv = StringMap.add x.desc (Var (tid, id)) env.venv}

let add_fresh_var env tid =
  let id = Ident.create env.next_ident "tmp" in
  Hashtbl.add env.vars id tid;
  Typing.Vsimple id

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
  | Some (x, _) -> error x.loc "duplicate %s: %s" s x.desc

let add_types env xts =
  check_unique fst xts "type name";
  let constrs, xts' =
    List.fold_left (fun (constrs, xts) (name, ty) ->
        match ty with
        | Tname s ->
            constrs, (name, `Tname s) :: xts
        | Tarray ty ->
            let constr = Ident.create env.next_ident name.desc in
            StringMap.add name.desc (Tconstr constr) constrs,
            (name, `Tarray (constr, ty)) :: xts
        | Trecord fl ->
            let constr = Ident.create env.next_ident name.desc in
            StringMap.add name.desc (Tconstr constr) constrs,
            (name, `Trecord (constr, fl)) :: xts
      ) (StringMap.empty, []) xts
  in
  let xts' = List.rev xts' in
  let resolve name =
    let visited = Hashtbl.create 0 in
    let rec loop name =
      if Hashtbl.mem visited name then failwith "recursive loop";
      Hashtbl.add visited name ();
      match List.find_map (fun (x, ty) -> if x.desc = name then Some ty else None) xts with
      | None ->
          begin match StringMap.find_opt name env.tenv with
          | None -> failwith "type not found"
          | Some tid -> tid
          end
      | Some (Tarray _ | Trecord _) ->
          begin match StringMap.find_opt name constrs with
          | Some tconstr -> tconstr
          | None -> assert false
          end
      | Some Tname s ->
          loop s.desc
    in
    loop name
  in
  let f = function
    | `Tarray (constr, elt) ->
        Hashtbl.replace env.cstr constr (Tarray (resolve elt.desc));
        Tconstr constr
    | `Trecord (constr, fields) ->
        let fields = List.map (fun (x, ty) -> x.desc, resolve ty.desc) fields in
        Hashtbl.replace env.cstr constr (Trecord fields);
        Tconstr constr
    | `Tname s ->
        resolve s.desc
  in
  let tenv =
    List.fold_left (fun tenv (name, desc) ->
        StringMap.add name.desc (f desc) tenv
      ) env.tenv xts'
  in
  {env with tenv}

let loc_of_variable v =
  {
    filename = v.loc.pos_fname;
    lineno = v.loc.pos_lnum;
    column = v.loc.pos_cnum - v.loc.pos_bol + 1;
  }

let rec statement env e =
  let s, e = expression env e in
  match e with
  | None -> s
  | Some _ -> failwith "type error"

and variable env v : statement * type_id * variable =
  match v.desc with
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
            | Trecord _ -> error v.loc "expected variable of array type"
            end
        | _ ->
            error v.loc "expected variable of array type"
      in
      let s2, x = expression' env x Tint in
      seq s1 s2, t', Vsubscript (t', v', x)
  | Vfield (v, x) ->
      let s, ty, v' = variable env v in
      let xts =
        match ty with
        | Tconstr tid ->
            begin match Hashtbl.find env.cstr tid with
            | Trecord fields -> fields
            | Tarray _ -> error v.loc "expected variable of record type"
            end
        | _ ->
            error v.loc "expected variable of record type"
      in
      let i, tx =
        let rec loop i = function
          | [] -> error x.loc "record type does not contain field"
          | (x', t') :: _xs when x' = x.desc -> i, t'
          | _ :: xs -> loop (i+1) xs
        in
        loop 0 xts
      in
      let typ = Array.of_list (List.map snd xts) in
      let loc = loc_of_variable v in
      s, tx, Vfield (loc, typ, v', i)

and declarations env ds : statement * env =
  match ds with
  | [] -> Sskip, env
  | Dvar (x, xty, init) :: ds ->
      let sinit, tid', einit =
        match xty with
        | None -> expression'' env init
        | Some sty ->
            let ty = find_type env sty in
            let s, e = expression' env init ty in
            s, ty, e
      in
      let var, env = add_var env x tid' in
      let s', env = declarations env ds in
      seq sinit (seq (Sassign (var, einit)) s'), env
  | Dtype (s, ty) :: ds ->
      let rec loop accu = function
        | [] -> List.rev accu, []
        | Dtype (s, ty) :: ds -> loop ((s, ty) :: accu) ds
        | (Dvar _ | Dfun _) :: _ as ds -> List.rev accu, ds
      in
      let tys, ds = loop [s, ty] ds in
      declarations (add_types env tys) ds
  | Dfun _ :: _ ->
      assert false
(* expression' (add_funs env funs) e ty *)

and expression' env e (ty : type_id) : statement * expression =
  match e.desc with
  | Enil ->
      begin match ty with
      | Tconstr tid ->
          begin match Hashtbl.find env.cstr tid with
          | Trecord _ -> Sskip, Enil
          | Tarray _ -> assert false
          end
      | _ ->
          assert false
      end
  | Eseq el ->
      let rec loop = function
        | [] -> failwith "type error"
        | [e] ->
            expression' env e ty
        | e :: el ->
            let s1, _ = expression env e in
            let s2, e2 = loop el in
            seq s1 s2, e2
      in
      loop el
  | Eif (e1, e2, Some e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 ty in
      let s3, e3 = expression' env e3 ty in
      let v = add_fresh_var env ty in
      seq s1 (Sifthenelse (e1, seq s2 (Sassign (v, e2)), seq s3 (Sassign (v, e3)))), Evar (ty, v)
  | Elet (ds, e) ->
      let s1, env = declarations env ds in
      let s2, e = expression' env e ty in
      seq s1 s2, e
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
  match e.desc with
  | Eint n ->
      Sskip, Some (Tint, Eint n)
  | Estring s ->
      Sskip, Some (Tstring, Estring s)
  | Enil ->
      error e.loc
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
  | Ebinop (e1, Op_cmp c, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some (Tint, Ebinop (e1, Op_cmp c, e2))
  | Eassign (v, e) ->
      let s1, ty, v = variable env v in
      let s2, e = expression' env e ty in
      seq s1 (seq s2 (Sassign (v, e))), None
  | Ecall (fn, params) ->
      let (args, res) as sign, impl = find_fun fn env in
      let num_expected = List.length args in
      let num_actual = List.length params in
      if num_expected <> num_actual then raise (Error (fn.loc, Wrong_arity (num_expected, num_actual)));
      let s, params =
        List.fold_left2 (fun (s, el) arg param -> let s', e' = expression' env param arg in seq s s', e' :: el)
          (Sskip, []) args params
      in
      begin match res with
      | None -> seq s (Scall (None, impl, List.rev params, sign)), None
      | Some _ -> assert false
      end
  | Eseq el ->
      List.fold_left (fun (s, _) e ->
          let s', e = expression env e in
          seq s s', e
        ) (Sskip, None) el
  | Earray (ty, e1, e2) ->
      let ty, elty =
        match find_type env ty with
        | Tconstr id as ty ->
            begin match Hashtbl.find env.cstr id with
            | Tarray tid -> ty, tid
            | Trecord _ -> assert false
            end
        | _ -> assert false
      in
      let s1, size = expression' env e1 Tint in
      let s2, init = expression' env e2 elty in
      let v = add_fresh_var env ty in
      seq s1 (seq s2 (Sarray (v, size, elty, init))), Some (ty, Evar (ty, v))
  | Erecord (ty, fl) ->
      let ty, ftyl =
        match find_type env ty with
        | Tconstr id as ty ->
            begin match Hashtbl.find env.cstr id with
            | Tarray _ -> assert false
            | Trecord fields -> ty, fields
            end
        | _ -> assert false
      in
      if List.length ftyl <> List.length fl then assert false;
      let s, tfl =
        List.fold_left2 (fun (s, el) (name, e) (name', ty) ->
            if name.desc <> name' then assert false;
            let s', e = expression' env e ty in
            seq s s', e :: el
          ) (Sskip, []) fl ftyl
      in
      let tfl = List.rev tfl in
      let v = add_fresh_var env ty in
      seq s (Srecord (v, Array.of_list (List.map snd ftyl), tfl)), Some (ty, Evar (ty, v))
  | Eif (e1, e2, e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression env e2 in
      let s3, e3 =
        match e3 with
        | None -> Sskip, None
        | Some e3 -> expression env e3
      in
      begin match e2, e3 with
      | None, None -> seq s1 (Sifthenelse (e1, s2, s3)), None
      | Some _, None | None, Some _ -> failwith "type error"
      | Some (t2, e2), Some (t3, e3) ->
          if not (type_eq t2 t3) then failwith "type error";
          let v = add_fresh_var env t2 in
          seq s1 (Sifthenelse (e1, seq s2 (Sassign (v, e2)), seq s3 (Sassign (v, e3)))), Some (t2, Evar (t2, v))
      end
  | Ewhile (e1, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2 = statement {env with loop = true} e2 in
      seq s1 (Sloop (seq s1 (Sifthenelse (e1, s2, Sbreak)))), None
  | Efor (i, e1, e2, e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      let i, env = add_var env i Tint in
      let s3 = statement {env with loop = true} e3 in
      let loop =
        Sloop (Sifthenelse
                 (Ebinop(e2, Op_cmp Clt, Evar (Tint, i)),
                  Sbreak, seq s3 (Sassign (i, Ebinop (Evar (Tint, i), Op_add, Eint 1L)))))
      in
      seq s1 (seq s2 (seq (Sassign (i, e1)) loop)), None
  | Ebreak ->
      if not env.loop then error e.loc "illegal use of 'break'";
      Sbreak, None
  | Elet (ds, e) ->
      let s1, env = declarations env ds in
      let s2, e = expression env e in
      seq s1 s2, e

let base_tenv =
  StringMap.of_list
    [
      "int", Tint;
      "string", Tstring;
    ]

let stdlib =
  [
    "printi", [Tint], None, "TIG_printi";
    "print", [Tstring], None, "TIG_print";
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
  let f venv (name, args, res, impl) = StringMap.add name (Fun ((args, res), impl)) venv in
  List.fold_left f StringMap.empty stdlib

let program (p : Tabs.program) =
  let env = empty_env base_venv base_tenv in
  let body = statement env p.body in
  {p_name = p.name; p_cstr = env.cstr; p_vars = env.vars; p_body = body}
