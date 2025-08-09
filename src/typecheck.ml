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
  | Duplicate_type_name of string
  | Not_a_statement
  | Not_a_record of type_id
  | Not_an_array of type_id
  | Unknown_field of string * string
  | Illegal_nil
  | Illegal_break
  | Missing_value
  | Mismatched_field of string * string
  | Missing_fields of string * string list
  | Too_many_fields of string * string list

let string_of_error = function
  | Unbound_variable s -> Printf.sprintf "unknown variable `%s'" s
  | Unknown_function s -> Printf.sprintf "unknown function `%s'" s
  | Unknown_type_name s -> Printf.sprintf "unknown type name `%s'" s
  | Wrong_arity (expected, actual) -> Printf.sprintf "wrong number of arguments: expected %i, got %i" expected actual
  | Duplicate_type_name s -> Printf.sprintf "repeated type name `%s'" s
  | Not_a_statement -> "this expression should not produce a value"
  | Not_a_record _ -> "this expression does not belong to a record type"
  | Not_an_array _ -> "this expression does not belong to an array type"
  | Unknown_field (ty, s) -> Printf.sprintf "record type `%s' does not contain a field `%s'" ty s
  | Illegal_nil -> Printf.sprintf "`nil' cannot appear here"
  | Illegal_break -> Printf.sprintf "`break' cannot appear here"
  | Missing_value -> Printf.sprintf "value-producing expression was expected here"
  | Mismatched_field (ty, s) -> Printf.sprintf "a field named `%s' belonging to the type `%s' was expected here" s ty
  | Missing_fields (ty, sl) ->
      Printf.sprintf "some fields belonging to the type `%s' are missing: %s"
        ty (String.concat ", " sl)
  | Too_many_fields (ty, sl) ->
      Printf.sprintf "too many fields for type `%s': %s"
        ty (String.concat ", " sl)

exception Error of error loc

let find_var id env =
  match StringMap.find_opt id.desc env.venv with
  | Some (Var (tid, id)) -> tid, id
  | Some (Fun _) | None -> raise (Error {id with desc = Unbound_variable id.desc})

let find_fun id env =
  match StringMap.find_opt id.desc env.venv with
  | Some (Fun (sign, impl)) -> sign, impl
  | Some (Var _) | None -> raise (Error {id with desc = Unknown_function id.desc})

let find_type env id =
  match StringMap.find_opt id.desc env.tenv with
  | Some tid -> tid
  | None -> raise (Error {id with desc = Unknown_type_name id.desc})

let get_record_type env loc = function
  | Tconstr tid as ty ->
      begin match Hashtbl.find env.cstr tid with
      | Trecord fields -> tid, fields
      | Tarray _ -> raise (Error {loc; desc = Not_a_record ty})
      end
  | ty ->
      raise (Error {loc; desc = Not_a_record ty})

let get_array_type env loc = function
  | Tconstr tid as ty ->
      begin match Hashtbl.find env.cstr tid with
      | Tarray tid -> tid
      | Trecord _ -> raise (Error {loc; desc = Not_an_array ty})
      end
  | ty ->
      raise (Error {loc; desc = Not_an_array ty})

let add_var env (x : ident) tid =
  let id = Ident.create env.next_ident x.desc in
  Hashtbl.add env.vars id tid;
  {desc = Typing.Vsimple id; ty = tid}, {env with venv = StringMap.add x.desc (Var (tid, id)) env.venv}

let add_fresh_var env tid =
  let id = Ident.create env.next_ident "tmp" in
  Hashtbl.add env.vars id tid;
  {ty = tid; desc = Typing.Vsimple id}

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

let check_unique_type_name xts =
  match has_duplicate (fun (x, _) -> x.desc) xts with
  | None -> ()
  | Some (x, _) -> raise (Error {x with desc = Duplicate_type_name x.desc})

let add_types env xts =
  check_unique_type_name xts;
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
          StringMap.find name constrs
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

let add_functions _env _fdefs =
  assert false

let loc_of_variable v =
  {
    filename = v.loc.pos_fname;
    lineno = v.loc.pos_lnum;
    column = v.loc.pos_cnum - v.loc.pos_bol + 1;
  }

let rec statement env e =
  let s, e' = expression env e in
  match e' with
  | None -> s
  | Some _ -> raise (Error {e with desc = Not_a_statement})

and variable env v : statement * variable =
  match v.desc with
  | Vsimple x ->
      let tid, id = find_var x env in
      Sskip, {desc = Vsimple id; ty = tid}
  | Vsubscript (v, x) ->
      let s1, v' = variable env v in
      let t' = get_array_type env v.loc v'.ty in
      let s2, x = expression' env x Tint in
      seq s1 s2, {desc = Vsubscript (v', x); ty = t'}
  | Vfield (v, x) ->
      let s, v' = variable env v in
      let cstr, xts = get_record_type env v.loc v'.ty in
      let i, tx =
        let rec loop i = function
          | [] -> raise (Error {x with desc = Unknown_field (Ident.name cstr, x.desc)})
          | (x', t') :: _xs when x' = x.desc -> i, t'
          | _ :: xs -> loop (i+1) xs
        in
        loop 0 xts
      in
      let loc = loc_of_variable v in
      s, {desc = Vfield (loc, v', i); ty = tx}

and declarations env ds : statement * env =
  match ds with
  | [] -> Sskip, env
  | Dvar (x, xty, init) :: ds ->
      let sinit, einit =
        match xty with
        | None -> expression'' env init
        | Some sty ->
            let ty = find_type env sty in
            let s, e = expression' env init ty in
            s, e
      in
      let var, env = add_var env x einit.ty in
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
  | Dfun fdef :: ds ->
      let rec loop accu = function
        | [] -> List.rev accu, []
        | Dfun fdef :: ds -> loop (fdef :: accu) ds
        | (Dvar _ | Dtype _) :: _ as ds -> List.rev accu, ds
      in
      let fdefs, ds = loop [fdef] ds in
      declarations (add_functions env fdefs) ds

and expression' env e (ty : type_id) : statement * expression =
  match e.desc with
  | Enil ->
      let _ = get_record_type env e.loc ty in
      Sskip, {desc = Enil; ty}
  | Eseq el ->
      let rec loop = function
        | [] ->
            raise (Error {e with desc = Missing_value})
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
      seq s1 (Sifthenelse (e1, seq s2 (Sassign (v, e2)), seq s3 (Sassign (v, e3)))), {ty; desc = Evar v}
  | Elet (ds, e) ->
      let s1, env = declarations env ds in
      let s2, e = expression' env e ty in
      seq s1 s2, e
  | _ ->
      let s, e' = expression env e in
      match e' with
      | None -> raise (Error {e with desc = Missing_value})
      | Some e' ->
          let ok =
            match ty, e'.ty with
            | Tint, Tint | Tstring, Tstring -> true
            | Tconstr cstr1, Tconstr cstr2 -> Ident.equal cstr1 cstr2
            | _ -> false
          in
          if not ok then failwith "type error";
          s, e'

and expression'' env e : statement * expression =
  match expression env e with
  | s, Some e -> s, e
  | _, None -> raise (Error {e with desc = Missing_value})

and expression env e : statement * expression option =
  match e.desc with
  | Eint n ->
      Sskip, Some {ty = Tint; desc = Eint n}
  | Estring s ->
      Sskip, Some {ty = Tstring; desc = Estring s}
  | Enil ->
      raise (Error {e with desc = Illegal_nil})
  | Evar v ->
      let s, v = variable env v in
      s, Some {ty = v.ty; desc = Evar v}
  | Ebinop (e1, Op_add, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some {ty = Tint; desc = Ebinop (e1, Op_add, e2)}
  | Ebinop (e1, Op_sub, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some {ty = Tint; desc = Ebinop (e1, Op_sub, e2)}
  | Ebinop (e1, Op_mul, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some {ty = Tint; desc = Ebinop (e1, Op_mul, e2)}
  | Ebinop (e1, Op_div, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some {ty = Tint; desc = Ebinop (e1, Op_div, e2)}
  | Ebinop (e1, Op_cmp c, e2) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2 = expression' env e2 Tint in
      seq s1 s2, Some {ty = Tint; desc = Ebinop (e1, Op_cmp c, e2)}
  | Eassign (v, e) ->
      let s1, v = variable env v in
      let s2, e = expression' env e v.ty in
      seq s1 (seq s2 (Sassign (v, e))), None
  | Ecall (fn, params) ->
      let (args, res) as sign, impl = find_fun fn env in
      let num_expected = List.length args in
      let num_actual = List.length params in
      if num_expected <> num_actual then raise (Error {fn with desc = Wrong_arity (num_expected, num_actual)});
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
      let ty = find_type env ty in
      let elty = get_array_type env e.loc ty in
      let s1, size = expression' env e1 Tint in
      let s2, init = expression' env e2 elty in
      let v = add_fresh_var env ty in
      seq s1 (seq s2 (Sarray (v, size, init))), Some {ty; desc = Evar v}
  | Erecord (ty, fl) ->
      let ty = find_type env ty in
      let cstr, ftyl = get_record_type env e.loc ty in
      let rec loop (s, el) fl tyl =
        match fl, tyl with
        | [], [] ->
            s, List.rev el
        | (sname, f) :: fl, (name, ty) :: tyl ->
            if not (String.equal sname.desc name) then
              raise (Error {sname with desc = Mismatched_field (Ident.name cstr, name)});
            let s', e = expression' env f ty in
            loop (seq s s', e :: el) fl tyl
        | [], _ :: _ ->
            raise (Error {e with desc = Missing_fields (Ident.name cstr, List.map fst tyl)})
        | _ :: _, [] ->
            raise (Error {e with desc = Too_many_fields (Ident.name cstr, List.map (fun (x, _) -> x.desc) fl)})
      in
      let s, tfl = loop (Sskip, []) fl ftyl in
      let v = add_fresh_var env ty in
      seq s (Srecord (v, tfl)), Some {ty; desc = Evar v}
  | Eif (e1, e2, e3) ->
      let s1, e1 = expression' env e1 Tint in
      let s2, e2' = expression env e2 in
      let s, e =
        match e2', e3 with
        | Some _, None ->
            raise (Error {e2 with desc = Not_a_statement})
        | None, None ->
            Sifthenelse (e1, s2, Sskip), None
        | None, Some e3 ->
            Sifthenelse (e1, s2, statement env e3), None
        | Some e2, Some e3 ->
            let s3, e3 = expression' env e3 e2.ty in
            let v = add_fresh_var env e2.ty in
            Sifthenelse (e1, seq s2 (Sassign (v, e2)), seq s3 (Sassign (v, e3))),
            Some {ty = e2.ty; desc = Typing.Evar v}
      in
      seq s1 s, e
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
                 ({ty = Tint; desc = Ebinop(e2, Op_cmp Clt, {ty = Tint; desc = Evar i})},
                  Sbreak, seq s3 (Sassign (i, {ty = Tint; desc = Ebinop ({ty = Tint; desc = Evar i},
                                                                         Op_add, {ty = Tint; desc = Eint 1L})}))))
      in
      seq s1 (seq s2 (seq (Sassign (i, e1)) loop)), None
  | Ebreak ->
      if not env.loop then raise (Error {e with desc = Illegal_break});
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
