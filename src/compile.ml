open Typing
open Irep

type env =
  {
    cstrs: type_structure Typing.Ident.Map.t;
    next_reg: Reg.state;
    next_label: Label.state;
    mutable blocks: instruction Label.Map.t;
    vars: reg Ident.Map.t;
  }

let type_structure env tid =
  Ident.Map.find tid env.cstrs

let reg_of_var env id =
  Ident.Map.find id env.vars

let new_reg env =
  Reg.next env.next_reg

let new_label env =
  Label.next env.next_label

let set_label env lbl i =
  env.blocks <- Label.Map.add lbl i env.blocks

let label_instr env i =
  let lbl = new_label env in
  env.blocks <- Label.Map.add lbl i env.blocks;
  lbl

let type_id : type_id -> ty = function
  | Tint -> Tint 64
  | Tstring | Tconstr _ -> Tpointer

let type_structure env : type_id -> ty = function
  | Tint | Tstring -> assert false
  | Tconstr cstr ->
      Tstruct (
        match type_structure env cstr with
        | Tarray tid -> [Tint 64; Tarray (type_id tid, 0)]
        | Trecord l -> List.map (fun (_, tid) -> type_id tid) l
      )

let load env ty r next =
  let r' = new_reg env in
  Iload (ty, r, r', next r')

let op env op args next =
  let r = new_reg env in
  Iop(op, args, r, next r)

let int64 env n next =
  op env (Pconstint n) [] next

let int env n next =
  int64 env (Int64.of_int n) next

let string env s next =
  op env (Pconststring s) [] next

let null env next =
  op env Pnull [] next

let nil_error env loc =
  string env loc.filename @@ fun filename ->
  int env loc.lineno @@ fun lineno ->
  int env loc.column @@ fun column ->
  op env
    (Iexternal ("TIG_nil_error", ([Tpointer; Tint 64; Tint 64], Tvoid)))
    [filename; lineno; column] (fun _ -> Iunreachable)

let null_check env loc v next =
  let lnext = label_instr env next in
  let lnull = label_instr env (nil_error env loc) in
  null env @@ fun z ->
  op env (Pcmpint Ceq) [v; z] @@ fun c ->
  Iifthenelse (c, lnull, lnext)

let bounds_error env loc =
  string env loc.filename @@ fun filename ->
  int env loc.lineno @@ fun lineno ->
  int env loc.column @@ fun column ->
  op env
    (Iexternal ("TIG_bounds_error", ([Tpointer; Tint 64; Tint 64], Tvoid)))
    [filename; lineno; column] (fun _ -> Iunreachable)

let bounds_check env loc ty v' i' next =
  let lnext = label_instr env next in
  let louts = label_instr env (bounds_error env loc) in
  int env 0 @@ fun z' ->
  op env (Pgep ty) [v'; z'; z'] @@ fun n' ->
  load env (Tint 64) n' @@ fun n' ->
  op env (Pcmpint Cge) [i'; z'] @@ fun c1' ->
  op env (Pcmpint Clt) [i'; n'] @@ fun c2' ->
  op env Pand [c1'; c2'] @@ fun c' ->
  Iifthenelse (c', lnext, louts)

let rec variable env v next =
  match v.desc with
  | Vsimple x ->
      next (reg_of_var env x)
  | Vsubscript (loc, v, i) ->
      variable env v @@ fun v' ->
      expression env i @@ fun i' ->
      load env Tpointer v' @@ fun v' ->
      let ty = type_structure env v.ty in
      bounds_check env loc ty v' i' @@
      int env 0 @@ fun zero' ->
      int env 1 @@ fun one' ->
      op env (Pgep ty) [v'; zero'; one'; i'] next
  | Vfield (loc, v, i) ->
      variable env v @@ fun v' ->
      int env i @@ fun i' ->
      int env 0 @@ fun zero' ->
      load env Tpointer v' @@ fun v' ->
      null_check env loc v' @@
      op env (Pgep (type_structure env v.ty)) [v'; zero'; i'] next

and expression env (e : expression) (next : reg -> instruction) =
  match e.desc with
  | Eint n ->
      int64 env n next
  | Estring s ->
      string env s next
  | Enil ->
      null env next
  | Evar v ->
      variable env v @@ fun v' ->
      load env (type_id v.ty) v' next
  | Ebinop (e1, Op_add, e2) ->
      expression env e1 @@ fun r1 ->
      expression env e2 @@ fun r2 ->
      op env Paddint [r1; r2] next
  | Ebinop (e1, Op_sub, e2) ->
      expression env e1 @@ fun r1 ->
      expression env e2 @@ fun r2 ->
      op env Psubint [r1; r2] next
  | Ebinop (e1, Op_mul, e2) ->
      expression env e1 @@ fun r1 ->
      expression env e2 @@ fun r2 ->
      op env Pmulint [r1; r2] next
  | Ebinop (e1, Op_div, e2) ->
      expression env e1 @@ fun r1 ->
      expression env e2 @@ fun r2 ->
      op env Pdivint[r1; r2] next
  | Ebinop (e1, Op_cmp c, e2) ->
      expression env e1 @@ fun r1 ->
      expression env e2 @@ fun r2 ->
      op env (Pcmpint c) [r1; r2] @@ fun rd ->
      op env Pzext [rd] next

and statement env lexit s next =
  match s with
  | Sskip ->
      next
  | Sloop body ->
      let lnext = label_instr env next in
      let lbody = new_label env in
      set_label env lbody (statement env (Some lnext) body (Igoto lbody));
      Igoto lbody
  | Sbreak ->
      Igoto (Option.get lexit)
  | Sifthenelse (e1, s2, s3) ->
      let lnext = label_instr env next in
      let lyes = label_instr env (statement env lexit s2 (Igoto lnext)) in
      let lnay = label_instr env (statement env lexit s3 (Igoto lnext)) in
      expression env e1 @@ fun r1 ->
      int env 0 @@ fun r2 ->
      op env (Pcmpint Tabs.Cne) [r1; r2] @@ fun r ->
      Iifthenelse (r, lyes, lnay)
  | Sseq (s1, s2) ->
      statement env lexit s1 (statement env lexit s2 next)
  | Sassign (v, e) ->
      variable env v @@ fun v' ->
      expression env e @@ fun e' ->
      Istore (e', v', next)
  | Scall (v, impl, el, sg) ->
      let rec loop rl = function
        | e :: el ->
            expression env e @@ fun r -> loop (r :: rl) el
        | [] ->
            let r = new_reg env in
            let next =
              match v with
              | None -> next
              | Some v -> variable env v @@ fun v' -> Istore (r, v', next)
            in
            let op =
              match impl with
              | External s ->
                  let sg =
                    let (args, res) = sg in
                    List.map type_id args, match res with None -> Tvoid | Some t -> type_id t
                  in
                  Iexternal (s, sg)
              | Internal id -> Icall id
            in
            Iop (op, List.rev rl, r, next)
      in
      loop [] el
  | Sreturn (Some e) ->
      expression env e @@ fun r ->
      Ireturn (Some r)
  | Sreturn None ->
      Ireturn None
  | Sarray (v, size, init) ->
      expression env size @@ fun rsize ->
      expression env init @@ fun rinit ->
      variable env v @@ fun rv ->
      op env Imakearray [rsize; rinit] @@ fun rd ->
      Istore (rd, rv, next)
  | Srecord (v, fl) ->
      let n = List.length fl in
      let ty = type_structure env v.ty in
      op env (Imakerecord n) [] @@ fun rr ->
      let rec loop rl = function
        | [] ->
            variable env v @@ fun v' ->
            let _, stores =
              List.fold_left (fun (i, next) r ->
                  i+1,
                  int env (n - i - 1) @@ fun i' ->
                  int env 0 @@ fun zero' ->
                  op env (Pgep ty) [rr; zero'; i'] @@ fun rd ->
                  Istore (r, rd, next)
                ) (0, Istore (rr, v', next)) rl
            in
            stores
        | e :: fl ->
            expression env e @@ fun r ->
            loop (r :: rl) fl
      in
      loop [] fl

let fundef cstrs fundef =
  let next_reg = Reg.create () in
  let vars =
    let vars = ref Ident.Map.empty in
    List.iter (fun (s, _) -> vars := Ident.Map.add s (Reg.next next_reg) !vars) fundef.fn_args;
    List.iter (fun (s, _) -> vars := Ident.Map.add s (Reg.next next_reg) !vars) fundef.fn_vars;
    !vars
  in
  let env = { cstrs; next_reg; next_label = Label.create (); blocks = Label.Map.empty; vars } in
  let entrypoint = statement env None fundef.fn_body (Ireturn None) in
  let entrypoint =
    List.fold_left (fun next (name, tid) ->
        let root = match tid with Tconstr _ | Tstring -> true | Tint -> false in
        Iop (Ialloca (type_id tid, root), [], Ident.Map.find name vars, next)
      ) entrypoint fundef.fn_vars
  in
  let _, entrypoint =
    List.fold_left (fun (i, next) (name, tid) ->
        let root = match tid with Tconstr _ | Tstring -> true | Tint -> false in
        let r = Reg.next next_reg in
        let next = Iop (Pparam i, [], r, Istore (r, Ident.Map.find name vars, next)) in
        i+1, Iop (Ialloca (type_id tid, root), [], Ident.Map.find name vars, next)
      ) (0, entrypoint) fundef.fn_args
  in
  let signature =
    List.map (fun (_, ty) -> type_id ty) fundef.fn_args,
    match fundef.fn_rtyp with
    | None -> Tvoid
    | Some ty -> type_id ty
  in
  { name = fundef.fn_name; signature; code = env.blocks; entrypoint }

let program (p : Typing.program) =
  let cstrs = Ident.Map.of_list p.p_cstr in
  let funs = List.map (fundef cstrs) p.p_funs in
  { funs }
