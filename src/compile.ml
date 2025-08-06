open Typing
open Irep

(* let tr_return_type env fn =
   match fn.fn_rtyp with
   | None -> void_ty
   | Some t -> find_type t env

   let fundecls = ref []

   let tr_function_header free_vars env fn =
   let rtyp = tr_return_type env fn in
   let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in
   let uid = gentmp fn.fn_name.s in
   add_fun fn.fn_name uid argst rtyp free_vars env

   let rec tr_function_body env fundef =
   let type_of_free_var x =
    match M.find x env.venv with
    | Variable _vi ->
        Tpointer
    | Function _ ->
        assert false
   in
   let fi = find_fun fundef.fn_name env in
   let ts, t = fi.fsign in
   let fvs = fi.free_vars in
   let tys1 = List.map type_of_free_var fvs in
   let env, args1 =
    List.fold_left (fun (env, args) x ->
        let vi = find_var {s = x; p = Lexing.dummy_pos} env in
        let env, x = add_var {s = x; p = Lexing.dummy_pos} vi.vtype env in
        env, x.id :: args
      ) (env, []) fvs
   in
   let args1 = List.rev args1 in
   let env, args2 =
    List.fold_left2 (fun (env, args) (x, _) t ->
        let id = fresh () in
        let env, x = add_var x t env in
        env, (id, x.id, transl_typ t) :: args
      ) (env, []) fundef.fn_args ts
   in
   let args2 = List.rev args2 in
   let tys2 = List.map transl_typ ts in
   let s = new builder in
   List.iter (fun (id1, id2, ty) ->
      s#insert_op (Ialloca ty) [||] [|id2|];
      s#insert_op Istore [|id1; id2|] [||]
    ) args2;
   let e = typ_exp {env with in_loop = false} s fundef.fn_body t in
   begin if fundef.fn_rtyp = None then
      s#insert (Ireturn false) [||] [||]
    else
      s#insert (Ireturn true) [|e s|] [||]
   end;
   let body = s#extract in
   let args2 = List.map (fun (id, _, _) -> id) args2 in
   let rty = transl_typ (tr_return_type env fundef) in
   let signature = Array.of_list (tys1 @ tys2), rty in
   fundecls := {name = fi.fname; args = Array.of_list (args1 @ args2); signature; body} :: !fundecls *)

module M = Map.Make(String)

type env =
  {
    next_reg: Reg.state;
    next_label: Label.state;
    mutable blocks: instruction Label.Map.t;
    vars: reg Ident.Map.t;
  }

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

let null env next =
  op env Pnull [] next

let rec variable env v next =
  match v with
  | Vsimple x ->
      next (reg_of_var env x)
  | Vsubscript (ty, v, i) ->
      variable env v @@ fun v ->
      expression env i @@ fun i ->
      load env Tpointer v @@ fun v ->
      op env (Pgep (type_id ty)) [v; i] next
  | Vfield (tyl, v, i) ->
      variable env v @@ fun v ->
      int env i @@ fun i ->
      int env 0 @@ fun zero ->
      load env Tpointer v @@ fun v ->
      op env (Pgep (Tstruct (Array.map type_id tyl))) [v; zero; i] next
  | Vup _ ->
      assert false

and expression env (e : expression) (next : reg -> instruction) =
  match e with
  | Eint n ->
      int64 env n next
  | Estring s ->
      op env (Imakestring s) [] next
  | Enil ->
      null env next
  | Evar (tid, v) ->
      variable env v @@ fun rv ->
      load env (type_id tid) rv next
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
      variable env v @@ fun rv ->
      expression env e @@ fun re ->
      Istore (re, rv, next)
  | Scall (None, s, el, sign) ->
      let rec loop rl = function
        | [] ->
            let r = new_reg env in
            let sign =
              let (args, res) = sign in
              Array.of_list (List.map type_id args), match res with None -> Tvoid | Some t -> type_id t
            in
            Iop (Iexternal (s, sign), List.rev rl, r, next)
        | e :: el ->
            expression env e @@ fun r -> loop (r :: rl) el
      in
      loop [] el
  | Scall (Some _, _, _, _) ->
      assert false
  | Sreturn (Some e) ->
      expression env e @@ fun r ->
      Ireturn (Some r)
  | Sreturn None ->
      Ireturn None
  | Sarray (v, size, ty, init) ->
      let kind = match ty with Tstring | Tconstr _ -> Pointer | Tint -> Int in
      expression env size @@ fun rsize ->
      expression env init @@ fun rinit ->
      variable env v @@ fun rv ->
      op env (Imakearray kind) [rsize; rinit] @@ fun rd ->
      Istore (rd, rv, next)
  | Srecord (v, tyl, fl) ->
      let n = List.length fl in
      let ty = Tstruct (Array.map type_id tyl) in
      op env (Imakerecord n) [] @@ fun rr ->
      let rec loop rl = function
        | [] ->
            variable env v @@ fun rv ->
            let _, stores =
              List.fold_left (fun (i, next) r ->
                  i+1,
                  int env (n - i - 1) @@ fun i' ->
                  int env 0 @@ fun zero ->
                  op env (Pgep ty) [rr; zero; i'] @@ fun rd ->
                  Istore (r, rd, next)
                ) (0, Istore (rr, rv, next)) rl
            in
            stores
        | e :: fl ->
            expression env e @@ fun r ->
            loop (r :: rl) fl
      in
      loop [] fl

let program (p : Typing.program) =
  let next_reg = Reg.create () in
  let vars =
    let vars = ref Ident.Map.empty in
    Hashtbl.iter (fun s _ -> vars := Ident.Map.add s (Reg.next next_reg) !vars) p.p_vars;
    !vars
  in
  let env = { next_reg; next_label = Label.create (); blocks = Label.Map.empty; vars } in
  let entrypoint =
    Hashtbl.fold (fun name tid next ->
        let root = match tid with Tconstr _ | Tstring -> true | Tint -> false in
        Iop (Ialloca (type_id tid, root), [], Ident.Map.find name vars, next)
      ) p.p_vars (statement env None p.p_body (Ireturn None))
  in
  {name = p.p_name; code = env.blocks; entrypoint}
