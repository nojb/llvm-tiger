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
  | ANY
  | VOID
  | INT
  | STRING
  | ARRAY of type_expr
  | RECORD of (string * type_expr) list
  | DUMMY

and type_expr =
  { mutable tdesc: type_desc ref;
    tname: string }

let void_ty = {tdesc = ref VOID; tname = "void"}
let int_ty = {tdesc = ref INT; tname = "int"}
let string_ty = {tdesc = ref STRING; tname = "string"}
let any_ty = {tdesc = ref ANY; tname = "<any>"}

type var_info =
  { id: int;
    vtype : type_expr;
    vimm : bool }

type fun_info =
  { fname: string;
    fsign: type_expr list * type_expr;
    f_user: bool;
    free_vars: string list }

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type env =
  { venv: value_desc M.t;
    tenv: type_expr M.t;
    in_loop: bool }

(* let rec base_type env ty = *)
(*   match ty.tdesc with *)
(*   | NAME x -> base_type env (M.find x env.tenv) *)
(*   | _ as t -> t *)

let type_equal (* env *) t1 t2 =
  t1.tdesc == t2.tdesc (* FIXME *)
(* t1.tdesc == ANY || t2.tdesc == ANY || base_type env t1 == base_type env t2 *)

let empty_env =
  { venv = M.empty;
    tenv = M.empty;
    in_loop = false }

let find_var id env =
  try
    match M.find id.s env.venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with Not_found ->
    error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?(immutable = false) t env =
  let vi = {id = fresh (); vtype = t; vimm = immutable} in
  {env with venv = M.add x.s (Variable vi) env.venv}, vi

let mem_var x env =
  try
    match M.find x env.venv with
    | Variable _ -> true
    | Function _ -> false
  with Not_found ->
    false

let add_fun x uid atyps rtyp free_vars env =
  let fi =
    { fname = uid; fsign = atyps, rtyp;
      f_user = true; free_vars }
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
  match find_type x env with
  | {tdesc = {contents = ARRAY t'}; _} as t -> t, t'
  | _ as t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s t.tname

let find_record_type env x =
  match find_type x env with
  | {tdesc = {contents = RECORD xts}; _} as t -> t, xts
  | _ as t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s t.tname

let find_record_field _env t (x : pos_string) =
  let xts = match !(t.tdesc) with RECORD xts -> xts | _ -> assert false in
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t.tname x.s
    | (x', t') :: _xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in
  loop 0 xts

let transl_typ t =
  let rec loop t =
    match !(t.tdesc) with
    | ANY -> assert false
    | VOID -> Tvoid
    | INT -> Tint 32
    | STRING -> Tpointer (Tint 8)
    | ARRAY t -> (* { i32, [0 x t] }* *)
        Tpointer (loop t) (*  (Tstruct [Tint 32; Tarray (loop t, 0)]) *)
    | RECORD _ ->
        Tpointer (Tnamed t.tname) (* FIXME record the fields *)
    (* if not (List.mem_assq t !named_structs) then begin *)
    (*   let ty = named_struct_type g_context x in *)
    (*   named_structs := (t, ty) :: !named_structs; *)
    (*   struct_set_body ty *)
    (*     (Array.of_list (List.map (fun (_, t) -> loop t) xts)) *)
    (*     false *)
    (* end; *)
    (* pointer_type (List.assq t !named_structs) *)
    | DUMMY ->
        assert false
  in
  loop t

let declare_types env xts =
  let env =
    List.fold_left (fun env (x, _t) ->
        add_type x {tdesc = ref DUMMY; tname = x.s} env
      ) env xts
  in
  List.iter (fun (x, t) ->
      let tx = find_type x env in
      match t with
      | Tname y ->
          let ty = find_type y env in
          tx.tdesc <- ty.tdesc
      | Tarray y ->
          tx.tdesc := ARRAY (find_type y env)
      | Trecord xs ->
          tx.tdesc := RECORD (List.map (fun (x, t) -> x.s, find_type t env) xs)
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

(* let check_type env (x, _) = *)
(*   let visited = ref [] in *)
(*   let rec loop thru_record t = *)
(*     if List.memq t !visited then *)
(*       if not thru_record then *)
(*         error x.p "type declaration cycle does not pass through record type" *)
(*     else begin *)
(*       visited := t :: !visited; *)
(*       match t with *)
(*       | VOID *)
(*       | INT *)
(*       | STRING -> () *)
(*       | ARRAY t -> *)
(*           loop thru_record t *)
(*       | RECORD (_, xts) -> *)
(*           List.iter (fun (_, t) -> loop true t) xts *)
(*       | NAME y -> *)
(*           begin try *)
(*             loop thru_record (M.find y env.tenv) *)
(*           with *)
(*             Not_found -> error x.p "unbound type '%s'" y *)
(*             (\* FIXME x.p != position of y in general *\) *)
(*           end *)
(*     end *)
(*   in *)
(*   loop false (M.find x.s env.tenv) *)

let let_type env tys =
  check_unique_type_names tys;
  declare_types env tys
(* let env = List.fold_left declare_type env tys in *)
(* (\* List.iter (check_type env) tys; *\) *)
(* env *)

(* let rec structured_type env t = *)
(*   match t with *)
(*   | NAME y -> structured_type env (M.find y env.tenv) *)
(*   | STRING *)
(*   | ARRAY _ *)
(*   | RECORD _ -> true *)
(*   | _ -> false *)

module C = struct
  let var id _ = id
  let op p args s =
    let args = List.map (fun arg -> arg s) args in
    let id = fresh () in
    s#insert_op p (Array.of_list args) [|id|];
    id
  let constint n = op (Pconstint n) []
  let addint c1 c2 = op Paddint [c1; c2]
  let subint c1 c2 = op Psubint [c1; c2]
  let mulint c1 c2 = op Pmulint [c1; c2]
  let divint c1 c2 = op Pdivint [c1; c2]
  let load ty c = op (Pload ty) [c]
  let gep v args = op Pgep (v :: args)
  let null _t _s = assert false
  let compint cmp c1 c2 = op (Pcmpint cmp) [c1; c2]
end

class builder =
  object (s)
    val mutable instr_seq = dummy_instr

    method extract =
      let rec aux i next =
        if i == dummy_instr then
          next
        else
          aux i.next {i with next}
      in
      aux instr_seq (end_instr ())

    method insert desc arg res =
      instr_seq <- {desc; arg; res; next = instr_seq}

    method insert_op op arg res =
      s#insert (Iop op) arg res
  end

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
    | Variable vi ->
        Tpointer (transl_typ vi.vtype)
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
  fundecls := {name = fi.fname; args = Array.of_list (args1 @ args2); signature; body} :: !fundecls

and let_funs env fundefs =
  check_unique_fundef_names fundefs;
  let free_vars =
    List.fold_left
      (fun s f ->
         let ffv =
           List.fold_left (fun s (x, _) -> S.remove x.s s) (fv f.fn_body) f.fn_args
         in
         S.union ffv s
      ) S.empty fundefs
  in
  let free_vars = S.elements free_vars in
  let env = List.fold_left (tr_function_header free_vars) env fundefs in
  List.iter (tr_function_body env) fundefs;
  env

and array_var env s v =
  let t, v' = var env s v in
  match t with
  | {tdesc = {contents = ARRAY t'}; _} -> t', v'
  | _ ->
      error v.vpos "expected variable of array type, but type is '%s'" t.tname

and record_var env s v =
  let t, v' = var env s v in
  match t with
  | {tdesc = {contents = RECORD _}; _} -> t, v'
  | _ ->
      error v.vpos "expected variable of record type, but type is '%s'" t.tname

and typ_exp env s e t' =
  let t, e' = exp env s e in
  if type_equal t t' then e'
  else
    error e.epos
      "type mismatch: expected type '%s', instead found '%s'" t'.tname t.tname

and int_exp env s e =
  typ_exp env s e int_ty

and void_exp env s e =
  let _f = typ_exp env s e void_ty in
  ()

and var env s v =
  match v.vdesc with
  | Vsimple x ->
      let vi = find_var x env in
      vi.vtype, C.var vi.id
  | Vsubscript (v, x) ->
      let t', v = array_var env s v in
      let x = int_exp env s x in
      t', C.gep (C.load (transl_typ t') v) [x]
  | Vfield (v, x) ->
      let t', v = record_var env s v in
      let i, tx = find_record_field env t' x in
      tx, C.gep (C.load (transl_typ t') v) [C.constint 0l; C.constint (Int32.of_int i)]

and exp env s e =
  match e.edesc with
  | Eunit ->
      void_ty, C.constint 0l
  | Eint n ->
      int_ty, C.constint n
  | Estring _s ->
      failwith "Estring not implemented"
  (* nxt (VAL (build_global_stringptr s "" g_builder)) STRING *)
  | Enil ->
      error e.epos
        "'nil' should be used in a context where \
         its type can be determined"
  | Evar v ->
      let t, v = var env s v in
      t, C.load (transl_typ t) v
  | Ebinop (x, Op_add, y) ->
      let x = int_exp env s x in
      let y = int_exp env s y in
      int_ty, C.addint x y
  | Ebinop (x, Op_sub, y) ->
      let x = int_exp env s x in
      let y = int_exp env s y in
      int_ty, C.subint x y
  | Ebinop (x, Op_mul, y) ->
      let x = int_exp env s x in
      let y = int_exp env s y in
      int_ty, C.mulint x y
  | Ebinop (x, Op_div, y) ->
      let x = int_exp env s x in
      let y = int_exp env s y in
      int_ty, C.divint x y
  | Ebinop _ ->
      failwith "not implemented"
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
  | Eassign (v, {edesc = Enil; _}) ->
      let t, v = var env s v in
      begin match t with
      | {tdesc = {contents = RECORD _}; _} ->
          s#insert_op Istore [|C.constint 0l s; v s|] [||];
          void_ty, C.constint 0l
      | _ ->
          error e.epos "trying to assign 'nil' to a field of non-record type"
      end
  | Eassign (v, e) ->
      let t, v = var env s v in
      let e = typ_exp env s e t in
      s#insert_op Istore [|e s; v s|] [||];
      void_ty, C.constint 0l
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
                    C.var vi.id :: ys
                  ) fi.free_vars (List.rev ys)
              else
                List.rev ys
            in
            let id = fresh () in
            if fi.f_user then begin
              s#insert_op (Iapply fi.fname) (Array.of_list (List.map (fun arg -> arg s) actuals)) [|id|]
            end else begin
              let sg = Array.of_list (List.map transl_typ (fst fi.fsign)), transl_typ (snd fi.fsign) in
              s#insert_op (Iexternal (fi.fname, sg)) (Array.of_list (List.map (fun arg -> arg s) actuals)) [|id|]
            end;
            t, C.var id
        | {edesc = Enil; epos = p} :: xs, t :: ts ->
            begin match t with
            | {tdesc = {contents = RECORD _}; _} ->
                bind (C.null (transl_typ t) :: ys) (xs, ts)
            | _ ->
                error p "expected record type, found '%s'" t.tname
            end
        | x :: xs, t :: ts ->
            let x = typ_exp env s x t in
            bind (x :: ys) (xs, ts)
        | _ ->
            assert false
      in
      bind [] (xs, ts)
  | Eseq (e1, e2) ->
      let _ = exp env s e1 in
      exp env s e2
  | Emakearray (x, y, {edesc = Enil; _}) ->
      let t, t' = find_array_type x env in
      begin match t' with
      | {tdesc = {contents = RECORD _}; _} ->
          let y = int_exp env s y in
          let id1 = fresh () in
          let id2 = fresh () in
          let sg = [|Tint 32; transl_typ t'|], transl_typ t in
          s#insert_op (Ialloca (transl_typ t)) [||] [|id2|];
          s#insert_op (Iexternal ("tiger_make_array", sg)) [|y s; C.null (transl_typ t') s|] [|id1|];
          s#insert_op Istore [|id1; id2|] [||];
          t, C.load (transl_typ t) (C.var id2)
      | _ ->
          error e.epos "array base type must be record type"
      end
  | Emakearray (x, y, z) ->
      let t, t' = find_array_type x env in
      let y = int_exp env s y in
      let z = typ_exp env s z t' in
      let id1 = fresh () in
      let id2 = fresh () in
      let sg = [|Tint 32; transl_typ t'|], transl_typ t in
      s#insert_op (Ialloca (transl_typ t)) [||] [|id2|];
      s#insert_op (Iexternal ("tiger_make_array", sg)) [|y s; z s|] [|id1|];
      s#insert_op Istore [|id1; id2|] [||];
      t, C.load (transl_typ t) (C.var id2)
  | Emakerecord (x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            let id1 = fresh () in
            let id2 = fresh () in
            s#insert_op (Ialloca (transl_typ t)) [||] [|id2|];
            s#insert_op (Iexternal ("tiger_make_record", assert false)) [||] [|id1|]; (* FIXME *)
            s#insert_op Istore [|id1; id2|] [||];
            let f i = C.gep (C.var id2) [C.constint 0l; C.constint (Int32.of_int i)] in
            let rec bind i = function
              | [] -> t, C.load (transl_typ t) (C.var id2)
              | v :: vs ->
                  s#insert_op Istore [|v s; f i s|] [||];
                  bind (i+1) vs
            in
            bind 0 (List.rev vs)
        | (x, {edesc = Enil; _}) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (C.null (transl_typ t) :: vs) (xts, ts)
            else
            if List.exists (fun (x', _) -> x.s = x') ts then
              error x.p "field '%s' is in the wrong other" x.s
            else
              error x.p "field '%s' is unknown" x.s
        | (x, e) :: xts, (x', t) :: ts ->
            if x.s = x' then
              let e = typ_exp env s e t in
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
      let e1 = int_exp env s e1 in
      let id = fresh () in
      let s2 = new builder in
      let t2, e2 = exp env s2 e2 in
      s2#insert_op Istore [|e2 s2; id|] [||];
      let s3 = new builder in
      let e3 = typ_exp env s3 e3 t2 in
      s3#insert_op Istore [|e3 s3; id|] [||];
      s#insert (Iifthenelse (s2#extract, s3#extract)) [|e1 s|] [||];
      t2, C.load (transl_typ t2) (C.var id)
  | Ewhile (e1, e2) ->
      let s2 = new builder in
      void_exp env s2 e2;
      let s3 = new builder in
      s3#insert (Iexit 0) [||] [||];
      let sbody = new builder in
      sbody#insert (Iifthenelse (s2#extract, s3#extract)) [|int_exp env sbody e1 sbody|] [||];
      let scatch = new builder in
      scatch#insert (Iloop (sbody#extract)) [||] [||];
      s#insert (Icatch (scatch#extract)) [||] [||];
      void_ty, C.constint 0l
  | Efor (i, x, y, z) ->
      let x = int_exp env s x in
      let y = int_exp env s y in
      let env, i = add_var i ~immutable:true int_ty env in
      s#insert_op (Ialloca (Tint 32)) [||] [|i.id|];
      s#insert_op Istore [|x s; i.id|] [||];
      let sbody = new builder in
      void_exp env sbody z;
      sbody#insert_op Istore [|C.addint (C.constint 1l) (C.load (Tint 32) (C.var i.id)) sbody; i.id|] [||];
      let sexit = new builder in
      sexit#insert (Iexit 0) [||] [||];
      let stest = new builder in
      let cond = C.compint Cleq (C.load (Tint 32) (C.var i.id)) y stest in
      stest#insert (Iifthenelse (sbody#extract, sexit#extract)) [|cond|] [||];
      let scatch = new builder in
      scatch#insert (Iloop (stest#extract)) [||] [||];
      s#insert (Icatch (scatch#extract)) [||] [||];
      void_ty, C.constint 0l
  | Ebreak ->
      if env.in_loop then begin
        s#insert (Iexit 0) [||] [||];
        any_ty, C.constint 0l
      end else
        error e.epos "illegal use of 'break'"
  | Elet (Dvar (x, None, y), z) ->
      let ty, y = exp env s y in
      let env, x = add_var x ty env in
      s#insert_op (Ialloca (transl_typ ty)) [||] [|x.id|];
      s#insert_op Istore [|y s; x.id|] [||];
      exp env s z
  | Elet (Dvar (x, Some t, {edesc = Enil; _}), z) ->
      let t = find_type t env in
      begin match t with
      | {tdesc = {contents = RECORD _}; _} ->
          let env, x = add_var x t env in
          s#insert_op (Ialloca (transl_typ t)) [||] [|x.id|];
          s#insert_op Istore [|C.null (transl_typ t) s; x.id|] [||];
          exp env s z
      | _ ->
          error e.epos "expected record type, found '%s'" t.tname
      end
  | Elet (Dvar (x, Some t, y), z) ->
      let ty = find_type t env in
      let y = typ_exp env s y ty in
      let env, x = add_var x ty env in
      s#insert_op (Ialloca (transl_typ ty)) [||] [|x.id|];
      s#insert_op Istore [|y s; x.id|] [||];
      exp env s z
  | Elet (Dtypes tys, e) ->
      let env = let_type env tys in
      exp env s e
  | Elet (Dfuns funs, e) ->
      exp (let_funs env funs) s e

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
    M.add x (Function {fname = fname; f_user = false; fsign = (ts, t); free_vars = []}) venv
  in
  List.fold_left decl_fun M.empty stdlib

let program e =
  fundecls := [];
  let env = {tenv = base_tenv; venv = base_venv; in_loop = false} in
  let s = new builder in
  let _ = exp env s e in
  s#insert (Ireturn true) [|C.constint 0l s|] [||];
  let body = s#extract in
  {name = "__tiger_main"; args = [||]; signature = ([||], Tint 32); body} :: !fundecls
