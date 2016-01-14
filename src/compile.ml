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
open Typedtree
(* open Llvm *)

let tmp_counter = ref (-1)

let gentmp s =
  incr tmp_counter;
  s ^ "__" ^ (string_of_int !tmp_counter)

type var_info =
  {
    vi_type: type_expr;
    vi_imm: bool;
  }

type fun_info =
  {
    fname: string;
    fsign: type_expr list * type_expr;
    f_user: bool;
  }

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type env =
  {
    venv: value_desc M.t;
    tenv: type_expr M.t;
    in_loop: bool;
  }

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

let add_var (x : pos_string) ?(immutable = false) t env =
  let vi = {vi_type = t; vi_imm = immutable} in
  {env with venv = M.add x.s (Variable vi) env.venv}

let mem_var x env =
  try match M.find x env.venv with
  | Variable _ -> true
  | Function _ -> false
  with Not_found -> false

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
  try match M.find x env.venv with
  | Function fi -> fi.f_user
  | Variable _ -> false
  with Not_found -> false

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
  { env with tenv = M.add x.s t env.tenv }

let find_array_type x env =
  match find_type x env with
  | {tdesc = ARRAY t'} as t -> t, t'
  | t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s
        (name_of_type t)

let find_record_type env x =
  match find_type x env with
  | {tdesc = RECORD xts} as t -> t, xts
  | t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s
        (name_of_type t)

let find_record_field env t (x : pos_string) =
  let xts = match t.tdesc with RECORD xts -> xts | _ -> assert false in
  (* let ts = M.find t env.renv in *)
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" (name_of_type t) x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in loop 0 xts

let declare_type env (x, t) =
  let find_type y env =
    try
      M.find y.s env.tenv
    with Not_found ->
      {tname = y.s; tdesc = DUMMY}
  in
  match t with
  | Tname y ->
      add_type x (find_type y env) env
  | Tarray y ->
      add_type x {tname = x.s; tdesc = ARRAY (find_type y env)} env
  | Trecord xs ->
      let xts = List.map (fun (x, t) -> x.s, find_type t env) xs in
      add_type x {tname = x.s; tdesc = RECORD xts} env

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

let check_type env (x, _) =
  let visited = ref [] in
  let rec loop thru_record t =
    if List.memq t !visited then begin
      if not thru_record then
        error x.p "type declaration cycle does not pass through record type"
    end else begin
      visited := t :: !visited;
      match t.tdesc with
      | VOID
      | INT
      | STRING -> ()
      | ARRAY t ->
          loop thru_record t
      | RECORD xts ->
          List.iter (fun (_, t) -> loop true t) xts
      | DUMMY ->
          begin try
              t.tdesc <- M.find t.tname
      (* | NAME y -> *)
      (*     begin try *)
      (*       loop thru_record (M.find y env.tenv) *)
      (*     with *)
      (*       Not_found -> error x.p "unbound type '%s'" y *)
      (*       (\* FIXME x.p != position of y in general *\) *)
      (*     end *)
    end
  in
  loop false (M.find x.s env.tenv)

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
  | None ->
      void_ty
  | Some t ->
      find_type t env

let tr_function_header env fn =
  let rtyp = tr_return_type env fn in
  let argst = List.map (fun (_, t) -> find_type t env) fn.fn_args in
  let uid = gentmp fn.fn_name.s in
  add_fun fn.fn_name uid argst rtyp env

let rec tr_function_body env fundef =
  let fi = find_fun fundef.fn_name env in
  let ts, t = fi.fsign in
  let env =
    List.fold_left2 (fun env (x, _) t ->
        add_var x t env
      ) env fundef.fn_args ts
  in
  let body = typ_exp {env with in_loop = false} fundef.fn_body t in
  let args = List.combine (List.map fst fundef.fn_args) ts in
  {fun_name = fundef.fn_name; fun_args = args; fun_rety = t; fun_body = body}

and let_funs env fundefs e =
  check_unique_fundef_names fundefs;
  let env' = List.fold_left tr_function_header env fundefs in
  let fundefs = List.map (tr_function_body env') fundefs in
  let e = exp env' e in
  mkexp (Tletrec (fundefs, e)) e.etype

and array_var env v =
  let v' = var env v in
  match v'.vtype.tdesc with
  | ARRAY t' ->
      v', t'
  | _ ->
      error (var_p v) "expected variable of array type, but type is '%s'"
        (name_of_type v'.vtype)

and record_var env v =
  let v' = var env v in
  match v'.vtype.tdesc with
  | RECORD _ ->
      v'
  | _ ->
      error (var_p v) "expected variable of record type, but type is '%s'"
        (name_of_type v'.vtype)

and typ_exp env e t' =
  let e' = exp env e in
  if type_equal t' e'.etype then
    e'
  else
    error (exp_p e)
      "type mismatch: expected type '%s', instead found '%s'"
      (name_of_type t') (name_of_type e'.etype)

and int_exp env e =
  typ_exp env e int_ty

and void_exp env e =
  typ_exp env e void_ty

(* Main typechecking/compiling functions *)

and var env v : Typedtree.var =
  match v with
  | Vsimple x ->
      let vi = find_var x env in
      mkvar (Tsimple x.s) vi.vi_type (* CHECK *)
      (* if vi.vimm then *)
      (*   nxt (VAL vi.v_alloca) vi.vtype *)
      (* else *)
      (*   nxt (LOADVAL vi.v_alloca) vi.vtype *)
  | Vsubscript (p, v, x) ->
      let v, t = array_var env v in
          (* let v = save (triggers x) v in *)
      let x = int_exp env x in
      mkvar (Tindex (v, x)) t
              (* let v = array_index p.Lexing.pos_lnum v x in *)
              (* nxt (load v) t')) *)
  | Vfield (p, v, x) ->
      let v = record_var env v in
      let i, tx = find_record_field env v.vtype x in
      mkvar (Tfield (v, i)) tx
(* let v = record_index p.Lexing.pos_lnum v i in *)
(* nxt (load v) tx) *)

and exp env e : Typedtree.exp =
  match e with
  | Eunit _ ->
      mkexp Tunit void_ty
  | Eint (_, n) ->
      mkexp (Tint n) int_ty
  (* | Estring (_, s) -> *)
  (*     nxt (VAL (build_global_stringptr s "" g_builder)) STRING *)
  | Enil p ->
      error p
        "'nil' should be used in a context where \
        its type can be determined"
  | Evar (_, v) ->
      let v = var env v in
      mkexp (Tvar v) v.vtype
  | Ebinop (_, x, Op_add, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      mkexp (Tbinop (x, Op_add, y)) int_ty
  | Ebinop (_, x, Op_sub, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      mkexp (Tbinop (x, Op_sub, y)) int_ty
  | Ebinop (_, x, Op_mul, y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      mkexp (Tbinop (x, Op_mul, y)) int_ty
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
  | Eassign (p, v, Enil _) ->
      let v = var env v in
      begin match v.vtype.tdesc with
        | RECORD _ ->
            mkexp (Tassign (v, mkexp Tnil v.vtype)) void_ty
        | _ ->
            error p "trying to assign 'nil' to a variable of non-record type"
      end
  | Eassign (p, v, e) ->
      let v = var env v in
      let e = typ_exp env e v.vtype in
      mkexp (Tassign (v, e)) void_ty
  | Ecall (p, x, xs) ->
      let fi = find_fun x env in
      let ts, t = fi.fsign in
      if List.length xs <> List.length ts then
        error p "bad arity: is %d, should be %d"
          (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            let actuals =
              (* if fi.f_user then *)
              (*   List.fold_right (fun x ys -> *)
              (*       let vi = find_var {s = x; p = Lexing.dummy_pos} env in *)
              (*       VAL vi.v_alloca :: ys *)
              (*     ) (S.elements (M.find x.s env.sols)) (List.rev ys) *)
              (* else *)
                List.rev ys
            in
            mkexp (Tcall (x, actuals)) t
        | Enil p :: xs, t :: ts ->
            begin match t.tdesc with
            | RECORD _ ->
                bind (mkexp Tnil t :: ys) (xs, ts)
            | _ ->
                error p "expected record type, found '%s'" (name_of_type t)
            end
        | x :: xs, t :: ts ->
            let x = typ_exp env x t in
            bind (x :: ys) (xs, ts)
        | _ ->
            assert false
      in
      bind [] (xs, ts)
  | Eseq (_, x1, x2) ->
      let e1 = exp env x1 in
      let e2 = exp env x2 in
      mkexp (Tseq (e1, e2)) e2.etype
  | Emakearray (p, x, y, Enil _) ->
      let t, t' = find_array_type x env in
      begin match t'.tdesc with
      | RECORD _ ->
          let y = int_exp env y in
          mkexp (Tmakearray (y, mkexp Tnil t')) t
      | _ ->
          error p "array base type must be record type"
      end
  | Emakearray (_, x, y, z) ->
      let t, t' = find_array_type x env in
      let y = int_exp env y in
      let z = typ_exp env z t' in
      mkexp (Tmakearray (y, z)) t
  | Emakerecord (p, x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            mkexp (Tmakerecord (List.rev vs)) t
        | (x, Enil _) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (mkexp Tnil t :: vs) (xts, ts)
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
            error p "some fields missing from initialisation"
        | _, [] ->
            error p "all fields have already been initialised"
      in
      bind [] (xts, ts)
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Eif (_, x, y, Eunit _) ->
      let x = int_exp env x in
      let y = void_exp env y in
      mkexp (Tif (x, y, mkexp Tunit void_ty)) void_ty
  | Eif (_, x, y, z) ->
      let x = int_exp env x in
      let y = exp env y in
      let z = typ_exp env z y.etype in
      mkexp (Tif (x, y, z)) y.etype
  | Ewhile (_, x, y) ->
      let x = int_exp env x in
      let y = void_exp {env with in_loop = true} y in
      mkexp (Twhile (x, y)) void_ty
  | Efor (_, i, x, y, z) ->
      let x = int_exp env x in
      let y = int_exp env y in
      let z = void_exp (add_var i ~immutable:true int_ty env) z in
      mkexp (Tfor (i, x, y, z)) void_ty
  | Ebreak p ->
      if env.in_loop then
        mkexp Tbreak void_ty (* FIXME *)
      else
        error p "illegal use of 'break'"
  | Elet (_, Dvar (x, None, y), z) ->
      let y = exp env y in
      let env = add_var x y.etype env in
      let z = exp env z in
      mkexp (Tlet (x, y, z)) z.etype
  | Elet (p, Dvar (x, Some t, Enil _), z) ->
      let t = find_type t env in
      begin match t.tdesc with
      | RECORD _ ->
          let env = add_var x t env in
          let z = exp env z in
          mkexp (Tlet (x, mkexp Tnil t, z)) z.etype
      | _ ->
          error p "expected record type, found '%s'" (name_of_type t)
      end
  | Elet (_, Dvar (x, Some t, y), z) ->
      let ty = find_type t env in
      let y = typ_exp env y ty in
      let env = add_var x ty env in
      let z = exp env z in
      mkexp (Tlet (x, y, z)) z.etype
  | Elet (_, Dtypes tys, e) ->
      let env = let_type env tys in
      exp env e
  | Elet (_, Dfuns funs, e) ->
      let_funs env funs e

let base_tenv =
  M.add "int" int_ty (M.add "string" string_ty M.empty)

let base_venv env =
  env
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

let program e = e
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
