open Globals
open Parsetree
open Typedtree

exception Error of Lexing.position * string

let error p =
  Printf.ksprintf (fun message -> raise (Error (p, message)))

let debug () =
  Printf.ksprintf (fun message -> Printf.fprintf stderr "DEBUG: %s\n%!" message)

(* type type_spec =
  | VOID
  | INT
  | STRING
  | ARRAY   of string * type_spec
  | RECORD  of string * Id.t (* name, unique name *)
  | PLACE   of string *)

let rec string_of_type = function
  | VOID -> "void"
  | INT -> "int"
  | STRING -> "string"
  | ARRAY (id, t) -> id ^ " = array of " ^ string_of_type t
  | RECORD (id, _) -> id ^ " = record"
  | PLACE _ -> assert false

let describe_type = function
  | VOID -> "void"
  | INT -> "int"
  | STRING -> "string"
  | ARRAY _ -> "array"
  | RECORD _ -> "record"
  | PLACE _ -> assert false

let type_equal t1 t2 =
  t1 == t2

type var_info = {
  vtype : type_spec;
  vaccess : access ref;
  vlevel : int;
  vimm : bool
}

type fun_impl =
  | Internal
  | External

type fun_info = {
  fname : string;
  fsign : type_spec list * type_spec;
  fimpl : fun_impl
}

type value_desc =
  | Variable of var_info
  | Function of fun_info

module M = Map.Make (String)

type env = {
  venv : value_desc M.t;
  tenv : type_spec M.t;
  renv : (string * type_spec) list M.t;
  in_loop : bool;
  lvl : int;
  fp : int ref list
}

let find_var id env =
  try
    match M.find id.s env.venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with
    Not_found ->
      error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?immutable:(immut=false) t lvl acc env =
  let vi = {
    vtype = t; vlevel = lvl;
    vaccess = acc; vimm = immut }
  in
  { env with venv = M.add x.s (Variable vi) env.venv }

let add_fun x atyps rtyp env =
  let fi = {
    fname = Id.to_string (Id.make x.s);
    fsign = atyps, rtyp;
    fimpl = Internal
  } in
  { env with venv = M.add x.s (Function fi) env.venv }

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
  | ARRAY (_, t') as t -> t, t'
  | _ as t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s
        (describe_type t)

let find_record_type env x =
  match find_type x env with
  | RECORD (ts, _) as t -> t, M.find ts env.renv
  | _ as t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s
        (describe_type t)

let find_record_field env t (x : pos_string) =
  assert false
  (* let ts = M.find t env.renv in
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in loop 0 ts *)

(* let named_structs : (string * llvm_type list) list ref = ref []

let rec transl_typ env t =
  let visited : string list ref = ref [] in
  let rec loop t =
    match t with
    | INT -> Tint 32
    | VOID -> Tint 32
    | STRING -> Tpointer (Tint 8)
    | ARRAY (_, t) -> (* { i32, i32, [0 x t] }* *)
        Tpointer (Tstruct [| Tint 32; Tint 32; Tarray (0, transl_typ env t) |])
    | RECORD (rname, uid) ->
        if not (List.exists (fun (x, _) -> x = Id.to_string uid) !named_structs)
        && not (List.mem (Id.to_string uid) !visited)
        then begin
          visited := (Id.to_string uid) :: !visited;
          named_structs := (Id.to_string uid,
            (Tint 32 :: List.map (fun (_, t) -> loop t) (M.find rname env.renv))) :: !named_structs
        end;
        Tpointer (Tnamedstruct (Id.to_string uid))
    | PLACE _ ->
        assert false
  in loop t *)

let declare_type env (x, t) =
  let find_type y env =
    try M.find y.s env.tenv
    with Not_found -> PLACE y.s in
  match t with
  | PTname y ->
      add_type x (find_type y env) env
  | PTarray y ->
      add_type x (ARRAY (x.s, find_type y env)) env
  | PTrecord xs ->
      add_type x (RECORD (x.s, Id.make x.s)) env

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

let define_type env (x, _) =
  let visited = ref [] in
  let rec loop y =
    if List.mem y !visited then
      error x.p "type declaration cycle does not pass through record type"
    visited := y :: !visited;
    try
      let t = M.find y env.tenv in
      match t with
      | PLACE y -> loop y
      | ARRAY (x, PLACE y') -> ARRAY (x, loop y')
      | _ -> t
    with Not_found ->
      error x.p "unbound type '%s'" y
        (* FIXME x.p != position of y in general *)
  in add_type x (loop x.s) env

let extract_record_type env (x, t) =
  match t with
  | PTrecord (xts) ->
      { env with renv =
          M.add x.s (List.map (fun (x, t) -> (x.s, find_type t env)) xts) env.renv }
  | _ ->
      env

let let_type env tys =
  check_unique_type_names tys;
  let env = List.fold_left declare_type env tys in
  let env = List.fold_left define_type env tys in
  let env = List.fold_left extract_record_type env tys in
  env

(** ----------------------------------------- *)

let rec structured_type t =
  match t with
  | PLACE _ -> assert false
  | STRING
  | ARRAY _
  | RECORD _ -> true
  | _ -> false

let array_exists p a =
  let rec loop i =
    if i >= Array.length a then false
    else if p a.(i) then true
    else loop (i+1)
  in loop 0

(* These utility functions are used in the processing of function definitions *)

let rec array_var env v =
  let v', t = var env v in
    match t with
    | ARRAY (_, t') -> v', t'
    | _ ->
        error (var_p v) "expected variable of array type, but type is '%s'"
          (describe_type t)

and record_var env v =
  let v', t = var env v in
    match t with
    | RECORD (t', _) -> v', t
    | _ ->
        error (var_p v) "expected variable of record type, but type is '%s'"
          (describe_type t)

and typ_exp env e t' =
  let e', t = exp env e in
    if type_equal t t' then e'
    else error (exp_p e)
      "type mismatch: expected type '%s', instead found '%s'"
        (string_of_type t') (string_of_type t)

and int_exp env e =
  typ_exp env e INT

and void_exp env e =
  typ_exp env e VOID

(* Main typechecking/compiling functions *)

and var env v : Typedtree.var * type_spec =
  match v with
  | PVsimple x ->
      let vi = find_var x env in
      let dlvl = env.lvl - vi.vlevel in
      begin match !(vi.vaccess) with
      | Local ->
          debug () "dlvl for %s = %d" x.s dlvl;
          if dlvl > 0 then
            let fpr = List.nth env.fp dlvl in
            let fp = !fpr in
            incr fpr;
            vi.vaccess := NonLocal fp;
            TVnonLocal (dlvl, fp), vi.vtype
          else
            TVlocal x.s, vi.vtype
      | NonLocal (fp) ->
          TVnonLocal (dlvl, fp), vi.vtype
      end
  | PVsubscript (p, v, x) ->
      let v, t' = array_var env v in
      let x = int_exp env x in
      TVsubscript (p.Lexing.pos_lnum, v, x), t'
  | PVfield (p, v, x) -> (* should check for nil XXX *)
      let v, t' = record_var env v in
      let i, tx = find_record_field env t' x in
      TVfield (p.Lexing.pos_lnum, v, i), tx

and exp env e =
  match e with
  | Pint (_, n) ->
      TCint n, INT
  | Pstring (_, s) ->
      TCstring s, STRING
  | Pnil p ->
      error p
        "'nil' should be used in a context where \
        its type can be determined"
  | Pvar (_, v) ->
      let v, t = var env v in
      Tvar v, t
  | Pbinop (_, x, (Op_add as op), y)
  | Pbinop (_, x, (Op_sub as op), y)
  | Pbinop (_, x, (Op_mul as op), y)
  | Pbinop (_, x, (Op_div as op), y)
  | Pbinop (_, x, (Op_and as op), y)
  | Pbinop (_, x, (Op_cmp Ceq as op), y) ->
      let x = int_exp env x in
      let y = int_exp env y in
      Tbinop (x, op, y), INT
  | Pbinop _ ->
      failwith "binop not implemented"
  (* | Passign (p, PVsimple x, Pnil _) ->
      let x, t, immut = find_var x venv in
      begin match t with
      | RECORD _ ->
          Tassign (TVsimple (x, ref Local), Tnil t), VOID
      | _ ->
          error p "trying to assign 'nil' to a variable of non-record type"
      end *)
  | Passign (p, PVsimple x, e) ->
      let vi = find_var x env in
      if vi.vimm then error p "variable '%s' should not be assigned to" x.s;
      let dlvl = env.lvl - vi.vlevel in
      let v, t = begin match !(vi.vaccess) with
      | Local ->
          if dlvl > 0 then
            let fpr = List.nth env.fp dlvl in
            let fp = !fpr in
            incr fpr;
            vi.vaccess := NonLocal fp;
            TVnonLocal (dlvl, fp), vi.vtype
          else
            TVlocal x.s, vi.vtype
      | NonLocal (fp) ->
          TVnonLocal (dlvl, fp), vi.vtype
      end in
      let e = typ_exp env e t in
      Tassign (v, e), VOID
  | Passign (p, PVsubscript (p', v, e1), Pnil _) ->
      let v, t' = array_var env v in
      begin match t' with
      | RECORD _ ->
          let e1 = int_exp env e1 in
          Tassign (TVsubscript (p'.Lexing.pos_lnum, v, e1), TCnil t'), VOID
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type"
      end
  | Passign (_, PVsubscript (p, v, e1), e2) ->
      let v, t' = array_var env v in
      let e1 = int_exp env e1 in
      let e2 = typ_exp env e2 t' in
      Tassign (TVsubscript (p.Lexing.pos_lnum, v, e1), e2), VOID
  | Passign (p, PVfield (p', v, x), Pnil _) ->
      let v, (t' : type_spec) = record_var env v in
      let i, tx = find_record_field env t' x in
      begin match tx with
      | RECORD _ ->
          Tassign (TVfield (p'.Lexing.pos_lnum, v, i), TCnil t'), VOID
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type"
      end
  | Passign (_, PVfield (p, v, x), e) ->
      let v, t' = record_var env v in
      let i, tx = find_record_field env.renv t' x in
      let e = typ_exp env e tx in
      Tassign (TVfield (p.Lexing.pos_lnum, v, i), e), VOID
  | Pcall (p, x, xs) ->
      assert false
      (* let x, (ts, t) = find_fun x venv in
      if List.length xs <> List.length ts then
        error p "bad arity: is %d, should be %d"
          (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            insert_let (CALL (x, List.rev ys)) (transl_typ env t)
              (fun call -> nxt call t)
        | x :: xs, t :: ts ->
            typ_exp tenv renv venv loop x t (fun x ->
              save renv ~triggers:(List.exists triggers xs) x t (fun x ->
              bind (x :: ys) (xs, ts)))
        | _ ->
            assert false
      in bind [] (xs, ts) *)
  | Pseq (_, xs) ->
      let rec bind = function
        | []      ->
            [], VOID
        | [x]     ->
            let x, t = exp env x in
            [x], t
        | x :: x' ->
            let x, _ = exp env x in
            let xs, t = bind x' in
            x :: xs, t
      in
      let xs, t = bind xs in
      Tseq xs, t
  | Pmakearray (p, x, y, Pnil _) ->
      let t, t' = find_array_type x env in
      begin match t' with
      | RECORD _ ->
          Tmakearray (int_exp env y, TCnil t'), t
      | _ ->
          error p "array base type must be record type"
      end
  | Pmakearray (_, x, y, z) ->
      let t, t' = find_array_type x env in
      let y = int_exp env y in
      let z = typ_exp env z t' in
      Tmakearray (y, z), t
  | Pmakerecord (p, x, xts) ->
      assert false
      (* let t, ts = find_record_type tenv renv x in
      let rec bind vs = function
        | [], [] ->
            let t' = (match transl_typ renv t with Tpointer t' -> t' | _ ->
              assert false) in
            insert_let (MALLOC t') (transl_typ renv t) (fun r ->
            let rec bind i = function
              | [], [] -> nxt r t
              | v :: vs, t :: ts ->
                  insert_let (GEP (r, [ VINT (32, 0); VINT (32, i) ]))
                    (Tpointer (transl_typ renv t)) (fun f ->
                      LET (Id.genid (), Tint 32, STORE (f, v), bind (i+1) (vs, ts)))
              | _ -> assert false
            in bind 1 (List.rev vs, List.map snd ts))
        | (x, Pnil _) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (VNULL (transl_typ renv t) :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "field '%s' is unknown" x.s
        | (x, e) :: xts, (x', t) :: ts ->
            if x.s = x' then
              typ_exp tenv renv venv loop e t (fun e ->
                save renv ~triggers:(List.exists (fun (_, e) -> triggers e) xts) e t (fun e ->
                  bind (e :: vs) (xts, ts)))
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "unknown field '%s'" x.s
        | [], _ ->
            error p "some fields missing from initialisation"
        | _, [] ->
            error p "all fields have already been initialised"
      in bind [] (xts, ts)
      *)
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Pif (_, x, y, None) ->
      let x = int_exp env x in
      Tif (x, void_exp env y, Tseq [], true), VOID
  | Pif (_, x, y, Some z) ->
      assert false
      (* let bl = Id.genid () in
      let w = Id.genid () in
      let tt = ref VOID in
      let body = int_exp tenv renv venv loop x (fun x ->
      insert_let (BINOP (x, Op_cmp Cne, VINT (32, 0))) (Tint 1)
        (fun c ->
          let yy = exp tenv renv venv loop y (fun y yt ->
            tt := yt;
            if yt = VOID then GOTO (bl, []) else GOTO (bl, [y])) in
        IF (c, yy,
          typ_exp tenv renv venv loop z !tt
            (fun z -> if !tt = VOID then GOTO (bl, []) else GOTO (bl, [z])))))
      in
      LET_BLOCK (bl, (if !tt = VOID then [] else [w, transl_typ renv !tt]), nxt
      (VVAR w) !tt, body) *)
  | Pwhile (_, x, y) ->
      Twhile (int_exp env x, void_exp { env with in_loop = true } y), VOID
  | Pfor (_, i, x, y, z) -> (* FIXME should check that i not be assigned to *)
      assert false
      (* let bl = Id.genid () in
      let cont = Id.genid () in
      int_exp tenv renv venv loop x (fun x ->
      int_exp tenv renv venv loop y (fun y ->
      let ii = Id.genid () in
      let venv' = add_var i ii ~immutable:true INT venv in
      LET_BLOCK (cont, [], nxt VUNDEF VOID,
      LET_BLOCK (bl, [ii, Tint 32],
        insert_let (BINOP (VVAR ii, Op_cmp Cle, y)) (Tint 1) (fun c ->
          IF (c, void_exp tenv renv venv' (Some cont) z
            (insert_let (BINOP (VVAR ii, Op_add, VINT (32, 1))) (Tint 32) (fun ii ->
              GOTO (bl, [ii]))), GOTO (cont, []))), GOTO (bl, [x])))))
      (* let body =
        insert_let (Eload (Vvar ii)) (Tint 32) (fun ii0 ->
        insert_let (Ebinop (ii0, Op_cmp Cle, y)) (Tint 1) (fun c ->
          Sif (c, void_exp tenv renv venv' true z
            (insert_let (Ebinop (ii0, Op_add, Vint (32, 1))) (Tint 32)
              (fun ii1 -> Sstore (Vvar ii, ii1))), Sbreak))) in
      Slet (ii, Tpointer (Tint 32), Ealloca (false, Tint 32),
      Sseq (Sstore (Vvar ii, x), Sseq (Sloop body, nxt Vundef VOID))))) *) *)
  | Pbreak _ when env.in_loop ->
      Tbreak, VOID
  | Pbreak p ->
      error p "illegal use of 'break'"
  | Pletvar (_, x, None, y, z) ->
      let y, yt = exp env y in
      let acc = ref Local in
      let env = add_var x yt env.lvl acc env in
      let z, zt = exp env z in
      Tletvar (x.s, acc, structured_type yt, yt, y, z), zt
  | Pletvar (p, x, Some t, Pnil _, z) ->
      let t = find_type t env in
      begin match t with
      | RECORD _ ->
          let acc = ref Local in
          let env = add_var x t env.lvl acc env in
          let z, zt = exp env z in
          Tletvar (x.s, acc, true, t, TCnil t, z), zt
      | _ ->
          error p "expected record type, found '%s'" (describe_type t)
      end
  | Pletvar (_, x, Some t, y, z) ->
      let t = find_type t env in
      let y = typ_exp env y t in
      let acc = ref Local in
      let env = add_var x t env.lvl acc env in
      let z, zt = exp env z in
      Tletvar (x.s, acc, structured_type t, t, y, z), zt
  | Plettype (_, tys, e) ->
      let env = let_type env tys in
      exp env e
  | Pletfuns (_, funs, e) ->
      let_funs env funs e

and let_funs env funs e =
  let return_type env fn =
    match fn.fn_rtyp with
    | None -> VOID
    | Some t -> find_type t env in

  let addfun env fn =
    add_fun fn.fn_name
      (List.map (fun (_, t) -> find_type t env) fn.fn_args)
      (return_type env fn) env
  in

  let addfun2 env fundef =
    let new_lvl = env.lvl+1 in
    let fi = find_fun fundef.fn_name env in
    let ts, t = fi.fsign in
    let args' = List.map (fun (x, _) -> (x, ref Local)) fundef.fn_args in
    let env = List.fold_left2
      (fun env (x, acc) t -> add_var x t new_lvl acc env) env args' ts in

    (* Process the body *)
    let body = typ_exp
      { env with lvl = new_lvl; in_loop = false; fp = ref 0 :: env.fp } fundef.fn_body t in

    { fn_name = fi.fname;
      fn_rtyp = t;
      fn_args = List.map2 (fun (x, acc) t -> (x.s, (t, acc))) args' ts;
      fn_body = body }
  in

  let env = List.fold_left addfun env funs in
  let fundefs = List.map (addfun2 env) funs in (* order matters ! *)
  let e, t = exp env e in
  Tletfuns (fundefs, e), t

let base_tenv =
  M.add "int" INT (M.add "string" STRING M.empty)

let base_venv =
  M.empty
  (* let stdlib =
    [ "print" , [STRING], VOID;
      "printi", [INT], VOID;
      "flush", [], VOID;
      "getchar", [], STRING;
      "ord", [STRING], INT;
      "chr", [INT], STRING;
      "size", [STRING], INT;
      "substring", [STRING; INT; INT], STRING;
      "concat", [STRING; STRING], STRING;
      "not", [INT], INT;
      "exit", [INT], VOID ] in
  List.fold_left (fun venv (x, ts, t) ->
    M.add x (Function (Id.make x, (ts, t))) venv) M.empty stdlib *)

let program e =
  let base_env = {
    tenv = base_tenv;
    renv = M.empty;
    venv = base_venv;
    in_loop = false;
    fp = [ref 0];
    lvl = 0
  } in
  fst (exp base_env e)
  (*
  { prog_body = s;
    prog_strings = [];
    prog_funs = [];
    prog_named = !named_structs }
    *)
