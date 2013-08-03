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

  (* used for lambda lifting *)
  vars : type_spec M.t;
  funs : S.t;
  sols : S.t M.t
}

let find_var id env =
  try
    match M.find id.s env.venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with
    Not_found ->
      error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) ?immutable:(immut=false) t env =
  let vi = { vtype = t; vimm = immut } in
  { env with
      venv = M.add x.s (Variable vi) env.venv;
      vars = M.add x.s t env.vars }

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
  let t = match t with RECORD (t, _) -> t | _ -> assert false in
  let ts = M.find t env.renv in
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in loop 0 ts

let named_structs : (string * Llvm.lltype) list ref = ref []

let rec transl_typ env t =
  let open Llvm in
  let int_t w = integer_type (global_context ()) w in
  let visited : string list ref = ref [] in
  let rec loop t =
    match t with
    | INT   -> int_t 32
    | VOID  -> int_t 32
    | STRING -> pointer_type (int_t 8)
    | ARRAY (_, t) -> (* { i32, i32, [0 x t] }* *)
        pointer_type (struct_type (global_context ())
          [| int_t 32; int_t 32; array_type (loop t) 0 |])
    | RECORD (rname, uid) ->
        if not (List.exists (fun (x, _) -> x = Id.to_string uid) !named_structs)
        && not (List.mem (Id.to_string uid) !visited)
        then begin
          visited := (Id.to_string uid) :: !visited;
          let ty = named_struct_type (global_context ()) (Id.to_string uid) in
          named_structs := (Id.to_string uid, ty) :: !named_structs;
          struct_set_body ty
            (Array.of_list (int_t 32 :: List.map (fun (_, t) -> loop t) (M.find rname
            env.renv))) false;
          (* ()) (Id.to_string uid)) :: !named_structs
            (Tint 32 :: List.map (fun (_, t) -> loop t) (M.find rname
            env.renv))) :: !named_structs *)
        end;
        pointer_type (List.assoc (Id.to_string uid) !named_structs)
        (* pointer_type (named_struct_type 
        Tpointer (Tnamedstruct (Id.to_string uid)) *)
    | PLACE _ ->
        assert false
  in loop t

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

let tr_return_type env fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t env

let tr_function_header env fn =
  add_fun fn.fn_name
    (List.map (fun (_, t) -> find_type t env) fn.fn_args)
    (tr_return_type env fn) env

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

let toplevel : (string, Llvm.lltype, Llvm.lltype * ptr_flag * free_flag, exp) fundef list ref =
  ref []

let rec tr_function_body env fundef =
  let fi = find_fun fundef.fn_name env in
  let ts, t = fi.fsign in

  let env = List.fold_left2 (fun env (x, _) t -> add_var x t env) env fundef.fn_args ts in

  (* Process the body *)
  let body = typ_exp env fundef.fn_body t in

  let formals =
    let getfree x =
      let t = M.find x env.vars in
      (transl_typ env t, IsPtr (structured_type t), IsFree true)
    in
    List.fold_right (fun x args -> (x, getfree x) :: args)
      (S.elements (M.find fundef.fn_name.s env.sols))
      (List.map2 (fun (x, _) t -> (x.s, (transl_typ env t, IsPtr (structured_type t), IsFree false)))
      fundef.fn_args ts) in

  toplevel := { fn_name = fi.fname; fn_rtyp = transl_typ env t; fn_args = formals; fn_body =
    body } :: !toplevel

and let_funs env fundefs e =
  let join m1 m2 = M.fold M.add m1 m2 in

  check_unique_fundef_names fundefs;

  Solver.reset ();
  List.iter (fun f ->
    let gs' = S.elements (fc f.fn_body) in
    let gs  = List.filter (fun fundef -> List.mem f.fn_name.s gs') fundefs in
    let sf  = S.filter (fun v -> M.mem v env.vars) (fv f.fn_body) in
    let hs  = List.filter (fun h -> S.mem h env.funs) gs' in
    let sf  = union_list (sf :: List.map (fun h -> M.find h env.sols) hs) in
    Solver.add_equation f.fn_name.s sf (List.map (fun g -> g.fn_name.s) gs))
    fundefs;
  let sols' = Solver.solve () in
  let sols' = join env.sols sols' in
  let funs' = List.fold_right S.add (List.map (fun f -> f.fn_name.s) fundefs)
    env.funs in
  let env' = { env with funs = funs'; sols = sols' } in
  let env' = List.fold_left tr_function_header env' fundefs in
  List.iter (tr_function_body env') fundefs;
  exp env' e

and array_var env v =
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
      TVsimple (x.s, IsImm vi.vimm), vi.vtype
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
  | Passign (p, PVsimple x, Pnil _) ->
      let vi = find_var x env in
      begin match vi.vtype with
      | RECORD _ ->
          Tassign (TVsimple (x.s, IsImm false),
            TCnil (transl_typ env vi.vtype)), VOID
      | _ ->
          error p "trying to assign 'nil' to a variable of non-record type"
      end
  | Passign (p, PVsimple x, e) ->
      let vi = find_var x env in
      if vi.vimm then error p "variable '%s' should not be assigned to" x.s;
      let e = typ_exp env e vi.vtype in
      Tassign (TVsimple (x.s, IsImm vi.vimm), e), VOID
  | Passign (p, PVsubscript (p', v, e1), Pnil _) ->
      let v, t' = array_var env v in
      begin match t' with
      | RECORD _ ->
          let e1 = int_exp env e1 in
          Tassign (TVsubscript (p'.Lexing.pos_lnum, v, e1),
            TCnil (transl_typ env t')), VOID
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
          Tassign (TVfield (p'.Lexing.pos_lnum, v, i),
            TCnil (transl_typ env t')), VOID
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type"
      end
  | Passign (_, PVfield (p, v, x), e) ->
      let v, t' = record_var env v in
      let i, tx = find_record_field env t' x in
      let e = typ_exp env e tx in
      Tassign (TVfield (p.Lexing.pos_lnum, v, i), e), VOID
  | Pcall (p, x, xs) ->
      let fi = find_fun x env in
      let ts, t = fi.fsign in
      if List.length xs <> List.length ts then
        error p "bad arity: is %d, should be %d"
          (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            let actuals =
              List.fold_right (fun x ys -> ArgNonLocal x :: ys)
                (S.elements (M.find x.s env.sols)) (List.rev ys) in
            Tcall (fi.fname, actuals), t
        | x :: xs, t :: ts ->
            let x = typ_exp env x t in
            bind (ArgExp (x, IsPtr (structured_type t)) :: ys) (xs, ts)
        | _ ->
            assert false
      in bind [] (xs, ts)
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
          Tmakearray (transl_typ env t', int_exp env y,
            TCnil (transl_typ env t')), t
      | _ ->
          error p "array base type must be record type"
      end
  | Pmakearray (_, x, y, z) ->
      let t, t' = find_array_type x env in
      let y = int_exp env y in
      let z = typ_exp env z t' in
      Tmakearray (transl_typ env t', y, z), t
  | Pmakerecord (p, x, xts) ->
      let t, ts = find_record_type env x in
      let rec bind vs = function
        | [], [] ->
            Tmakerecord (transl_typ env t, List.rev vs), t
            (* let t' = (match transl_typ renv t with Tpointer t' -> t' | _ ->
              assert false) in
            insert_let (MALLOC t') (transl_typ renv t) (fun r ->
            let rec bind i = function
              | [], [] -> nxt r t
              | v :: vs, t :: ts ->
                  insert_let (GEP (r, [ VINT (32, 0); VINT (32, i) ]))
                    (Tpointer (transl_typ renv t)) (fun f ->
                      LET (Id.genid (), Tint 32, STORE (f, v), bind (i+1) (vs, ts)))
              | _ -> assert false
            in bind 1 (List.rev vs, List.map snd ts)) *)
        | (x, Pnil _) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind ((TCnil (transl_typ env t), IsPtr false) :: vs) (xts, ts)
            else
              if List.exists (fun (x', _) -> x.s = x') ts then
                error x.p "field '%s' is in the wrong other" x.s
              else
                error x.p "field '%s' is unknown" x.s
        | (x, e) :: xts, (x', t) :: ts ->
            if x.s = x' then
              let e = typ_exp env e t in
              bind ((e, IsPtr (structured_type t)) :: vs) (xts, ts)
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
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Pif (_, x, y, None) ->
      let x = int_exp env x in
      Tif (x, void_exp env y, Tseq [], IsVoid true, transl_typ env VOID), VOID
  | Pif (_, x, y, Some z) ->
      let x = int_exp env x in
      let y, ty = exp env y in
      let z = typ_exp env z ty in
      Tif (x, y, z, IsVoid (ty = VOID), transl_typ env ty), ty
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
  | Pfor (_, i, x, y, z) ->
      let x = int_exp env x in
      let y = int_exp env y in
      let env' = add_var i ~immutable:true INT env in
      Tfor (i.s, x, y, void_exp { env' with in_loop = true } z), VOID
  | Pbreak _ when env.in_loop ->
      Tbreak, VOID
  | Pbreak p ->
      error p "illegal use of 'break'"
  | Pletvar (_, x, None, y, z) ->
      let y, yt = exp env y in
      let env = add_var x yt env in
      let z, zt = exp env z in
      Tletvar (x.s, IsPtr (structured_type yt), transl_typ env yt, y, z), zt
  | Pletvar (p, x, Some t, Pnil _, z) ->
      let t = find_type t env in
      begin match t with
      | RECORD _ ->
          let env = add_var x t env in
          let z, zt = exp env z in
          Tletvar (x.s, IsPtr true, transl_typ env t, TCnil (transl_typ env t), z), zt
      | _ ->
          error p "expected record type, found '%s'" (describe_type t)
      end
  | Pletvar (_, x, Some t, y, z) ->
      let t = find_type t env in
      let y = typ_exp env y t in
      let env = add_var x t env in
      let z, zt = exp env z in
      Tletvar (x.s, IsPtr (structured_type t), transl_typ env t, y, z), zt
  | Plettype (_, tys, e) ->
      let env = let_type env tys in
      exp env e
  | Pletfuns (_, funs, e) ->
      let_funs env funs e

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
  toplevel := [];
  let base_env = {
    tenv = base_tenv;
    renv = M.empty;
    venv = base_venv;
    in_loop = false;
    vars = M.empty;
    funs = S.empty;
    sols = M.empty
  } in
  let e, _ = exp base_env e in
  { fn_name = "main"; fn_rtyp = transl_typ base_env INT; fn_args = []; fn_body = Tseq [e; TCint 0] } :: !toplevel
  (*
  { prog_body = s;
    prog_strings = [];
    prog_funs = [];
    prog_named = !named_structs }
    *)
