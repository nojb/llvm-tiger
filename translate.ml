open Globals
open Parsetree
open Anf

exception Error of Lexing.position * string

let error p =
  Printf.ksprintf (fun message -> raise (Error (p, message)))

type type_spec =
  | VOID
  | INT
  | STRING
  | ARRAY   of string * type_spec
  | RECORD  of string * Id.t (* name, unique name *)
  | PLACE   of string

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
  (* if t1 == t2 then true
  else match t1, t2 with
  | VOID, VOID
  | INT, INT
  | STRING, STRING -> true
  | ARRAY _, Tarray _ -> false
  | Trecord id, Trecord id' -> id = id'
  | Tplace _, _
  | _, Tplace _ -> assert false
  | _ -> false *)

type value_desc =
  | Variable of (Id.t * type_spec * bool) (* unique_name, type, immutable *)
  | Function of (Id.t * (type_spec list * type_spec))

(* type venv = (string * value_desc) list *)

module M = Map.Make (String)

let find_var id venv =
  try
    match M.find id.s venv with
    | Variable vi -> vi
    | Function _ -> raise Not_found
  with
    Not_found ->
      error id.p "unbound variable '%s'" id.s

let add_var (x : pos_string) id ?immutable:(immut=false) t venv =
  M.add x.s (Variable (id, t, immut)) venv

let add_fun x atyps rtyp venv =
  let id = Id.make x.s in
  M.add x.s (Function (id, (atyps, rtyp))) venv, id

let find_fun x venv =
  try
    match M.find x.s venv with
    | Variable _ -> raise Not_found
    | Function fi -> fi
  with
    Not_found ->
      error x.p "unbound function '%s'" x.s

(* type tenv = (string * E.typ) list *)
  
let find_type x tenv =
  try
    M.find x.s tenv
  with Not_found ->
    error x.p "unbound type '%s'" x.s

let add_type x t tenv =
  M.add x.s t tenv

let find_array_type x tenv =
  match find_type x tenv with
  | ARRAY (_, t') as t -> t, t'
  | _ as t ->
      error x.p "expected '%s' to be of array type, but is '%s'" x.s
        (describe_type t)

let find_record_type tenv renv x =
  match find_type x tenv with
  | RECORD (ts, _) as t -> t, M.find ts renv
  | _ as t ->
      error x.p "expected '%s' to be of record type, but is '%s'" x.s
        (describe_type t)

let find_record_field renv t (x : pos_string) =
  let ts = M.find t renv in
  let rec loop i = function
    | [] -> error x.p "record type '%s' does not contain field '%s'" t x.s
    | (x', t') :: xs when x' = x.s -> i, t'
    | _ :: xs -> loop (i+1) xs
  in loop 0 ts

let named_structs : (string * llvm_type list) list ref = ref []

let rec transl_typ renv t =
  let visited : string list ref = ref [] in
  let rec loop t =
    match t with
    | INT -> Tint 32
    | VOID -> Tint 32
    | STRING -> Tpointer (Tint 8)
    | ARRAY (_, t) -> (* { i32, i32, [0 x t] }* *)
        Tpointer (Tstruct [| Tint 32; Tint 32; Tarray (0, transl_typ renv t) |])
    | RECORD (rname, uid) ->
        if not (List.exists (fun (x, _) -> x = Id.to_string uid) !named_structs)
        && not (List.mem (Id.to_string uid) !visited)
        then begin
          visited := (Id.to_string uid) :: !visited;
          named_structs := (Id.to_string uid,
            (Tint 32 :: List.map (fun (_, t) -> loop t) (M.find rname renv))) :: !named_structs
        end;
        Tpointer (Tnamedstruct (Id.to_string uid))
    | PLACE _ ->
        assert false
  in loop t

let declare_type tenv (x, t) =
  let find_type y tenv =
    try M.find y.s tenv
    with Not_found -> PLACE y.s in
  match t with
  | PTname y ->
      add_type x (find_type y tenv) tenv
  | PTarray y ->
      add_type x (ARRAY (x.s, find_type y tenv)) tenv
  | PTrecord xs ->
      add_type x (RECORD (x.s, Id.make x.s)) tenv

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

let define_type tenv (x, _) =
  let visited = ref [] in
  let rec loop y =
    if List.mem y !visited then
      error x.p "type declaration cycle does not pass through record type"
    visited := y :: !visited;
    try
      let t = M.find y tenv in
      match t with
      | PLACE y -> loop y
      | ARRAY (x, PLACE y') -> ARRAY (x, loop y')
      | _ -> t
    with Not_found ->
      error x.p "unbound type '%s'" y
        (* FIXME x.p != position of y in general *)
  in add_type x (loop x.s) tenv

let extract_record_type tenv renv (x, t) =
  match t with
  | PTrecord (xts) ->
      M.add x.s (List.map (fun (x, t) -> (x.s, find_type t tenv)) xts) renv
  | _ ->
      renv

let let_type tenv renv tys =
  check_unique_type_names tys;
  let tenv = List.fold_left declare_type tenv tys in
  let tenv = List.fold_left define_type tenv tys in
  let renv = List.fold_left (extract_record_type tenv) renv tys in
  tenv, renv

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

let rec triggers = function
  | Pint _
  | Pstring _
  | Pnil _ -> false
  | Pvar (_, v) -> triggers_var v
  | Pbinop (_, e1, _, e2) -> triggers e1 || triggers e2
  | Passign (_, v, e) -> triggers_var v || triggers e
  | Pcall _ -> true
  | Pseq (_, es) -> List.exists triggers es
  | Pmakearray _
  | Pmakerecord _ -> true
  | Pif (_, e1, e2, None) -> triggers e1 || triggers e2
  | Pif (_, e1, e2, Some e3) -> triggers e1 || triggers e2 || triggers e3
  | Pwhile (_, e1, e2) -> triggers e1 || triggers e2
  | Pfor (_, _, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Pbreak _ -> false
  | Pletvar (_, _, _, e1, e2) -> triggers e1 || triggers e2
  | Pletfuns (_, _, e)
  | Plettype (_, _, e) -> triggers e

and triggers_var = function
  | PVsimple _ -> false
  | PVsubscript (_, v, e) -> triggers_var v || triggers e
  | PVfield (_, v, _) -> triggers_var v

  (*
let rec pure = function
  | Eundef
  | Eint _
  | T.Vstring _
  | T.Enull _
  | T.Eaddr _
  | T.Evar _ -> true
  | T.Eload e -> pure e
  | T.Ebinop (e1, _, e2) ->
      pure e1 && pure e2
  | T.Ecall (_, _, ea)
  | T.Ebuiltin (_, ea) ->
      array_exists pure ea
  | T.Egep (e, ea) ->
      pure e && array_exists pure ea
      *)

let insert_let e t k =
  let x' = Id.genid () in
  LET (x', t, e, k (VVAR x'))

let save renv ?triggers:(triggers=true) e t nxt =
  if structured_type t && triggers then
    match e with
    | VLOAD _ as v -> nxt v
    | _ ->
        let id = Id.genid () in
        LET (id, Tpointer (transl_typ renv t),
          ALLOCA (true, transl_typ renv t),
          LET (Id.genid (), Tint 32, STORE (VVAR id, e), nxt (VLOAD id)))
  else
    nxt e

(* These utility functions are used in the processing of function definitions *)

let return_type tenv fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t tenv

(* Memory layout of arrays
 *
 * -----------------------------------------------
 * | i32 (gc tag) | i32 (no of elems) | elements |
 * -----------------------------------------------
 * 
 * This means that the type [T = array of t] is represented
 * by the following LLVM type:
 * 
 * %T = type { i32, i32, [0 x t] }*
 *
 * Thus given an llvm variable of type %T named a, in order
 * to reference its i-th element we need to use the gep
 * instruction as follows
 *
 * %a_i = getelementptr T %a, 0, 2, 0, i ; has type t*
 * *)

let array_length v nxt =
  insert_let (GEP (v, [ VINT (32, 0); VINT (32, 1) ]))
    (Tpointer (Tint 32)) (fun lenp -> insert_let (LOAD lenp) (Tint 32) nxt)

let array_index p t' v x nxt =
  array_length v (fun l ->
  insert_let (BINOP (x, Op_cmp Cle, l)) (Tint 1) (fun c ->
  IF (c, insert_let (GEP (v, [ VINT (32, 0); VINT (32, 2); x ])) t' nxt,
    DIE (Printf.sprintf "Runtime error: index out of bounds in line %d\n"
    p.Lexing.pos_lnum))))

let record_index p tx v i nxt =
  insert_let (PTRTOINT v) (Tint 64) (fun ptr ->
  insert_let (BINOP (ptr, Op_cmp Cne, VINT (64, 0))) (Tint 1) (fun c ->
  IF (c, insert_let (GEP (v, [ VINT (32, 0); VINT (32, i+1) ])) tx nxt,
    DIE (Printf.sprintf "field access to nil record in line %d"
      p.Lexing.pos_lnum))))

let rec array_var tenv renv venv loop v nxt =
  var tenv renv venv loop v (fun v' t ->
    match t with
    | ARRAY (_, t') -> nxt v' t t'
    | _ ->
        error (var_p v) "expected variable of array type, but type is '%s'"
          (describe_type t))

and record_var tenv renv venv loop v nxt =
  var tenv renv venv loop v (fun v' t ->
    match t with
    | RECORD (t', _) -> nxt v' t t'
    | _ ->
        error (var_p v) "expected variable of record type, but type is '%s'"
          (describe_type t))

and typ_exp tenv renv venv loop e t' nxt =
  exp tenv renv venv loop e (fun e' t ->
    if type_equal t t' then nxt e'
    else error (exp_p e)
      "type mismatch: expected type '%s', instead found '%s'"
        (string_of_type t') (string_of_type t))

and int_exp tenv renv venv loop e nxt =
  typ_exp tenv renv venv loop e INT nxt

and void_exp tenv renv venv loop e nxt =
  typ_exp tenv renv venv loop e VOID (fun _ -> nxt)

(* Main typechecking/compiling functions *)

and var tenv renv venv loop v nxt =
  match v with
  | PVsimple x ->
      let x, t, immut = find_var x venv in
      nxt (if immut then VVAR x else VLOAD x) t
  | PVsubscript (p, v, x) ->
      array_var tenv renv venv loop v (fun v t t' ->
      save renv ~triggers:(triggers x) v t (fun v ->
      int_exp tenv renv venv loop x (fun x ->
      array_index p (transl_typ renv t') v x (fun v ->
      insert_let (LOAD v) (transl_typ renv t') (fun v -> nxt v t')))))
  | PVfield (p, v, x) -> (* should check for nil XXX *)
      record_var tenv renv venv loop v (fun v t t' ->
      let i, tx = find_record_field renv t' x in
      record_index p (transl_typ renv tx) v i (fun v ->
      insert_let (LOAD v) (transl_typ renv tx) (fun v -> nxt v tx)))

and exp tenv renv venv loop e nxt =
  match e with
  | Pint (_, n) ->
      nxt (VINT (32, n)) INT
  (* | Pstring (_, s) ->
      nxt (Vstring s) STRING *)
  | Pnil p ->
      error p
        "'nil' should be used in a context where \
        its type can be determined"
  | Pvar (_, v) ->
      var tenv renv venv loop v nxt
  | Pbinop (_, x, (Op_add as op), y)
  | Pbinop (_, x, (Op_sub as op), y)
  | Pbinop (_, x, (Op_mul as op), y)
  | Pbinop (_, x, (Op_div as op), y)
  | Pbinop (_, x, (Op_and as op), y)
  | Pbinop (_, x, (Op_cmp Ceq as op), y) ->
      int_exp tenv renv venv loop x (fun x ->
      int_exp tenv renv venv loop y (fun y ->
      insert_let (BINOP (x, op, y)) (Tint 32) (fun v -> nxt v INT)))
  | Pbinop _ ->
      failwith "binop not implemented"
  | Passign (p, PVsimple x, Pnil _) ->
      let x, t, immut = find_var x venv in
      begin match t with
      | RECORD _ ->
          LET (Id.genid (), Tint 32, STORE (VVAR x, VNULL (transl_typ renv t)),
          nxt VUNDEF VOID)
      | _ ->
          error p "trying to assign 'nil' to a variable of non-record type"
      end
  | Passign (p, PVsimple x0, e) ->
      let x, t, immut = find_var x0 venv in
      if immut then error p "variable '%s' should not be assigned to" x0.s;
      typ_exp tenv renv venv loop e t (fun e ->
      LET (Id.genid (), Tint 32, STORE (VVAR x, e), nxt VUNDEF VOID))
  | Passign (p, PVsubscript (_, v, e1), Pnil _) ->
      array_var tenv renv venv loop v (fun v t t' ->
      begin match t' with
      | RECORD _ ->
          save renv ~triggers:(triggers e1) v t (fun v ->
          int_exp tenv renv venv loop e1 (fun e1 ->
          array_index p (transl_typ renv t') v e1 (fun v ->
          LET (Id.genid (), Tint 32, STORE (v, VNULL (transl_typ renv t')), nxt VUNDEF VOID))))
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type"
      end)
  | Passign (_, PVsubscript (p, v, e1), e2) ->
      array_var tenv renv venv loop v (fun v t t' ->
      save renv ~triggers:(triggers e1 || triggers e2) v t (fun v ->
      int_exp tenv renv venv loop e1 (fun e1 ->
      array_index p (transl_typ renv t') v e1 (fun v ->
      typ_exp tenv renv venv loop e2 t'
        (fun e2 -> LET (Id.genid (), Tint 32, STORE (v, e2), nxt VUNDEF VOID))))))
  | Passign (p, PVfield (_, v, x), Pnil _) ->
      record_var tenv renv venv loop v (fun v t t' ->
      let i, tx = find_record_field renv t' x in
      begin match tx with
      | RECORD _ ->
          record_index p (transl_typ renv tx) v i (fun v ->
          LET (Id.genid (), Tint 32, STORE (v, VNULL (transl_typ renv tx)), nxt VUNDEF VOID))
      | _ ->
          error p "trying to assign 'nil' to a field of non-record type"
      end)
  | Passign (_, PVfield (p, v, x), e) ->
      record_var tenv renv venv loop v (fun v t t' ->
      let i, tx = find_record_field renv t' x in
      save renv ~triggers:(triggers e) v t (fun v ->
      record_index p (transl_typ renv tx) v i (fun v ->
      typ_exp tenv renv venv loop e tx
        (fun e -> LET (Id.genid (), Tint 32, STORE (v, e), nxt VUNDEF VOID)))))
  | Pcall (p, x, xs) ->
      let x, (ts, t) = find_fun x venv in
      if List.length xs <> List.length ts then
        error p "bad arity: is %d, should be %d"
          (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            insert_let (CALL (x, List.rev ys)) (transl_typ renv t)
              (fun call -> nxt call t)
        | x :: xs, t :: ts ->
            typ_exp tenv renv venv loop x t (fun x ->
              save renv ~triggers:(List.exists triggers xs) x t (fun x ->
              bind (x :: ys) (xs, ts)))
        | _ ->
            assert false
      in bind [] (xs, ts)
  | Pseq (_, xs) ->
      let rec bind = function
        | []      ->
            nxt VUNDEF VOID
        | [x]     ->
            exp tenv renv venv loop x nxt
        | x :: x' ->
            exp tenv renv venv loop x (fun _ _ -> bind x')
      in
      bind xs
  | Pmakearray (p, x, y, Pnil _) ->
      let t, t' = find_array_type x tenv in
      begin match t' with
      | RECORD _ ->
          int_exp tenv renv venv loop y (fun y ->
          insert_let (ARRAY_MALLOC (y, VNULL (transl_typ renv t')))
            (transl_typ renv t) (fun arr -> nxt arr t))
      | _ ->
          error p "array base type must be record type"
      end
  | Pmakearray (_, x, y, z) ->
      let t, t' = find_array_type x tenv in
      int_exp tenv renv venv loop y (fun y ->
      typ_exp tenv renv venv loop z t' (fun z ->
      insert_let (ARRAY_MALLOC (y, z)) (transl_typ renv t)
        (fun arr -> nxt arr t)))
  | Pmakerecord (p, x, xts) ->
      let t, ts = find_record_type tenv renv x in
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
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Pif (_, x, y, None) ->
      let bl = Id.genid () in
      LET_BLOCK (bl, [], nxt VUNDEF VOID,
      int_exp tenv renv venv loop x (fun x ->
      insert_let (BINOP (x, Op_cmp Cne, VINT (32, 0))) (Tint 1)
        (fun c -> IF (c, void_exp tenv renv venv loop y (GOTO (bl, [])),
          (GOTO (bl, [])))))) (* FIXME _v *)
  | Pif (_, x, y, Some z) ->
      let bl = Id.genid () in
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
      LET_BLOCK (bl, (if !tt = VOID then [] else [w, transl_typ renv !tt]), nxt (VVAR w) !tt, body)
  | Pwhile (_, x, y) ->
      let cont = Id.genid () in
      let bl = Id.genid () in
      let body = int_exp tenv renv venv loop x (fun x ->
      insert_let (BINOP (x, Op_cmp Cne, VINT (32, 0))) (Tint 1)
      (fun c -> IF (c, void_exp tenv renv venv (Some cont) y (GOTO (bl, [])), GOTO
      (cont, [])))) in
      LET_BLOCK (cont, [], nxt VUNDEF VOID,
      LET_BLOCK (bl, [], body, GOTO (bl, [])))
  | Pfor (_, i, x, y, z) -> (* FIXME should check that i not be assigned to *)
      let bl = Id.genid () in
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
      Sseq (Sstore (Vvar ii, x), Sseq (Sloop body, nxt Vundef VOID))))) *)
  | Pbreak p ->
      begin match loop with
        Some cont -> GOTO (cont, []) (* ignore nxt *)
      | None -> error p "illegal use of 'break'"
      end
  | Pletvar (_, x, None, y, z) ->
      exp tenv renv venv loop y (fun y yt ->
      let id = Id.genid () in
      let venv = add_var x id yt venv in
      LET (id, Tpointer (transl_typ renv yt),
      ALLOCA (structured_type yt, transl_typ renv yt),
      LET (Id.genid (), Tint 32, STORE (VVAR id, y),
      exp tenv renv venv loop z nxt)))
  | Pletvar (p, x, Some t, Pnil _, z) ->
      let t = find_type t tenv in
      begin match t with
      | RECORD _ ->
          let id = Id.genid () in
          let venv = add_var x id t venv in
          LET (id, Tpointer (transl_typ renv t),
          ALLOCA (structured_type t, transl_typ renv t),
          LET (Id.genid (), Tint 32, STORE (VVAR id, VNULL (transl_typ renv t)),
          exp tenv renv venv loop z nxt))
      | _ ->
          error p "expected record type, found '%s'" (describe_type t)
      end
  | Pletvar (_, x, Some t, y, z) ->
      let t = find_type t tenv in
      typ_exp tenv renv venv loop y t (fun y ->
      let id = Id.genid () in
      let venv = add_var x id t venv in
      LET (id, Tpointer (transl_typ renv t),
      ALLOCA (structured_type t, transl_typ renv t),
      LET (Id.genid (), Tint 32, STORE (VVAR id, y),
      exp tenv renv venv loop z nxt)))
  | Plettype (_, tys, e) ->
      let tenv, renv = let_type tenv renv tys in
      exp tenv renv venv loop e nxt
  | Pletfuns (_, funs, e) ->
      let_funs tenv renv venv loop funs e nxt

and let_funs tenv renv venv loop funs e nxt =
  let addfun venv fn =
    fst (add_fun fn.fn_name
      (List.map (fun (_, t) -> find_type t tenv) fn.fn_args)
      (return_type tenv fn) venv)
  in
  let addfun2 venv {fn_name; fn_args; fn_rtyp; fn_body} =
    let f, (ts, t) = find_fun fn_name venv in
    let venv, args = List.fold_left2
      (fun (venv, args) (x, _) t -> let x' = Id.make x.s in add_var x x' t venv, x' :: args)
      (venv, []) fn_args ts in
    let args' = List.map (fun x -> Id.make (Id.to_string x)) args in
    let args' = List.combine args' ts in

    (* Process the body *)
    let body = typ_exp tenv renv venv None fn_body t
      (fun e ->
        match t with
        | VOID ->
            RETURN (VAL (VINT (32, 0)))
        | t ->
            RETURN (VAL e)) in

    let body =
      List.fold_right2 (fun (x', t') x body ->
        LET (x, Tpointer (transl_typ renv t'),
          ALLOCA (structured_type t', (transl_typ renv t')),
        LET (Id.genid (), Tint 32, STORE (VVAR x, VVAR x'),
          body))) (List.rev args') (List.rev args) body in

    { fn_name = f;
      fn_rtyp = Some (transl_typ renv t); (* FIXME XXX *)
      fn_args = List.rev_map (fun (x, t) -> (x, transl_typ renv t)) args';
      fn_body = body }
  in
  let venv = List.fold_left addfun venv funs in
  LET_REC (List.map (addfun2 venv) funs, exp tenv renv venv loop e nxt)

let base_tenv =
  M.add "int" INT (M.add "string" STRING M.empty)

let base_venv =
  let stdlib =
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
    M.add x (Function (Id.make x, (ts, t))) venv) M.empty stdlib

let program e =
  let base_renv = M.empty in
  let s = exp base_tenv base_renv base_venv None e
    (fun _ _ -> RETURN (VAL (VINT (32, 0)))) in
  { prog_body = s;
    prog_strings = [];
    prog_funs = [];
    prog_named = !named_structs }
