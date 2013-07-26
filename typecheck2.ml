open Globals
open Parsetree
open Typedtree2

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
  | Variable of (Id.t * type_spec)
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

let add_var (x : pos_string) id t venv =
  M.add x.s (Variable (id, t)) venv

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

let named_structs : (string * typ array) list ref = ref []

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
          named_structs := (Id.to_string uid, Array.of_list
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

let triggers _ =
  true

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
  match e with
  | Evalue v -> k v
  | _ ->
      let x' = Id.genid () in
      Slet (x', t, e, k (Vvar x'))

let save renv ?triggers:(triggers=true) e t nxt =
  insert_let e (transl_typ renv t) (fun e ->
  if structured_type t && triggers then
    match e with
    | Vload _ as v -> nxt v
    | _ ->
        let id = Id.genid () in
        Slet (id, Tpointer (transl_typ renv t),
          Ealloca (true, transl_typ renv t),
          Sseq (Sstore (Vvar id, e), nxt (Vload id)))
  else
    nxt e)

(* These utility functions are used in the processing of function definitions *)

let return_type tenv fn =
  match fn.fn_rtyp with
  | None -> VOID
  | Some t -> find_type t tenv

let add_formal (env, args) (x, _) t =
  assert false
  (* let x' = Id.make x in
  let env = add_variable x x' t env in
  env, (x', transl_typ t) :: args *)

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
  insert_let (Egep (v, [| Vint (32, 0); Vint (32, 1) |]))
    (Tpointer (Tint 32)) (fun lenp -> nxt (Eload lenp))

let array_index v x nxt =
  array_length v (fun l ->
    insert_let l (Tint 32) (fun l ->
    insert_let (Ebinop (x, Op_cmp Cle, l)) (Tint 1) (fun c ->
      nxt (Eassert (c, Egep (v, [| Vint (32, 0); Vint (32, 2); x |]),
      (Printf.sprintf "index out of bounds in line %d" (-1)))))))

let record_index v i nxt =
  insert_let (Optrtoint v) (Tint 64) (fun p ->
  insert_let (Ebinop (p, Op_cmp Cne, Vint (64, 0))) (Tint 1) (fun c ->
    nxt (Eassert (c, Egep (v, [| Vint (32, 0); Vint (32, i+1) |]),
    (Printf.sprintf "field access to nil record in line %d" (-1))))))

let side_expr e =
  Slet (Id.genid (), transl_typ M.empty VOID, e, Sskip)

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
  typ_exp tenv renv venv loop e VOID nxt

(* Main typechecking/compiling functions *)

and var tenv renv venv loop v nxt =
  match v with
  | PVsimple x ->
      let x, t = find_var x venv in
      nxt (Evalue (Vload x)) t
  | PVsubscript (_, v, x) ->
      array_var tenv renv venv loop v (fun v t t' ->
        save renv ~triggers:(triggers x) v t (fun v ->
        int_exp tenv renv venv loop x (fun x ->
          insert_let x (Tint 32) (fun x ->
          array_index v x (fun v ->
            insert_let v (Tpointer (transl_typ renv t')) (fun v ->
            nxt (Eload v) t'))))))
  | PVfield (_, v, x) -> (* should check for nil XXX *)
      record_var tenv renv venv loop v (fun v t t' ->
        let i, tx = find_record_field renv t' x in
        insert_let v (transl_typ renv t) (fun v ->
        record_index v i (fun v ->
          insert_let v (Tpointer (transl_typ renv tx))
            (fun v -> nxt (Eload v) tx))))

and exp tenv renv (venv : value_desc M.t) loop e nxt =
  match e with
  | Pint (_, n) ->
      nxt (Evalue (Vint (32, n))) INT
  | Pstring (_, s) ->
      nxt (Evalue (Vstring s)) STRING
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
        insert_let x (Tint 32) (fun x ->
        int_exp tenv renv venv loop y (fun y ->
          insert_let y (Tint 32) (fun y ->
          nxt (Ebinop (x, op, y)) INT))))
  | Pbinop _ ->
      failwith "binop not implemented"
  | Passign (_, PVsimple x, Pnil _) ->
      assert false
  | Passign (_, PVsimple x, e) ->
      let x, t = find_var x venv in
      typ_exp tenv renv venv loop e t (fun e ->
        insert_let e (transl_typ renv t) (fun e ->
        Sseq (Sstore (Vvar x, e), nxt (Evalue Vundef) VOID)))
  | Passign (_, PVsubscript (_, v, e1), Pnil _) ->
      assert false
  | Passign (_, PVsubscript (_, v, e1), e2) ->
      array_var tenv renv venv loop v (fun v t t' ->
        save renv ~triggers:(triggers e1 || triggers e2) v t (fun v ->
        int_exp tenv renv venv loop e1 (fun e1 ->
          insert_let e1 (Tint 32) (fun x ->
            array_index v x (fun v ->
              insert_let v (Tpointer (transl_typ renv t')) (fun v ->
              typ_exp tenv renv venv loop e2 t'
                (fun e2 -> insert_let e2 (transl_typ renv t')
                (fun e2 -> Sseq (Sstore (v, e2), nxt (Evalue Vundef) VOID)))))))))
  | Passign (_, PVfield (_, v, x), Pnil _) ->
      assert false
  | Passign (_, PVfield (_, v, x), e) ->
      record_var tenv renv venv loop v (fun v t t' ->
        let i, tx = find_record_field renv t' x in
        save renv ~triggers:(triggers e) v t (fun v ->
        record_index v i (fun v ->
          insert_let v (Tpointer (transl_typ renv tx)) (fun v ->
          typ_exp tenv renv venv loop e tx
            (fun e -> insert_let e (transl_typ renv tx)
            (fun e -> Sseq (Sstore (v, e), nxt (Evalue Vundef) VOID)))))))
  | Pcall (p, x, xs) ->
      let x, (ts, t) = find_fun x venv in
      if List.length xs <> List.length ts then
        error p "bad arity: is %d, should be %d"
          (List.length xs) (List.length ts);
      let rec bind ys = function
        | [], [] ->
            nxt (Ecall (x, Array.of_list (List.rev ys))) t
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
            nxt (Evalue Vundef) VOID
        | [x]     ->
            exp tenv renv venv loop x nxt
        | x :: x' ->
            exp tenv renv venv loop x (fun e t ->
              Slet (Id.genid (), transl_typ renv t, e, bind x'))
      in
      bind xs
  | Pmakearray (_, x, y, z) ->
      let t, t' = find_array_type x tenv in
      int_exp tenv renv venv loop  y (fun y ->
        insert_let y (Tint 32) (fun y ->
        typ_exp tenv renv venv loop z t' (fun z ->
          (* nxt (Earraymalloc (transl_typ renv t', y)) t))) *)
          insert_let z (transl_typ renv t') (fun z ->
          nxt (Earraymalloc (y, z)) t))))
  | Pmakerecord (p, x, xts) ->
      let t, ts = find_record_type tenv renv x in
      let rec bind vs = function
        | [], [] ->
            let t' = (match transl_typ renv t with Tpointer t' -> t' | _ ->
              assert false) in
            insert_let (Emalloc t') (transl_typ renv t) (fun r ->
            let rec bind i = function
              | [], [] -> nxt (Evalue r) t
              | v :: vs, t :: ts ->
                  insert_let (Egep (r, [| Vint (32, 0); Vint (32, i) |]))
                    (Tpointer (transl_typ renv t)) (fun f ->
                      Sseq (Sstore (f, v), bind (i+1) (vs, ts)))
              | _ -> assert false
            in bind 1 (List.rev vs, List.map snd ts))
        | (x, Pnil _) :: xts, (x', t) :: ts ->
            if x.s = x' then
              bind (Vnull (transl_typ renv t) :: vs) (xts, ts)
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
      int_exp tenv renv venv loop x (fun x ->
        insert_let x (Tint 32) (fun x ->
        insert_let (Ebinop (x, Op_cmp Cne, Vint (32, 0))) (Tint 1)
          (fun c -> Sseq (Sif (c, void_exp tenv renv venv loop y side_expr,
            Sskip), nxt (Evalue Vundef) VOID))))
  | Pif (_, x, y, Some z) ->
      int_exp tenv renv venv loop x (fun x ->
        let tmp = Id.genid () in
        let tt = ref VOID in
        let yy = exp tenv renv venv loop y (fun y yt ->
          tt := yt;
          insert_let y (transl_typ renv yt) (fun y ->
          Sstore (Vvar tmp, y))) in
        let zz = typ_exp tenv renv venv loop z !tt (fun z ->
          insert_let z (transl_typ renv !tt) (fun z ->
          Sstore (Vvar tmp, z))) in
        insert_let x (Tint 32) (fun x ->
        Slet (tmp, Tpointer (transl_typ renv !tt),
          Ealloca (structured_type !tt, transl_typ renv !tt),
          insert_let (Ebinop (x, Op_cmp Cne, Vint (32, 0))) (Tint 1)
            (fun c -> Sseq (Sif (c, yy, zz),
              nxt (Evalue (Vload tmp)) !tt)))))
  | Pwhile (_, x, y) ->
      let body = int_exp tenv renv venv loop x (fun x ->
        insert_let x (Tint 32) (fun x ->
        insert_let (Ebinop (x, Op_cmp Cne, Vint (32, 0))) (Tint 1)
          (fun c -> Sif (c, void_exp tenv renv venv true y side_expr, Sbreak)))) in
      Sseq (Sloop body, nxt (Evalue Vundef) VOID)
  | Pfor (_, i, x, y, z) ->
      (* int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          let yy = Id.genid () in
          let id = new_var (Tint 32) in
          let venv' = add_var i id E.Tint venv in
          Sseq (Slet (yy, y, Sstore (Eaddr id, x,
            Sloop (Sif (Ebinop (Eload (Eaddr id), P.Op_cmp P.Cle, Evar yy),
              void_exp tenv venv' true z
                (Sstore (.Eaddr id,
                  Ebinop (Eload (Eaddr id), P.Op_add, Vint (32, 1)),
                  Sskip)),
                  Sbreak)))), nxt Eundef E.Tvoid))) *)
      assert false
  | Pbreak p ->
      if loop then Sbreak (* ignore nxt *)
      else error p "illegal use of 'break'"
  | Pletvar (_, x, None, y, z) ->
      exp tenv renv venv loop y (fun y yt ->
        insert_let y (transl_typ renv yt) (fun y ->
        let id = Id.genid () in (* new_var (transl_typ yt) in *)
        let venv = add_var x id yt venv in
        Slet (id, Tpointer (transl_typ renv yt),
          Ealloca (structured_type yt, transl_typ renv yt),
          Sseq (Sstore (Vvar id, y), exp tenv renv venv loop z nxt))))
  | Pletvar (_, x, Some t, Pnil _, z) ->
      (*
      let t, _ = find_record_type t env in
      let env, x = E.add_variable x t env in
      Eletvar (x, transl_typ t, Enull (transl_typ t), exp' env inloop z nxt)
      *)
      assert false
  | Pletvar (_, x, Some t, y, z) ->
      let t = find_type t tenv in
      typ_exp tenv renv venv loop y t (fun y ->
        insert_let y (transl_typ renv t) (fun y ->
        let id = Id.genid () in (* new_var (transl_typ t) in *)
        let venv = add_var x id t venv in
        Slet (id, Tpointer (transl_typ renv t),
          Ealloca (structured_type t, transl_typ renv t),
          Sseq (Sstore (Vvar id, y), exp tenv renv venv loop z nxt))))
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
    let venv, args = List.fold_left2 add_formal (venv, []) fn_args ts in

    (* Process the body *)
    let body = typ_exp tenv renv venv false fn_body t
      (fun e ->
        match t with
        | VOID ->
            Sreturn None
        | t ->
            insert_let e (transl_typ renv t) (fun e -> Sreturn (Some e))) in

    { fn_name = f;
      fn_rtyp = Some (transl_typ renv t); (* FIXME XXX *)
      fn_args = List.rev args;
      fn_body = body }
  in
  let venv = List.fold_left addfun venv funs in
  Sletrec (List.map (addfun2 venv) funs, exp tenv renv venv loop e nxt)

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
  let s = exp base_tenv base_renv base_venv false e (fun e t ->
    Slet (Id.genid (), transl_typ base_renv t, e, Sreturn (Some (Vint (32, 0))))) in
  { prog_body = s;
    prog_strings = [];
    prog_named = !named_structs }
