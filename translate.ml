open Globals
open Parsetree
open Typedtree
open IL

module M = Map.Make (String)

exception Error of Lexing.position * string

let error p =
  Printf.ksprintf (fun message -> raise (Error (p, message)))

let gentmp () =
  Printf.sprintf "tmp__%d" (unique ())

let genlabel () =
  L (Printf.sprintf "block__%d" (unique ()))

module LM = Map.Make (Label)

type env = {
  venv : llvm_type M.t;
  lenv : block LM.t ref;
  curr : label
}

let new_env () = {
  venv = M.empty;
  lenv = ref LM.empty;
  curr = genlabel ()
}

(* let named_structs : (string * llvm_type list) list ref = ref [] *)

let rec transl_typ t =
  assert false
  (* let visited : string list ref = ref [] in
  let rec loop t =
    match t with
    | INT -> Tint 32
    | VOID -> Tint 32
    | STRING -> Tpointer (Tint 8)
    | ARRAY (_, t) -> (* { i32, i32, [0 x t] }* *)
        Tpointer (Tstruct [| Tint 32; Tint 32; Tarray (0, transl_typ t) |])
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
  in loop t *)

(* let rec structured_type t =
  match t with
  | PLACE _ -> assert false
  | STRING
  | ARRAY _
  | RECORD _ -> true
  | _ -> false *)

let array_exists p a =
  let rec loop i =
    if i >= Array.length a then false
    else if p a.(i) then true
    else loop (i+1)
  in loop 0

let rec triggers (e : Typedtree.exp) : bool =
  match e with
  | TCint _
  | TCstring _
  | TCnil _ -> false
  | Tvar (v) -> triggers_var v
  | Tbinop (e1, _, e2) -> triggers e1 || triggers e2
  | Tassign (v, e) -> triggers_var v || triggers e
  | Tcall _ -> true
  | Tseq (es) -> List.exists triggers es
  | Tmakearray _
  | Tmakerecord _ -> true
  | Tif (e1, e2, e3, _) -> triggers e1 || triggers e2 || triggers e3
  | Twhile (e1, e2) -> triggers e1 || triggers e2
  | Tfor (_, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Tbreak -> false
  | Tletvar (_, _, _, _, e1, e2) -> triggers e1 || triggers e2
  | Tletfuns (_, e) -> triggers e

and triggers_var = function
  | TVlocal _
  | TVnonLocal _ -> false
  | TVsubscript (_, v, e) -> triggers_var v || triggers e
  | TVfield (_, v, _) -> triggers_var v

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

(* These utility functions are used in the processing of function definitions *)

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

let load_type = function
  | Tpointer t -> t
  | _ -> assert false

let load (v, t) nxt =
  let tmp = gentmp () in
  Load (tmp, v, nxt (Var tmp, load_type t))

let nil =
  Int (32, 0), Tint 32

let store (v, _) (p, _) nxt = (* does not check the types XXX *)
  Store (v, p, nxt nil)

let gep (v, t) vts nxt =
  assert false
  (* let tmp = gentmp () in
  Gep (tmp, v, vs, nxt (Var tmp, ...)) *)

let binop op (v1, t1) (v2, t2) nxt =
  let tmp = gentmp () in
  match op, t1, t2 with
  | Add, Tint n, Tint m 
  | Sub, Tint n, Tint m 
  | Mul, Tint n, Tint m 
  | Div, Tint n, Tint m ->
      assert (n = m);
      Binary (tmp, op, v1, v2, nxt (Var tmp, Tint n))
  | Icmp _, Tint n, Tint m when n = m ->
      Binary (tmp, op, v1, v2, nxt (Var tmp, Tint 1))

let call _ =
  assert false

let phi _ =
  assert false

let cond_br (c, _) yay nay = (* does not check the types XXX *)
  Condbr (c, yay, nay)

let array_length v nxt =
  gep v [ Int (32, 0); Int (32, 1) ] (fun l -> load l nxt)

let array_index lnum v x nxt =
  assert false
  (* array_length v (fun l ->
  insert_let (BINOP (x, Op_cmp Cle, l)) (Tint 1) (fun c ->
  CHECK (c, insert_let (GEP (v, [VINT (32, 0); VINT (32, 2); x])) t' nxt,
    Printf.sprintf "Runtime error: index out of bounds in line %d\n"
    p.Lexing.pos_lnum))) *)

let record_index lnum v i nxt =
  assert false
  (* insert_let (PTRTOINT v) (Tint 64) (fun ptr ->
  insert_let (BINOP (ptr, Op_cmp Cne, VINT (64, 0))) (Tint 1) (fun c ->
  CHECK (c, insert_let (GEP (v, [ VINT (32, 0); VINT (32, i+1) ])) tx nxt,
    Printf.sprintf "field access to nil record in line %d"
    p.Lexing.pos_lnum))) *)

(* Main typechecking/compiling functions *)

let save triggers (v, t) (nxt : value * llvm_type -> block) =
  if triggers then
    match v with
    | Loadvar _ -> nxt (v, load_type t)
    | _ ->
        let id = gentmp () in
        Alloca (id, t, true,
        Store (Var id, v,
        nxt (Loadvar id, t)))
  else
    nxt (v, t)

let find x env =
  M.find x env.venv

let new_block env lbl b =
  env.lenv := LM.add lbl b !(env.lenv)

let rec var env lbreak v (nxt : value * llvm_type -> block) =
  match v with
  | TVlocal x (* XXX FIXME immutable *) ->
      nxt (Loadvar x, load_type (find x env))
  | TVnonLocal (dlvl, idx) ->
      assert false
  | TVsubscript (lnum, v, x) ->
      var env lbreak v (fun v ->
      save (triggers x) v (fun v ->
      exp env lbreak x (fun x ->
      array_index lnum v x (fun v ->
      load v nxt))))
  | TVfield (lnum, v, i) ->
      var env lbreak v (fun v ->
      record_index lnum v i (fun v ->
      load v nxt))

and exp env lbreak e (nxt : value * llvm_type -> block) : block =
  match e with
  | TCint (n) ->
      nxt (Int (32, n), Tint 32)
  (* | Pstring (_, s) ->
      nxt (Vstring s) STRING *)
  | TCnil t ->
      nxt (Null (transl_typ t), transl_typ t)
  | Tvar (v) ->
      var env lbreak v nxt
  | Tbinop (x, Op_add, y) ->
      exp env lbreak x (fun x ->
      exp env lbreak y (fun y ->
      binop Add x y nxt))
  | Tbinop (x, Op_sub, y) ->
      exp env lbreak x (fun x ->
      exp env lbreak y (fun y ->
      binop Sub x y nxt))
  | Tbinop (x, Op_mul, y) ->
      exp env lbreak x (fun x ->
      exp env lbreak y (fun y ->
      binop Mul x y nxt))
  | Tbinop (x, Op_div, y) ->
      exp env lbreak x (fun x ->
      exp env lbreak y (fun y ->
      binop Div x y nxt))
  | Tbinop (x, Op_cmp Ceq, y) ->
      exp env lbreak x (fun x ->
      exp env lbreak y (fun y ->
      binop (Icmp Eq) x y nxt))
  | Tbinop _ ->
      failwith "binop not implemented"
  (* | Tassign (TVsimple x, e) ->
      exp env lbreak e (fun e -> store e (Var x, M.find x env) nxt) *)
  | Tassign (TVsubscript (lnum, v, e1), e2) ->
      var env lbreak v (fun v ->
      save (triggers e1 || triggers e2) v (fun v ->
      exp env lbreak e1 (fun e1 ->
      array_index lnum v e1 (fun v ->
      exp env lbreak e2 (fun e2 -> store e2 v nxt)))))
  | Tassign (TVfield (lnum, v, i), e) ->
      var env lbreak v (fun v ->
      save (triggers e) v (fun v ->
      record_index lnum v i (fun v ->
      exp env lbreak e (fun e -> store e v nxt))))
  | Tcall (x, xs) ->
      let rec bind ys = function
        | [] ->
            call (Function x) (List.rev ys) nxt
        | (x, is_ptr) :: xs ->
            exp env lbreak x (fun x ->
              save (is_ptr && List.exists triggers (List.map fst xs)) x (fun x ->
              bind (x :: ys) xs))
      in bind [] xs
  | Tseq (xs) ->
      let rec bind = function
        | []      -> nxt nil
        | [x]     -> exp env lbreak x nxt
        | x :: x' -> exp env lbreak x (fun _ -> bind x')
      in
      bind xs
  | Tmakearray (y, z) ->
      assert false
      (* let t, t' = find_array_type x tenv in
      int_exp tenv renv venv loop y (fun y ->
      typ_exp tenv renv venv loop z t' (fun z ->
      insert_let (ARRAY_MALLOC (y, z)) (transl_typ renv t)
        (fun arr -> nxt arr t))) *)
  | Tmakerecord (x, xts) ->
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
        | _ ->
            assert false
      in bind [] (xts, ts) *)
  (* | Pif (_, P.Ecmp (x, op, y), z, None) ->
      int_exp tenv venv looping x (fun x ->
        int_exp tenv venv looping y (fun y ->
          .Sseq (T.Sif (Ebinop (x, op, y),
            void_exp tenv venv looping z Sskip, Sskip),
            nxt Eundef E.Tvoid))) *)
  | Tif (x, y, z, true) -> (* result is void *)
      let cont = genlabel () in
      let yay  = genlabel () in
      let nay  = genlabel () in
      new_block env yay (exp env lbreak y (fun _ -> Br cont));
      new_block env nay (exp env lbreak z (fun _ -> Br cont));
      new_block env cont (nxt nil);
      exp env lbreak x (fun x ->
        binop (Icmp Ne) x (Int (32, 0), Tint 32) (fun c ->
        cond_br c yay nay))
  | Tif (x, y, z, false) ->
      let cont = genlabel () in
      let yay  = genlabel () in
      let nay  = genlabel () in
      let yy   = ref nil in
      let zz   = ref nil in
      new_block env yay (exp env lbreak y (fun y -> yy := y; Br cont));
      new_block env nay (exp env lbreak z (fun z -> zz := z; Br cont));
      new_block env cont (phi [yay, !yy; nay, !zz] nxt);
      exp env lbreak x (fun x ->
        binop (Icmp Ne) x (Int (32, 0), Tint 32) (fun c -> cond_br c yay nay))
  | Twhile (x, y) ->
      let cont = genlabel () in
      let test = genlabel () in
      let body = genlabel () in
      new_block env cont (nxt nil);
      new_block env test (exp env lbreak x (fun x ->
        binop (Icmp Ne) x (Int (32, 0), Tint 32) (fun c ->
        cond_br c body cont)));
      new_block env body (exp env (Some cont) y (fun _ -> Br test));
      Br test
  | Tfor (i, x, y, z) ->
      let cont = genlabel () in
      let test = genlabel () in
      let body = genlabel () in
      let x1 = ref nil in
      new_block env cont (nxt nil);
      new_block env body (exp env (Some cont) z (fun _ ->
        binop Add (Var i, Tint 32) (Int (32, 1), Tint 32) (fun i1 -> x1 := i1; Br test)));
      exp env lbreak x (fun x ->
      exp env lbreak y (fun y ->
        new_block env test (phi [env.curr, x; body, !x1] (fun i ->
          binop (Icmp Le) i y (fun c ->
          cond_br c test cont)));
        Br test))
  | Tbreak ->
      begin match lbreak with
        Some cont -> Br cont (* ignore nxt *)
      | None -> assert false
      end
  | Tletvar (x, acc, is_ptr, ty, y, z) ->
      begin match !acc with
      | Local ->
          assert false
          (* exp env lbreak y (fun y ->
          alloca is_ptr (transl_typ ty) (fun a ->
          store y a (exp (add x (transl_typ ty) env) lbreak z nxt))) *)
          (* LET (id, Tpointer (transl_typ renv yt),
          Alloca (x, is_ptr, transl_typ yt,
          Store (Var x, y,
          exp lbreak z nxt)))) *)
      | NonLocal _ ->
          assert false
      end
  | Tletfuns (fundefs, e) ->
      let_funs lbreak fundefs e nxt

and let_funs lbreak fundefs e nxt =
  assert false
  (* let addfun venv fn =
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
  LET_REC (List.map (addfun2 venv) funs, exp tenv renv venv loop e nxt) *)

  (*
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
    *)

let program e =
  let env = new_env () in
  let s = exp env None e (fun _ -> Ret (Some (Int (32, 0)))) in
  s
  (* { prog_body = s;
    prog_strings = [];
    prog_funs = [];
    prog_named = !named_structs } *)
