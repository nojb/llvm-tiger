type cmp_op =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_cmp of cmp_op


type pos =
  Lexing.position

type pos_string = {
  s : string;
  p : Lexing.position
}

type typ =
  | Tname of pos_string
  | Tarray of pos_string
  | Trecord of (pos_string * pos_string) list

type var =
  | Vsimple of pos_string
  | Vsubscript of pos * var * exp
  | Vfield of pos * var * pos_string

and exp =
  | Eunit of pos
  | Eint of pos * int
  | Estring of pos * string
  | Enil of pos
  | Evar of pos * var
  | Ebinop of pos * exp * bin * exp
  | Eassign of pos * var * exp
  | Ecall of pos * pos_string * exp list
  | Eseq of pos * exp * exp
  | Emakearray of pos * pos_string * exp * exp
  | Emakerecord of pos * pos_string * (pos_string * exp) list
  | Eif of pos * exp * exp * exp
  | Ewhile of pos * exp * exp
  | Efor of pos * pos_string * exp * exp * exp
  | Ebreak of pos
  | Elet of pos * dec * exp

and dec =
  | Dtypes of (pos_string * typ) list
  | Dfuns of fundef list
  | Dvar of pos_string * pos_string option * exp

and fundef = {
  fn_name : pos_string;
  fn_rtyp : pos_string option;
  fn_args : (pos_string * pos_string) list;
  fn_body : exp
}

let exp_p = function
  | Eunit p
  | Eint (p, _)
  | Estring (p, _)
  | Enil p
  | Evar (p, _)
  | Ebinop (p, _, _, _)
  | Eassign (p, _, _)
  | Ecall (p, _, _)
  | Eseq (p, _, _)
  | Emakearray (p, _, _, _)
  | Emakerecord (p, _, _)
  | Eif (p, _, _, _)
  | Ewhile (p, _, _)
  | Efor (p, _, _, _, _)
  | Ebreak p
  | Elet (p, _, _) -> p

let var_p = function
  | Vsimple s -> s.p
  | Vsubscript (p, _, _)
  | Vfield (p, _, _) -> p

module S = Set.Make (String)

let remove_list l s =
  List.fold_right S.remove l s

let union_list l =
  List.fold_left S.union S.empty l

let rec fc = function
  | Eunit _
  | Eint _
  | Estring _
  | Enil _ -> S.empty
  | Evar (_, v) -> fc_var v
  | Ebinop (_, e1, _, e2) -> S.union (fc e1) (fc e2)
  | Eassign (_, v, e) -> S.union (fc_var v) (fc e)
  | Ecall (_, x, es) ->
      S.add x.s (union_list (List.map fc es))
  | Eseq (_, e1, e2)
  | Emakearray (_, _, e1, e2) -> S.union (fc e1) (fc e2)
  | Emakerecord (_, _, xes) ->
      union_list (List.map (fun (_, e) -> fc e) xes)
  | Eif (_, e1, e2, e3) -> S.union (fc e1) (S.union (fc e2) (fc e3))
  | Ewhile (_, e1, e2) -> S.union (fc e1) (fc e2)
  | Efor (_, _, e1, e2, e3) -> S.union (fc e1) (S.union (fc e2) (fc e3))
  | Ebreak _ -> S.empty
  | Elet (_, Dvar (_, _, e1), e2) -> S.union (fc e1) (fc e2)
  | Elet (_, Dfuns fundefs, e) ->
      remove_list (List.map (fun fundef -> fundef.fn_name.s) fundefs)
        (S.union (fc e) (union_list (List.map
          (fun fundef -> fc fundef.fn_body) fundefs)))
  | Elet (_, Dtypes _, e) -> fc e

and fc_var = function
  | Vsimple _ -> S.empty
  | Vsubscript (_, v, e) -> S.union (fc_var v) (fc e)
  | Vfield (_, v, _) -> fc_var v

let rec fv = function
  | Eunit _
  | Eint _
  | Estring _
  | Enil _ -> S.empty
  | Evar (_, v) -> fv_var v
  | Ebinop (_, e1, _, e2) -> S.union (fv e1) (fv e2)
  | Eassign (_, v, e) -> S.union (fv_var v) (fv e)
  | Ecall (_, _, es) -> union_list (List.map fv es)
  | Eseq (_, e1, e2)
  | Emakearray (_, _, e1, e2) -> S.union (fv e1) (fv e2)
  | Emakerecord (_, _, xes) ->
      List.fold_left S.union S.empty (List.map (fun (_, e) -> fv e) xes)
  | Eif (_, e1, e2, e3) -> S.union (fv e1) (S.union (fv e2) (fv e3))
  | Ewhile (_, e1, e2) -> S.union (fv e1) (fv e2)
  | Efor (_, i, e1, e2, e3) ->
      S.union (fv e1) (S.union (fv e2) (S.remove i.s (fv e3)))
  | Ebreak _ -> S.empty
  | Elet (_, Dvar (x, _, e1), e2) -> S.union (fv e1) (S.remove x.s (fv e2))
  | Elet (_, Dfuns fundefs, e) ->
      S.union (fv e)
        (union_list (List.map (fun fundef ->
          remove_list (List.map (fun (x, _) -> x.s) fundef.fn_args)
            (fv fundef.fn_body)) fundefs))
  | Elet (_, Dtypes _, e) -> fv e

and fv_var = function
  | Vsimple x -> S.singleton x.s
  | Vsubscript (_, v, e) -> S.union (fv_var v) (fv e)
  | Vfield (_, v, _) -> fv_var v

let rec triggers = function
  | Eunit _
  | Eint _
  | Estring _
  | Enil _ -> false
  | Evar (_, v) -> triggers_var v
  | Ebinop (_, e1, _, e2) -> triggers e1 || triggers e2
  | Eassign (_, v, e) -> triggers_var v || triggers e
  | Ecall _ -> true
  | Eseq (_, e1, e2) -> triggers e1 || triggers e2
  | Emakearray _
  | Emakerecord _ -> true
  | Eif (_, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Ewhile (_, e1, e2) -> triggers e1 || triggers e2
  | Efor (_, _, e1, e2, e3) -> triggers e1 || triggers e2 || triggers e3
  | Ebreak _ -> false
  | Elet (_, Dvar (_, _, e1), e2) -> triggers e1 || triggers e2
  | Elet (_, Dfuns _, e)
  | Elet (_, Dtypes _, e) -> triggers e

and triggers_var = function
  | Vsimple _ -> false
  | Vsubscript (_, v, e) -> triggers_var v || triggers e
  | Vfield (_, v, _) -> triggers_var v

