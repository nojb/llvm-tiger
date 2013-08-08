open Globals

type cmp_op =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_and | Op_or | Op_cmp of cmp_op


type pos =
  Lexing.position

type pos_string = {
  s : string;
  p : Lexing.position
}

type typ =
  | PTname of pos_string
  | PTarray of pos_string
  | PTrecord of (pos_string * pos_string) list

type var =
  | PVsimple of pos_string
  | PVsubscript of pos * var * exp
  | PVfield of pos * var * pos_string

and exp =
  | Pint of pos * int
  | Pstring of pos * string
  | Pnil of pos
  | Pvar of pos * var
  | Pbinop of pos * exp * bin * exp
  | Passign of pos * var * exp
  | Pcall of pos * pos_string * exp list
  | Pseq of pos * exp list
  | Pmakearray of pos * pos_string * exp * exp
  | Pmakerecord of pos * pos_string * (pos_string * exp) list
  | Pif of pos * exp * exp * exp option
  | Pwhile of pos * exp * exp
  | Pfor of pos * pos_string * exp * exp * exp
  | Pbreak of pos
  | Pletvar of pos * pos_string * pos_string option * exp * exp
  | Pletfuns of pos * fundef list * exp
  | Plettype of pos * (pos_string * typ) list * exp

and fundef = {
  fn_name : pos_string;
  fn_rtyp : pos_string option;
  fn_args : (pos_string * pos_string) list;
  fn_body : exp
}

let exp_p = function
  | Pint (p, _)
  | Pstring (p, _)
  | Pnil p
  | Pvar (p, _)
  | Pbinop (p, _, _, _)
  | Passign (p, _, _)
  | Pcall (p, _, _)
  | Pseq (p, _)
  | Pmakearray (p, _, _, _)
  | Pmakerecord (p, _, _)
  | Pif (p, _, _, _)
  | Pwhile (p, _, _)
  | Pfor (p, _, _, _, _)
  | Pbreak p
  | Pletvar (p, _, _, _, _)
  | Pletfuns (p, _, _)
  | Plettype (p, _, _) -> p

let var_p = function
  | PVsimple s -> s.p
  | PVsubscript (p, _, _)
  | PVfield (p, _, _) -> p

module S = Set.Make (String)

let remove_list l s =
  List.fold_right S.remove l s

let union_list l =
  List.fold_left S.union S.empty l

let rec fc = function
  | Pint _
  | Pstring _
  | Pnil _ -> S.empty
  | Pvar (_, v) -> fc_var v
  | Pbinop (_, e1, _, e2) -> S.union (fc e1) (fc e2)
  | Passign (_, v, e) -> S.union (fc_var v) (fc e)
  | Pcall (_, x, es) ->
      S.add x.s (union_list (List.map fc es))
  | Pseq (_, es) ->
      union_list (List.map fc es)
  | Pmakearray (_, _, e1, e2) -> S.union (fc e1) (fc e2)
  | Pmakerecord (_, _, xes) ->
      union_list (List.map (fun (_, e) -> fc e) xes)
  | Pif (_, e1, e2, None) -> S.union (fc e1) (fc e2)
  | Pif (_, e1, e2, Some e3) -> S.union (fc e1) (S.union (fc e2) (fc e3))
  | Pwhile (_, e1, e2) -> S.union (fc e1) (fc e2)
  | Pfor (_, _, e1, e2, e3) -> S.union (fc e1) (S.union (fc e2) (fc e3))
  | Pbreak _ -> S.empty
  | Pletvar (_, _, _, e1, e2) -> S.union (fc e1) (fc e2)
  | Pletfuns (_, fundefs, e) ->
      remove_list (List.map (fun fundef -> fundef.fn_name.s) fundefs)
        (S.union (fc e) (union_list (List.map
          (fun fundef -> fc fundef.fn_body) fundefs)))
  | Plettype (_, _, e) -> fc e

and fc_var = function
  | PVsimple _ -> S.empty
  | PVsubscript (_, v, e) -> S.union (fc_var v) (fc e)
  | PVfield (_, v, _) -> fc_var v

let rec fv = function
  | Pint _
  | Pstring _
  | Pnil _ -> S.empty
  | Pvar (_, v) -> fv_var v
  | Pbinop (_, e1, _, e2) -> S.union (fv e1) (fv e2)
  | Passign (_, v, e) -> S.union (fv_var v) (fv e)
  | Pcall (_, _, es)
  | Pseq (_, es) ->
      List.fold_left S.union S.empty (List.map fv es)
  | Pmakearray (_, _, e1, e2) -> S.union (fv e1) (fv e2)
  | Pmakerecord (_, _, xes) ->
      List.fold_left S.union S.empty (List.map (fun (_, e) -> fv e) xes)
  | Pif (_, e1, e2, None) -> S.union (fv e1) (fv e2)
  | Pif (_, e1, e2, Some e3) -> S.union (fv e1) (S.union (fv e2) (fv e3))
  | Pwhile (_, e1, e2) -> S.union (fv e1) (fv e2)
  | Pfor (_, i, e1, e2, e3) ->
      S.union (fv e1) (S.union (fv e2) (S.remove i.s (fv e3)))
  | Pbreak _ -> S.empty
  | Pletvar (_, x, _, e1, e2) -> S.union (fv e1) (S.remove x.s (fv e2))
  | Pletfuns (_, fundefs, e) ->
      S.union (fv e)
        (union_list (List.map (fun fundef ->
          remove_list (List.map (fun (x, _) -> x.s) fundef.fn_args)
            (fv fundef.fn_body)) fundefs))
  | Plettype (_, _, e) -> fv e

and fv_var = function
  | PVsimple x -> S.singleton x.s
  | PVsubscript (_, v, e) -> S.union (fv_var v) (fv e)
  | PVfield (_, v, _) -> fv_var v

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

