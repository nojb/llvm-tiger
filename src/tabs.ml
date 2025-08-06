type 'a loc =
  {
    desc: 'a;
    loc: Lexing.position;
  }

type comparison =
  | Ceq | Cle | Cge | Cne | Clt | Cgt

type bin =
  | Op_add | Op_sub | Op_mul | Op_div
  | Op_cmp of comparison

type ident =
  string loc

type typ =
  | Tname of ident
  | Tarray of ident
  | Trecord of (ident * ident) list

type var =
  var_ loc

and var_ =
  | Vsimple of ident
  | Vsubscript of var * exp
  | Vfield of var * ident

and exp =
  exp_ loc

and exp_ =
  | Eint of int64
  | Estring of string
  | Enil
  | Evar of var
  | Ebinop of exp * bin * exp
  | Eassign of var * exp
  | Ecall of  ident * exp list
  | Eseq of exp list
  | Earray of ident * exp * exp
  | Erecord of ident * (ident * exp) list
  | Eif of exp * exp * exp option
  | Ewhile of exp * exp
  | Efor of ident * exp * exp * exp
  | Ebreak
  | Elet of dec list * exp

and dec =
  | Dtype of ident * typ
  | Dfun of fundef
  | Dvar of ident * ident option * exp

and fundef =
  { fn_name: ident;
    fn_rtyp: ident option;
    fn_args: (ident * ident) list;
    fn_body: exp }

type program =
  {
    name: string;
    body: exp;
  }
(*
module S = Set.Make (String)

let remove_list l s =
  List.fold_right S.remove l s

let union_list l =
  List.fold_left S.union S.empty l

let rec fv e =
  match e.edesc with
  | Eunit
  | Eint _
  | Estring _
  | Enil -> S.empty
  | Evar v -> fv_var v
  | Ebinop (e1, _, e2) -> S.union (fv e1) (fv e2)
  | Eassign (v, e) -> S.union (fv_var v) (fv e)
  | Ecall (_, es) -> union_list (List.map fv es)
  | Eseq (e1, e2)
  | Emakearray (_, e1, e2) -> S.union (fv e1) (fv e2)
  | Emakerecord (_, xes) ->
      List.fold_left S.union S.empty (List.map (fun (_, e) -> fv e) xes)
  | Eif (e1, e2, e3) -> S.union (fv e1) (S.union (fv e2) (fv e3))
  | Ewhile (e1, e2) -> S.union (fv e1) (fv e2)
  | Efor (i, e1, e2, e3) ->
      S.union (fv e1) (S.union (fv e2) (S.remove i.s (fv e3)))
  | Ebreak -> S.empty
  | Elet (Dvar (x, _, e1), e2) -> S.union (fv e1) (S.remove x.s (fv e2))
  | Elet (Dfuns fundefs, e) ->
      S.union (fv e)
        (union_list (List.map (fun fundef ->
             remove_list (List.map (fun (x, _) -> x.s) fundef.fn_args)
               (fv fundef.fn_body)) fundefs))
  | Elet (Dtypes _, e) -> fv e

and fv_var v =
  match v.vdesc with
  | Vsimple x -> S.singleton x.s
  | Vsubscript (v, e) -> S.union (fv_var v) (fv e)
  | Vfield (v, _) -> fv_var v *)
