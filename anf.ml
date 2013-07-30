open Globals

type bin = 
  Parsetree.bin

type llvm_type =
  | Tint of int
  | Tarray of int * llvm_type
  | Tpointer of llvm_type
  | Tstruct of llvm_type array
  | Tnamedstruct of string

type signature = {
  sig_args : llvm_type array;
  sig_rtyp : llvm_type option
}

type value =
  | VUNDEF
  | VINT of int * int
  | VNULL of llvm_type
  | VVAR of Id.t
  | VLOAD of Id.t

type cexp =
  | VAL of value
  | ALLOCA of bool * llvm_type
  | MALLOC of llvm_type
  | ARRAY_MALLOC of value * value
  | LOAD of value
  | STORE of value * value
  | BINOP of value * bin * value
  | CALL of Id.t * value list
  | EXT_CALL of string * value list
  | GEP of value * value list
  | PTRTOINT of value

type exp =
  | DIE of string
  | LET of Id.t * llvm_type * cexp * exp
  | IF of value * exp * exp
  | RETURN of cexp
  | LET_BLOCK of Id.t * (Id.t * llvm_type) list * exp * exp
  | GOTO of Id.t * value list
  | LET_REC of (Id.t, llvm_type, exp) fundef list * exp

type prog = {
  prog_named : (string * llvm_type list) list;
  prog_strings : (Id.t * string) list;
  prog_body : exp
}

module S = Set.Make (Id)

let remove_list l s =
  List.fold_right S.remove l s

let fv_value = function
  | VUNDEF
  | VINT _
  | VNULL _ -> S.empty
  | VVAR x
  | VLOAD x -> S.singleton x

let fv_cexp = function
  | VAL v -> fv_value v
  | ALLOCA _
  | MALLOC _ -> S.empty
  | ARRAY_MALLOC (v1, v2) -> S.union (fv_value v1) (fv_value v2)
  | LOAD v -> fv_value v
  | STORE (v1, v2)
  | BINOP (v1, _, v2) -> S.union (fv_value v1) (fv_value v2)
  | CALL (_, vs)
  | EXT_CALL (_, vs) -> List.fold_left S.union S.empty (List.map fv_value vs)
  | GEP (v, vs) -> List.fold_left S.union S.empty (List.map fv_value (v :: vs))
  | PTRTOINT v -> fv_value v

let rec fv = function
  | DIE _ -> S.empty
  | LET (x, _, e1, e2) ->
      S.union (fv_cexp e1) (S.remove x (fv e2))
  | IF (v, e1, e2) ->
      S.union (fv e1) (S.union (fv e2) (fv_value v))
  | RETURN c ->
      fv_cexp c
  | LET_BLOCK (_, args, e1, e2) ->
      S.union (fv e2) (remove_list (List.map fst args) (fv e1))
  | GOTO (_, vs) ->
      List.fold_left S.union S.empty (List.map fv_value vs)
  | LET_REC (fundefs, e) ->
      S.union (fv e)
        (List.fold_left (fun s fundef ->
          S.union s (remove_list (List.map fst fundef.fn_args)
            (fv fundef.fn_body))) S.empty fundefs)

let rec fc = function
  | DIE _ -> S.empty
  | LET (_, _, CALL (x, _), e2) ->
      S.add x (fc e2)
  | LET (_, _, _, e2) ->
      fc e2
  | IF (_, e1, e2) ->
      S.union (fc e1) (fc e2)
  | RETURN (CALL (x, _)) ->
      S.singleton x
  | RETURN _ ->
      S.empty
  | LET_BLOCK (_, _, e1, e2) ->
      S.union (fc e1) (fc e2)
  | GOTO _ ->
      S.empty
  | LET_REC (fundefs, e) ->
      remove_list (List.map (fun fundef -> fundef.fn_name) fundefs) (fc e)
