open Anf
open Format

let rec value pp = function
  | VUNDEF -> fprintf pp "undef"
  | VINT (1, 0) -> fprintf pp "false"
  | VINT (1, _) -> fprintf pp "true"
  | VINT (_, n) -> fprintf pp "%d" n
  | VNULL _ -> fprintf pp "null"
  | VVAR x -> fprintf pp "%a" Id.pp x
  | VLOAD x -> fprintf pp "@[(load@ %a)@]" Id.pp x

and pp_actuals pp = function
  | [] -> fprintf pp "()"
  | [x] -> value pp x
  | x :: xs ->
      fprintf pp "%a@ %a" value x pp_actuals xs

let cexp pp = function
  | VAL v -> value pp v
  | ALLOCA (_, t) -> fprintf pp "@[alloca@]"
  | MALLOC _ -> fprintf pp "@[malloc@]"
  | ARRAY_MALLOC (v1, v2) ->
      fprintf pp "@[array_malloc %a@ %a@]" value v1 value v2
  | LOAD v -> fprintf pp "@[load %a@]" value v
  | STORE (v1, v2) -> fprintf pp "@[store %a@ %a@]" value v1 value v2
  | BINOP (v1, _, v2) ->
      fprintf pp "@[%a@ op@ %a@]" value v1 value v2
  | CALL (x, vs) ->
      fprintf pp "@[%a@ %a@]" Id.pp x pp_actuals vs

let rec exp pp = function
  | DIE s -> fprintf pp "@[<hov 2>die@ %S@]" s
  | LET (x, _, e1, e2) ->
      fprintf pp "@[<hov 0>@[<hv 2>let %a =@ %a@] in@ %a@]"
        Id.pp x cexp e1 exp e2
  | IF (v, e1, e2) ->
      fprintf pp "@[<hov 0>if %a@ then %a@ else %a@]"
        value v exp e1 exp e2
  | RETURN c ->
      fprintf pp "@[%a@]"
        cexp c
  | LET_BLOCK (x, args, body, e) ->
      fprintf pp "@[<hov 0>@[<hv 2>let rec %a %a =@ %a@ in@]@ %a@]"
        Id.pp x pp_formals args exp body exp e
  | GOTO (x, args) ->
      fprintf pp "@[%a %a@]" Id.pp x pp_actuals args

and pp_formals pp = function
  | [] -> fprintf pp "()"
  | [x, _] -> Id.pp pp x
  | (x, _) :: xs ->
      fprintf pp "%a@ %a" Id.pp x pp_formals xs

let f p =
  fprintf Format.std_formatter "@[%a@\n@]" exp p.prog_body
