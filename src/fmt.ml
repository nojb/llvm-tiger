open Format
open Tabs

let string_of_binary_operation = function
  | Op_add -> "+"
  | _ -> "<binop>"

let rec declaration ppf d =
  match d with
  | Dvar (s, _, e) ->
      fprintf ppf "@[<2>var %s := %a@]" s.desc expression e
  | _ ->
      assert false

and variable ppf v =
  match v.desc with
  | Vsimple s -> pp_print_string ppf s.desc
  | _ -> assert false

and expression ppf e =
  match e.desc with
  | Eint n -> pp_print_string ppf (Int32.to_string n)
  | Estring s -> fprintf ppf "%S" s
  | Enil -> pp_print_string ppf "nil"
  | Evar v -> variable ppf v
  | Ebinop (e1, op, e2) ->
      fprintf ppf "@[<2>%a %s@ %a@]" expression e1 (string_of_binary_operation op) expression e2
  | Eassign (v, e) ->
      fprintf ppf "@[<2>%a := %a@]" variable v expression e
  | Ecall (s, el) ->
      let arguments = pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") expression in
      fprintf ppf "@[%s(%a)@]" s.desc arguments el
  | Eseq el ->
      fprintf ppf "@[(%a)@]" (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ";@ ") expression) el
  | Emakearray (ty, e1, e2) ->
      fprintf ppf "@[<2>%s[%a] of@ %a@]" ty.desc expression e1 expression e2
  | Emakerecord _ ->
      assert false
  | Eif (e1, e2, None) ->
      fprintf ppf "@[if@ %a@ then@ %a]" expression e1 expression e2
  | Eif (e1, e2, Some e3) ->
      fprintf ppf "@[if@ %a@ then@ %a@ else@ %a@]" expression e1 expression e2 expression e3
  | Ewhile (e1, e2) ->
      fprintf ppf "@[while@ %a@ do@ %a@]" expression e1 expression e2
  | Efor _ ->
      assert false
  | Ebreak ->
      pp_print_string ppf "break"
  | Elet (ds, e) ->
      let declarations = pp_print_list ~pp_sep:pp_print_cut declaration in
      fprintf ppf "@[let @[<v>%a@] in@ %a@ end@]" declarations ds expression e
