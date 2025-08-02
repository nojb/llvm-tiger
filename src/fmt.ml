open Format
open Tabs

let string_of_binary_operation = function
  | Op_add -> "+"
  | _ -> "<binop>"

let rec declaration ppf d =
  match d with
  | Dvar (s, _, e) ->
      fprintf ppf "@[<2>var %s := %a@]" s.s expression e
  | _ ->
      assert false

and variable ppf v =
  match v.vdesc with
  | Vsimple s -> pp_print_string ppf s.s
  | _ -> assert false

and expression ppf e =
  match e.edesc with
  | Eunit -> pp_print_string ppf "()"
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
      fprintf ppf "@[%s(%a)@]" s.s arguments el
  | Eseq _ ->
      let rec loop e el =
        match e.edesc, el with
        | Eseq (e1, e2), _ ->
            loop e1 (e2 :: el)
        | _, [] ->
            expression ppf e
        | _, e' :: el ->
            fprintf ppf "%a;@ " expression e;
            loop e' el
      in
      fprintf ppf "@[(";
      loop e [];
      fprintf ppf ")@]"
  | Emakearray (ty, e1, e2) ->
      fprintf ppf "@[<2>%s[%a] of@ %a@]" ty.s expression e1 expression e2
  | Emakerecord _ ->
      assert false
  | Eif (e1, e2, e3) ->
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
