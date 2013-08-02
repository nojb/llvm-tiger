open Printf
open IL

let pr_value oc = function
  | Int (_, n)  -> fprintf oc "$%d" n
  | Null _      -> fprintf oc "null"
  | Global n
  | Function n  -> fprintf oc "@%s" n
  | Var n       -> fprintf oc "%%%s" n
  | Loadvar n   -> fprintf oc "(%%%s)" n

let rec pr_block oc = function
  | Load (dst, v, nxt) ->
      fprintf oc "\tload\t%a" pr_value v;
      pr_block oc nxt
  | Store (src, dst, nxt) ->
      fprintf oc "\tstore\t%a, %a" pr_value dst pr_value src;
      pr_block oc nxt
  | Condbr (v, L lbl1, L lbl2) ->
      fprintf oc "\tcond_br\t%a, %s, %s" pr_value v lbl1 lbl2
  | Br (L lbl) ->
      fprintf oc "\tbr\t\t%s" lbl
  | Ret None ->
      fprintf oc "\tret"
  | Ret (Some v) ->
      fprintf oc "\tret\t%a" pr_value v
