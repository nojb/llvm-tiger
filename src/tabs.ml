(* The MIT License (MIT)

   Copyright (c) 2013-2016 Nicolas Ojeda Bar <n.oje.bar@gmail.com>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE. *)

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

module Ident = struct
  include String
  let print ppf s = Format.pp_print_string ppf s
end

type comparison =
  | Ceq | Cneq | Clt | Cgt | Cle | Cge

type array_kind =
  | Paddrarray | Pintarray

type primitive =
    Pidentity
  | Pignore
  (* | Ploc of loc_kind *)
  (* Globals *)
  | Pgetglobal of Ident.t
  | Psetglobal of Ident.t
  (* Operations on heap blocks *)
  | Pmakeblock of int
  | Pfield of int
  | Psetfield of int
    (* External call *)
  (* | Pccall of Primitive.description *)
  (* Boolean operations *)
  | Psequand | Psequor | Pnot
  (* Integer operations *)
  | Pnegint | Paddint | Psubint | Pmulint | Pdivint | Pmodint
  | Pandint | Porint | Pxorint
  | Plslint | Plsrint | Pasrint
  | Pintcomp of comparison
  | Poffsetint of int
  | Poffsetref of int
  (* String operations *)
  | Pstringlength | Pstringrefu | Pstringsetu | Pstringrefs | Pstringsets
  (* Array operations *)
  | Pmakearray of array_kind
  | Parraylength of array_kind
  | Parrayrefu of array_kind
  | Parraysetu of array_kind
  | Parrayrefs of array_kind
  | Parraysets of array_kind
  (* (\* Bitvect operations *\) *)
  (* | Pbittest *)
  (* (\* Compile time constants *\) *)
  (* | Pctconst of compile_time_constant *)

(* type structured_constant = *)
(*   | Const_base of constant *)
(*   | Const_pointer of int *)
(*   | Const_block of int * structured_constant list *)
(*   | Const_immstring of string *)

type lambda =
  | Lvar of Ident.t
  | Lconst of nativeint
  (* | Lconst of structured_constant *)
  | Lapply of Ident.t * lambda list
  | Llet of Ident.t * lambda * lambda
  | Lletrec of (Ident.t * Ident.t list * lambda) list * lambda
  | Lprim of primitive * lambda list
  | Lifthenelse of lambda * lambda * lambda
  | Lsequence of lambda * lambda
  | Lwhile of lambda * lambda
  | Lfor of Ident.t * lambda * lambda * lambda
  | Lassign of Ident.t * lambda
  (* | Levent of lambda * lambda_event *)

open Format

let array_kind = function
  | Paddrarray -> "addr"
  | Pintarray -> "int"

let primitive ppf = function
  | Pidentity -> fprintf ppf "id"
  | Pignore -> fprintf ppf "ignore"
  | Pgetglobal id -> fprintf ppf "global %a" Ident.print id
  | Psetglobal id -> fprintf ppf "setglobal %a" Ident.print id
  | Pmakeblock(tag) -> fprintf ppf "makeblock %i" tag
  | Pfield n -> fprintf ppf "field %i" n
  | Psetfield(n) ->
      fprintf ppf "setfield %i" n
  (* | Pccall p -> fprintf ppf "%s" p.prim_name *)
  | Psequand -> fprintf ppf "&&"
  | Psequor -> fprintf ppf "||"
  | Pnot -> fprintf ppf "not"
  | Pnegint -> fprintf ppf "~"
  | Paddint -> fprintf ppf "+"
  | Psubint -> fprintf ppf "-"
  | Pmulint -> fprintf ppf "*"
  | Pdivint -> fprintf ppf "/"
  | Pmodint -> fprintf ppf "mod"
  | Pandint -> fprintf ppf "and"
  | Porint -> fprintf ppf "or"
  | Pxorint -> fprintf ppf "xor"
  | Plslint -> fprintf ppf "lsl"
  | Plsrint -> fprintf ppf "lsr"
  | Pasrint -> fprintf ppf "asr"
  | Pintcomp(Ceq) -> fprintf ppf "=="
  | Pintcomp(Cneq) -> fprintf ppf "!="
  | Pintcomp(Clt) -> fprintf ppf "<"
  | Pintcomp(Cle) -> fprintf ppf "<="
  | Pintcomp(Cgt) -> fprintf ppf ">"
  | Pintcomp(Cge) -> fprintf ppf ">="
  | Poffsetint n -> fprintf ppf "%i+" n
  | Poffsetref n -> fprintf ppf "+:=%i"n
  | Pstringlength -> fprintf ppf "string.length"
  | Pstringrefu -> fprintf ppf "string.unsafe_get"
  | Pstringsetu -> fprintf ppf "string.unsafe_set"
  | Pstringrefs -> fprintf ppf "string.get"
  | Pstringsets -> fprintf ppf "string.set"
  | Parraylength k -> fprintf ppf "array.length[%s]" (array_kind k)
  | Pmakearray k -> fprintf ppf "makearray[%s]" (array_kind k)
  | Parrayrefu k -> fprintf ppf "array.unsafe_get[%s]" (array_kind k)
  | Parraysetu k -> fprintf ppf "array.unsafe_set[%s]" (array_kind k)
  | Parrayrefs k -> fprintf ppf "array.get[%s]" (array_kind k)
  | Parraysets k -> fprintf ppf "array.set[%s]" (array_kind k)

let name_of_primitive = function
  | Pidentity -> "Pidentity"
  | Pignore -> "Pignore"
  | Pgetglobal _ -> "Pgetglobal"
  | Psetglobal _ -> "Psetglobal"
  | Pmakeblock _ -> "Pmakeblock"
  | Pfield _ -> "Pfield"
  | Psetfield _ -> "Psetfield"
  (* | Pccall _ -> "Pccall" *)
  | Psequand -> "Psequand"
  | Psequor -> "Psequor"
  | Pnot -> "Pnot"
  | Pnegint -> "Pnegint"
  | Paddint -> "Paddint"
  | Psubint -> "Psubint"
  | Pmulint -> "Pmulint"
  | Pdivint -> "Pdivint"
  | Pmodint -> "Pmodint"
  | Pandint -> "Pandint"
  | Porint -> "Porint"
  | Pxorint -> "Pxorint"
  | Plslint -> "Plslint"
  | Plsrint -> "Plsrint"
  | Pasrint -> "Pasrint"
  | Pintcomp _ -> "Pintcomp"
  | Poffsetint _ -> "Poffsetint"
  | Poffsetref _ -> "Poffsetref"
  | Pstringlength -> "Pstringlength"
  | Pstringrefu -> "Pstringrefu"
  | Pstringsetu -> "Pstringsetu"
  | Pstringrefs -> "Pstringrefs"
  | Pstringsets -> "Pstringsets"
  | Parraylength _ -> "Parraylength"
  | Pmakearray _ -> "Pmakearray"
  | Parrayrefu _ -> "Parrayrefu"
  | Parraysetu _ -> "Parraysetu"
  | Parrayrefs _ -> "Parrayrefs"
  | Parraysets _ -> "Parraysets"

let rec lam ppf = function
  | Lvar id ->
      Ident.print ppf id
  | Lconst cst ->
      Format.pp_print_string ppf (Nativeint.to_string cst)
      (* struct_const ppf cst *)
  | Lapply (func, args) ->
      let lams ppf largs =
        List.iter (fun l -> fprintf ppf "@ %a" lam l) largs in
      fprintf ppf "@[<2>(apply@ %a%a)@]" Ident.print func lams args
  | Llet(id, arg, body) ->
      let rec letbody = function
        | Llet(id, arg, body) ->
            fprintf ppf "@ @[<2>%a =@ %a@]" Ident.print id lam arg;
            letbody body
        | expr -> expr in
      fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a =@ %a@]"
        Ident.print id lam arg;
      let expr = letbody body in
      fprintf ppf ")@]@ %a)@]" lam expr
  | Lletrec(id_arg_list, body) ->

      (*
  | Lfunction{kind; params; body; attr} ->
      let pr_params ppf params =
        match kind with
        | Curried ->
            List.iter (fun param -> fprintf ppf "@ %a" Ident.print param) params
        | Tupled ->
            fprintf ppf " (";
            let first = ref true in
            List.iter
              (fun param ->
                if !first then first := false else fprintf ppf ",@ ";
                Ident.print ppf param)
              params;
            fprintf ppf ")" in
      fprintf ppf "@[<2>(function%a@ %a%a)@]" pr_params params
        function_attribute attr lam body
*)

      (* let bindings ppf id_arg_list = *)
      (*   let spc = ref false in *)
      (*   List.iter *)
      (*     (fun (id, l, body) -> *)
      (*       if !spc then fprintf ppf "@ " else spc := true; *)
      (*       fprintf ppf "@[<2>%a@ %a@]" Ident.print id lam l) *)
      (*     id_arg_list in *)
      (* fprintf ppf *)
      (*   "@[<2>(letrec@ (@[<hv 1>%a@])@ %a)@]" bindings id_arg_list lam body *)
      failwith "not implemented"
  | Lprim(prim, largs) ->
      let lams ppf largs =
        List.iter (fun l -> fprintf ppf "@ %a" lam l) largs in
      fprintf ppf "@[<2>(%a%a)@]" primitive prim lams largs
  | Lifthenelse(lcond, lif, lelse) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" lam lcond lam lif lam lelse
  | Lsequence(l1, l2) ->
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" lam l1 sequence l2
  | Lwhile(lcond, lbody) ->
      fprintf ppf "@[<2>(while@ %a@ %a)@]" lam lcond lam lbody
  | Lfor(param, lo, hi, body) ->
      fprintf ppf "@[<2>(for %a@ %a@ %a@ %a)@]"
       Ident.print param lam lo
       lam hi lam body
  | Lassign(id, expr) ->
      fprintf ppf "@[<2>(assign@ %a@ %a)@]" Ident.print id lam expr
  (* | Levent(expr, ev) -> *)
  (*     let kind = *)
  (*      match ev.lev_kind with *)
  (*      | Lev_before -> "before" *)
  (*      | Lev_after _  -> "after" *)
  (*      | Lev_function -> "funct-body" in *)
  (*     fprintf ppf "@[<2>(%s %s(%i)%s:%i-%i@ %a)@]" kind *)
  (*             ev.lev_loc.Location.loc_start.Lexing.pos_fname *)
  (*             ev.lev_loc.Location.loc_start.Lexing.pos_lnum *)
  (*             (if ev.lev_loc.Location.loc_ghost then "<ghost>" else "") *)
  (*             ev.lev_loc.Location.loc_start.Lexing.pos_cnum *)
  (*             ev.lev_loc.Location.loc_end.Lexing.pos_cnum *)
  (*             lam expr *)

and sequence ppf = function
  | Lsequence(l1, l2) ->
      fprintf ppf "%a@ %a" sequence l1 sequence l2
  | l ->
      lam ppf l

(* let structured_constant = struct_const *)

let pp_lambda = lam

type label = int                        (* Symbolic code labels *)

type instruction =
  | Klabel of label
  | Kacc of int
  | Kenvacc of int
  | Kpush
  | Kpop of int
  | Kassign of int
  | Kpush_retaddr of label
  | Kapply of int                       (* number of arguments *)
  | Kappterm of int * int               (* number of arguments, slot size *)
  | Kreturn of int                      (* slot size *)
  | Krestart
  | Kgrab of int                        (* number of arguments *)
  | Kclosure of label * int
  | Kclosurerec of label list * int
  | Koffsetclosure of int
  | Kgetglobal of Ident.t
  | Ksetglobal of Ident.t
  (* | Kconst of structured_constant *)
  | Kconst of nativeint
  | Kmakeblock of int * int             (* size, tag *)
  | Kmakefloatblock of int
  | Kgetfield of int
  | Ksetfield of int
  | Kgetfloatfield of int
  | Ksetfloatfield of int
  | Kvectlength
  | Kgetvectitem
  | Ksetvectitem
  | Kgetstringchar
  | Ksetstringchar
  | Kbranch of label
  | Kbranchif of label
  | Kbranchifnot of label
  | Kstrictbranchif of label
  | Kstrictbranchifnot of label
  | Kswitch of label array * label array
  | Kboolnot
  | Kpushtrap of label
  | Kpoptrap
  | Kcheck_signals
  | Kccall of string * int
  | Knegint | Kaddint | Ksubint | Kmulint | Kdivint | Kmodint
  | Kandint | Korint | Kxorint | Klslint | Klsrint | Kasrint
  | Kintcomp of comparison
  | Koffsetint of int
  | Koffsetref of int
  | Kisint
  | Kisout
  | Kgetmethod
  | Kgetpubmet of int
  | Kgetdynmet
  (* | Kevent of debug_event *)
  | Kstop
