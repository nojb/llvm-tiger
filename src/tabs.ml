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

type ident =
  {
    idesc : string;
    ipos : Lexing.position
  }

type typ =
  | Tname of ident
  | Tarray of ident
  | Trecord of (ident * ident) list

type var_desc =
  | Vsimple of ident
  | Vsubscript of var * exp
  | Vfield of var * ident

and var =
  {
    vdesc : var_desc;
    vpos : Lexing.position;
  }

and exp_desc =
  | Eunit
  | Eint of int
  | Estring of string
  | Enil
  | Evar of var
  | Ebinop of exp * bin * exp
  | Eassign of var * exp
  | Ecall of ident * exp list
  | Eseq of exp * exp
  | Emakearray of ident * exp * exp
  | Emakerecord of ident * (ident * exp) list
  | Eif of exp * exp * exp
  | Ewhile of exp * exp
  | Efor of ident * exp * exp * exp
  | Ebreak
  | Elet of dec * exp

and exp =
  {
    edesc : exp_desc;
    epos : Lexing.position;
  }

and dec =
  | Dtypes of (ident * typ) list
  | Dfuns of fundef list
  | Dvar of ident * ident option * exp

and fundef =
  {
    fname : ident;
    frety : ident option;
    fargs : (ident * ident) list;
    fbody : exp
  }

module S = Set.Make (String)

let remove_list l s =
  List.fold_right S.remove l s

let union_list l =
  List.fold_left S.union S.empty l

module Ident = struct
  include String
  let print ppf s = Format.pp_print_string ppf s
end

type comparison =
  | Ceq | Cneq | Clt | Cgt | Cle | Cge

type value_kind =
  | Addr | Int

type primitive =
    Pidentity
  | Pignore
  (* | Ploc of loc_kind *)
  (* Globals *)
  | Pgetglobal of Ident.t
  | Psetglobal of Ident.t
  (* Operations on heap blocks *)
  | Pmakeblock of int
  | Pfield of value_kind * int
  | Psetfield of value_kind * int
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
  | Pmakearray of value_kind
  | Parraylength of value_kind
  | Parrayrefu of value_kind
  | Parraysetu of value_kind
  | Parrayrefs of value_kind
  | Parraysets of value_kind
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
  | Lbreak

let rec fv = function
  | Lvar id -> S.singleton id
  | Lconst _ -> S.empty
  | Lprim (_, el)
  | Lapply (_, el) -> List.fold_left (fun s e -> S.union s (fv e)) S.empty el
  | Llet (i, e1, e2) -> S.union (fv e1) (S.remove i (fv e2))
  | Lletrec (_, e) -> fv e (* CHECK *)
  | Lfor (i, e1, e2, e3) ->
      S.union (fv e1) (S.union (fv e2) (S.remove i (fv e3)))
  | Lifthenelse (e1, e2, e3) -> S.union (fv e1) (S.union (fv e2) (fv e3))
  | Lsequence (e1, e2)
  | Lwhile (e1, e2) -> S.union (fv e1) (fv e2)
  | Lassign (i, e) -> S.add i (fv e)
  | Lbreak -> S.empty

open Format

let value_kind = function
  | Addr -> "addr"
  | Int -> "int"

let primitive ppf = function
  | Pidentity -> fprintf ppf "id"
  | Pignore -> fprintf ppf "ignore"
  | Pgetglobal id -> fprintf ppf "global %a" Ident.print id
  | Psetglobal id -> fprintf ppf "setglobal %a" Ident.print id
  | Pmakeblock(tag) -> fprintf ppf "makeblock %i" tag
  | Pfield (k, n) -> fprintf ppf "field[%s] %i" (value_kind k) n
  | Psetfield(k, n) -> fprintf ppf "setfield[%s] %i" (value_kind k) n
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
  | Parraylength k -> fprintf ppf "array.length[%s]" (value_kind k)
  | Pmakearray k -> fprintf ppf "makearray[%s]" (value_kind k)
  | Parrayrefu k -> fprintf ppf "array.unsafe_get[%s]" (value_kind k)
  | Parraysetu k -> fprintf ppf "array.unsafe_set[%s]" (value_kind k)
  | Parrayrefs k -> fprintf ppf "array.get[%s]" (value_kind k)
  | Parraysets k -> fprintf ppf "array.set[%s]" (value_kind k)

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
