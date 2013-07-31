open Globals
open Anf

module S = Set.Make (Id)
module M = Map.Make (Id)

let add_list xts env =
  List.fold_left (fun env (x, t) -> M.add x t env) env xts

let union_list l =
  List.fold_left S.union S.empty l

let debug () =
  Printf.ksprintf (fun message -> Printf.fprintf stderr "Debug: %s\n%!" message)

module Solver =
  struct
    let eqns : (Id.t * S.t * Id.t list) list ref = ref []
    let reset () = eqns := []
    let add_equation f s gs = eqns := (f, s, gs) :: !eqns
    let solve () =
      let count = ref 0 in
      let start = List.fold_left
        (fun m (f, s, _) -> M.add f s m) M.empty !eqns in
      let iter m =
        incr count;
        debug () "LL iteration %d" !count;
        List.fold_left (fun m (f, s, gs) ->
          let s' = union_list (s :: List.map (fun g -> M.find g m) gs) in
          debug () "free vars for %s: %s"
            (Id.to_string f)
            (String.concat " " (List.map Id.to_string (S.elements s')));
          M.add f (union_list (s :: List.map (fun g -> M.find g m) gs)) m) m
          !eqns in
      let rec loop m =
        let m' = iter m in
        if M.equal S.equal m m' then
          begin debug () "LL fixpoint reached."; m' end
        else
          loop m'
      in loop start
  end;;

let join m1 m2 =
  M.fold M.add m1 m2

let toplevel : (Id.t, llvm_type, exp) fundef list ref = ref []

let cexp sols = function
  | CALL (x, vs) ->
      let xs = S.elements (M.find x sols) in
      CALL (x, List.fold_right (fun x vs -> VVAR x :: vs) xs vs)
  | _ as c -> c

let rec exp vars funs sols = function
  | CHECK (v, e, msg) ->
      CHECK (v, exp vars funs sols e, msg)
  | LET (x, t, c, e) ->
      LET (x, t, cexp sols c, exp (M.add x t vars) funs sols e)
  | IF (v, e1, e2) ->
      IF (v, exp vars funs sols e1, exp vars funs sols e2)
  | RETURN (c) ->
      RETURN (cexp sols c)
  | LET_BLOCK (bl, args, body, e) ->
      LET_BLOCK (bl, args, exp (add_list args vars) funs sols body,
        exp vars funs sols e)
  | GOTO (bl, vs) ->
      GOTO (bl, vs)
  | LET_REC (fundefs, e) ->
      Solver.reset ();
      List.iter (fun f ->
        let gs' = S.elements (fc f.fn_body) in
        let gs = List.filter (fun fundef -> List.mem fundef.fn_name gs')
          fundefs in
        let sf = S.filter (fun v -> M.mem v vars) (fv f.fn_body) in
        let hs = List.filter (fun h -> S.mem h funs) gs' in
        let sf = union_list
          (sf :: List.map (fun h -> M.find h sols) hs) in
        Solver.add_equation f.fn_name sf (List.map (fun g -> g.fn_name) gs))
        fundefs;
      let sols' = Solver.solve () in
      let sols' = join sols sols' in
      let funs' = List.fold_right S.add (List.map (fun f -> f.fn_name) fundefs)
        funs in
      List.iter (fun fundef ->
        toplevel := { fundef with fn_args = 
          List.fold_right (fun x args -> (x, M.find x vars) :: args)
            (S.elements (M.find fundef.fn_name sols')) fundef.fn_args;
            fn_body = exp vars funs' sols' fundef.fn_body } ::
              !toplevel) fundefs;
          (* List.map (fun x -> x, M.find x vars)
            (S.elements (M.find fundef.fn_name sols')) } :: !toplevel) fundefs;
            *)
      exp vars funs' sols' e

let f p =
  let body' = exp M.empty S.empty M.empty p.prog_body in
  { p with
    prog_funs = !toplevel;
    prog_body = body' }
