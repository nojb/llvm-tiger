module S = Set.Make (String)
module M = Map.Make (String)

let add_list xts env =
  List.fold_left (fun env (x, t) -> M.add x t env) env xts

let union_list l =
  List.fold_left S.union S.empty l

let debug () =
  Printf.ksprintf (fun message -> Printf.fprintf stderr "Debug: %s\n%!" message)

let eqns : (string * S.t * string list) list ref = ref []
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
      debug () "free vars for %s: %s" f
        (String.concat " " (S.elements s'));
      M.add f (union_list (s :: List.map (fun g -> M.find g m) gs)) m) m
      !eqns in
  let rec loop m =
    let m' = iter m in
    if M.equal S.equal m m' then
      begin debug () "LL fixpoint reached."; m' end
    else
      loop m'
  in loop start
