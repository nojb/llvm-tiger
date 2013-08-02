type ('a, 'b, 'c, 'd) fundef = {
  fn_name : 'a;
  fn_rtyp : 'b;
  fn_args : ('a * 'c) list;
  fn_body : 'd
}

let unique : unit -> int =
  let count = ref (-1) in
  fun () ->
    incr count;
    !count
