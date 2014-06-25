
exception Error of Lexing.position * string

let error p =
  Printf.ksprintf (fun message -> raise (Error (p, message)))

let debug () =
  Printf.ksprintf (fun message -> Printf.fprintf stderr "DEBUG: %s\n%!" message)

let report_error p msg =
  Printf.eprintf "%s: %d: %d: %s.\n%!"
    p.Lexing.pos_fname p.Lexing.pos_lnum
    (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)
    msg

