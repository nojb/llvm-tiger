let report_error p msg =
  Printf.eprintf "%s: %d: %d: %s\n%!"
    p.Lexing.pos_fname p.Lexing.pos_lnum
    (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)
    msg

let compile_stdin () =
  try
    let lexbuf = Lexing.from_channel stdin in
    lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>" };
    let m = Compile.program (Parser.program Lexer.token lexbuf) in
    Llvm.dump_module m;
    Llvm.dispose_module m
  with
    Compile.Error (p, msg) -> report_error p msg

let basename name =
  if Filename.check_suffix name ".tig" then
    Filename.chop_suffix name ".tig"
  else
    name

let compile_file name =
  let base  = basename name in
  let dest  = base ^ ".bc" in 
  let f     = open_in name in
  let out   = open_out dest in
  try try
    let lexbuf = Lexing.from_channel f in
    lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
    let m = Compile.program (Parser.program Lexer.token lexbuf) in
    close_in f;
    ignore (Llvm_bitwriter.output_bitcode out m);
    close_out out;
    Llvm.dispose_module m
  with e -> (close_in f; close_out out; raise e)
  with Compile.Error (p, msg) ->
    report_error p msg

let _ =
  Arg.parse [
    (* "-opt", Arg.Set Opt.optimize, "Optimize";
    "-dlambda", Arg.Set Emitlambda.dlambda, "Print lambda representation";
    "-dllvm", Arg.Set Emitllvm.dllvm, "Print llvm representation";
    "-usegc", Arg.Set Emitlambda.usegc, "Use shadow-stack garbage collector" *)
    "-stdin", Arg.Unit compile_stdin, "read input from stdin"
  ] compile_file "llvm-tigerc compiler 0.1"
