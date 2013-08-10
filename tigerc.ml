let optimize = ref false

let opt m =
  if !optimize then begin
    let fpm = Llvm.PassManager.create_function m in
    Llvm_scalar_opts.add_memory_to_register_promotion fpm;
    Llvm_scalar_opts.add_constant_propagation fpm;
    Llvm_scalar_opts.add_sccp fpm;
    Llvm_scalar_opts.add_gvn fpm;
    Llvm_scalar_opts.add_reassociation fpm;
    Llvm_scalar_opts.add_instruction_combination fpm;
    Llvm_scalar_opts.add_dead_store_elimination fpm;
    Llvm_scalar_opts.add_aggressive_dce fpm;
    Llvm_scalar_opts.add_cfg_simplification fpm;
    ignore (Llvm.PassManager.initialize fpm);
    Llvm.iter_functions (fun f ->
      ignore (Llvm.PassManager.run_function f fpm)) m;
    ignore (Llvm.PassManager.finalize fpm);
    Llvm.PassManager.dispose fpm
  end

let compile_stdin () =
  try
    let lexbuf = Lexing.from_channel stdin in
    lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>" };
    let m = Compile.program (Parser.program Lexer.token lexbuf) in
    opt m;
    Llvm.dump_module m;
    Llvm.dispose_module m
  with
    Error.Error (p, msg) -> Error.report_error p msg

let basename name =
  if Filename.check_suffix name ".tig" then
    Filename.chop_suffix name ".tig"
  else
    name

let compile_file name =
  let base  = basename name in
  let dest  = base ^ ".bc" in 
  let f     = open_in name in
  try
    try
      let lexbuf = Lexing.from_channel f in
      lexbuf.Lexing.lex_curr_p <-
        { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      let m = Compile.program (Parser.program Lexer.token lexbuf) in
      close_in f;
      opt m;
      let out = open_out dest in
      ignore (Llvm_bitwriter.output_bitcode out m);
      close_out out;
      Llvm.dispose_module m;
      ignore (Sys.command ("llc " ^ dest));
      ignore (Sys.command ("clang " ^ base ^ ".s " ^ "tiger_stdlib.c tiger_gc.c"))
    with e -> (close_in f; raise e)
  with Error.Error (p, msg) -> Error.report_error p msg

let _ =
  Arg.parse [
    "-opt", Arg.Set optimize, "Activate LLVM optimisation";
    (* "-dlambda", Arg.Set Emitlambda.dlambda, "Print lambda representation";
    "-dllvm", Arg.Set Emitllvm.dllvm, "Print llvm representation";
    "-usegc", Arg.Set Emitlambda.usegc, "Use shadow-stack garbage collector" *)
    "-stdin", Arg.Unit compile_stdin, "read input from stdin"
  ] compile_file "llvm-tigerc compiler 0.1"
