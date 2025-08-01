(* let opt m =
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
   end *)

let compile_channel ic =
  try
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>"};
    let m =
      lexbuf
      |> Parser.program Lexer.token
      |> Typecheck.program
      |> Compile.program
      |> Irep.transl_program
    in
    Llvm.dump_module m;
    Llvm.dispose_module m
  with Error.Error (p, msg) ->
    Error.report_error p msg

(* let compile_file name = *)
(*   let base  = basename name in *)
(*   let basebase = Filename.basename base in *)
(*   let f     = open_in name in *)
(*   try *)
(*     try *)
(*       let lexbuf = Lexing.from_channel f in *)
(*       lexbuf.Lexing.lex_curr_p <- *)
(*         { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name }; *)
(*       let m = Compile.program (Parser.program Lexer.token lexbuf) in *)
(*       close_in f; *)
(*       let outname, outchan = Filename.open_temp_file ~mode:[Open_binary] basebase ".bc" in *)
(*       let outbase = Filename.chop_suffix outname ".bc" in *)
(*       ignore (Llvm_bitwriter.output_bitcode outchan m); *)
(*       close_out outchan; *)
(*       Llvm.dispose_module m; *)
(*       if !emit_llvm then *)
(*         command "llvm-dis %s -o %s.ll" outname base; *)
(*       if !emit_asm then *)
(*         command "clang %s -o %s.s" outname base; *)
(*       if not !emit_llvm && not !emit_asm then begin *)
(*         command "llc %s" outname; *)
(*         command "clang %s.s tiger_stdlib.c tiger_gc.c" outbase *)
(*       end *)
(*     with e -> *)
(*       close_in f; *)
(*       raise e *)
(*   with *)
(*   | Error.Error (p, msg) -> *)
(*       Error.report_error p msg *)
(*   | Failure s -> *)
(*       Printf.eprintf ">> Fatal error: %s\n%!" s *)

let spec =
  [
    "-stdin", Arg.Unit (fun () -> compile_channel stdin), " Read input from stdin"
  ]

let main () =
  Arg.parse (Arg.align spec) ignore (* compile_file *) "llvm-tigerc compiler 0.1"

let () =
  try
    main ()
  with
  | Failure s | Sys_error s ->
      Printf.eprintf "ERROR: %s\n%!" s;
      exit 1
  | exn ->
      Printf.eprintf "UNEXPECTED ERROR: %s\n%!" (Printexc.to_string exn);
      Printexc.print_backtrace stderr;
      exit 2
