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

(* let opt_level = ref 0 *)
let emit_llvm = ref false
let emit_asm = ref false

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

let compile_stdin () =
  try
    let lexbuf = Lexing.from_channel stdin in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>"};
    let p = Compile.program (Parser.program Lexer.token lexbuf) in
    List.iter (Irep.print_fundecl Format.err_formatter) p;
    let m = Llvm.create_module (Llvm.global_context ()) "" in
    Irep.transl_program m p;
    Llvm.dump_module m;
    Llvm.dispose_module m
  with
    Error.Error (p, msg) -> Error.report_error p msg

let _basename name =
  if Filename.check_suffix name ".tig" then
    Filename.chop_suffix name ".tig"
  else
    name

let _command fmt =
  Printf.ksprintf (fun cmd ->
      let code = Sys.command cmd in
      if code <> 0 then
        Printf.ksprintf failwith "command %S failed with code %d" cmd code
    ) fmt

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
    (* "-O", Arg.Set_int opt_level, "\t\tOptimisation level used by llc"; *)
    "-S", Arg.Set emit_asm, " Emit asm assembly in .s file";
    "-emit-llvm", Arg.Set emit_llvm, " Emit LLVM assembly in .ll file";
    "-stdin", Arg.Unit compile_stdin, " Read input from stdin"
  ]

let main () =
  Arg.parse (Arg.align spec) ignore (* compile_file *) "llvm-tigerc compiler 0.1"

let () =
  try
    main ()
  with e ->
    Printf.eprintf "ERROR: %s\n%!" (Printexc.to_string e);
    exit 1
