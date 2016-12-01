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

let emit_asm = ref false

let compile_stdin () =
  try
    let lexbuf = Lexing.from_channel stdin in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>"};
    let p = Compile.program (Parser.program Lexer.token lexbuf) in
    Format.eprintf "@[%a@]@." Irep.print p
    (* List.iter (Irep.print_fundecl Format.err_formatter) p; *)
    (* Irep.transl_program m p; *)
  with
    Error.Error (p, msg) -> Error.report_error p msg

let basename name =
  if Filename.check_suffix name ".tig" then
    Filename.chop_suffix name ".tig"
  else
    name

let command fmt =
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

let _ =
  Arg.parse [
    (* "-O", Arg.Set_int opt_level, "\t\tOptimisation level used by llc"; *)
    "-S", Arg.Set emit_asm, "\t\tEmit asm assembly in .s file";
    "-stdin", Arg.Unit compile_stdin, "\tread input from stdin"
  ] ignore (* compile_file *) "llvm-tigerc compiler 0.1"
