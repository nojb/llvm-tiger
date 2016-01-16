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

let compile_stdin () =
  try
    let lexbuf = Lexing.from_channel stdin in
    lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>" };
    let p = Parser.program Lexer.token lexbuf in
    let m, _ = Compile.program p in
    let b = Bytegen.compile m in
    let _ = Byterun.run b in
    ()
  with
    Error.Error (p, msg) -> Error.report_error p msg

let basename name =
  if Filename.check_suffix name ".tig" then
    Filename.chop_suffix name ".tig"
  else
    name

let compile_file name =
  let base = basename name in
  let f = open_in name in
  try
    try
      let lexbuf = Lexing.from_channel f in
      lexbuf.Lexing.lex_curr_p <-
        { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      let m = Compile.program (Parser.program Lexer.token lexbuf) in
      close_in f
    with e -> (close_in f; raise e)
  with Error.Error (p, msg) -> Error.report_error p msg

let speclist =
  [
    (* "-O", Arg.Set_int opt_level, "\t\tOptimisation level used by llc"; *)
    (* "-S", Arg.Set emit_asm, "\t\tEmit asm assembly in .s file"; *)
    (* "-emit-llvm", Arg.Set emit_llvm, "\temit LLVM assembly in .ll file"; *)
    "-stdin", Arg.Unit compile_stdin, "\tread input from stdin"
  ]

let _ =
  Arg.parse speclist compile_file "llvm-tigerc compiler 0.1"
