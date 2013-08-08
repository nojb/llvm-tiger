let parse ch =
    Compile.program
      (Parser.program Lexer.token
        (Lexing.from_channel ch))

let _ =
  parse stdin

(* let _ =
  parse stdin *)

(* let _ =
  Llvm.dump_module (Emit.program (parse stdin)) *)
