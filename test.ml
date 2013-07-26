let parse ch =
    (Typecheck2.program
      (Parser.program Lexer.token
        (Lexing.from_channel ch)))

let _ =
  Llvm.dump_module (EmitLlvm.program (parse stdin))
