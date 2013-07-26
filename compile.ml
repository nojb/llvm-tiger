open Format

let report_error loc err =
  printf "@[@[<v2>Error while typechecking at %a:@,%a@]@\n@]"
    Location.pp loc Typeerror.pp_error err

let compile inp =
  let m = Opt.program
    (Emitllvm.program
      (Emitlambda.program
        (Nested.program
          (Typecheck.program
            (Parser.program Lexer.token
              (Lexing.from_channel inp)))))) in
  if !Emitllvm.dllvm then Llvm.dump_module m;
  m
