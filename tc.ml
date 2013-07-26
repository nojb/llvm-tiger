let extract fname =
  if String.length fname < 4 then fname
  else if
    (String.sub fname ((String.length fname)-4) 4) = ".tig" then
      String.sub fname 0 ((String.length fname)-4)
  else
    fname

let file fname =
  let froot = extract fname in
  let fdest = froot ^ ".bc" in 
  let f = open_in fname in
  let out = open_out fdest in
  try try
    let m = Compile.compile f in
    close_in f;
    ignore (Llvm_bitwriter.output_bitcode out m);
    close_out out;
    Llvm.dispose_module m
  with e -> (close_in f; close_out out; raise e)
  with Typeerror.Error (loc, err) ->
    Compile.report_error loc err

let _ =
  Arg.parse [
    "-opt", Arg.Set Opt.optimize, "Optimize";
    "-dlambda", Arg.Set Emitlambda.dlambda, "Print lambda representation";
    "-dllvm", Arg.Set Emitllvm.dllvm, "Print llvm representation";
    "-usegc", Arg.Set Emitlambda.usegc, "Use shadow-stack garbage collector"
  ] file "Tiger/LLVM Compiler 0.1"
