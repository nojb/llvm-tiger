let dump_llvm = ref false
let opt_level = ref 1

let () =
  Printexc.record_backtrace true

let () =
  Llvm_all_backends.initialize ()

let opt m =
  if !opt_level <= 0 then m
  else begin
    let passes = ["mem2reg"] in
    let passes = if !opt_level >= 2 then "gvn" :: passes else passes in
    let triple = Llvm_target.Target.default_triple () in
    let target = Llvm_target.Target.by_triple triple in
    let target_machine = Llvm_target.TargetMachine.create ~triple target in
    let options = Llvm_passbuilder.create_passbuilder_options () in
    let res = Llvm_passbuilder.run_passes m (String.concat "," passes) target_machine options in
    Llvm_passbuilder.dispose_passbuilder_options options;
    match res with
    | Ok () -> m
    | Error s -> failwith s
  end

let lexbuf_from_file fn =
  let lexbuf = Lexing.from_string (In_channel.with_open_bin fn In_channel.input_all) in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fn};
  lexbuf

let write_bitcode_file fn m =
  let _ = Llvm_bitwriter.write_bitcode_file m (Filename.chop_extension fn ^ ".bc") in
  m

let dump m =
  if !dump_llvm then Llvm.dump_module m;
  m

let compile_file fn =
  try
    fn
    |> lexbuf_from_file
    |> Parser.program Lexer.token
    |> Typecheck.program
    |> Compile.program
    |> Irep.transl_program
    |> opt
    |> dump
    |> write_bitcode_file fn
    |> Llvm.dispose_module
  with Error.Error (p, msg) ->
    Error.report_error p msg

let format_file fn =
  let lexbuf = lexbuf_from_file fn in
  let ast = Parser.program Lexer.token lexbuf in
  Format.printf "%a@." Fmt.expression ast.body

type mode =
  | Fmt
  | Compile

let mode = ref None

let anonymous s =
  match !mode, s with
  | None, "fmt" -> mode := Some Fmt
  | None, ("c" | "compile") -> mode := Some Compile
  | (None | Some Compile), s -> compile_file s
  | Some Fmt, s -> format_file s

let main () =
  let spec =
    [
      "-dllvm", Arg.Set dump_llvm, " Dump LLVM representation";
      "-O0", Arg.Unit (fun () -> opt_level := 0), " Disable all optimizations";
      "-O1", Arg.Unit (fun () -> opt_level := 1), " Minimal optimizations (default)";
      "-O2", Arg.Unit (fun () -> opt_level := 2), " Further optimmizations";
    ]
  in
  Arg.parse (Arg.align spec) anonymous "tigerc 0.1"

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
