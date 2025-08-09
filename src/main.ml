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
    let passes = if !opt_level >= 2 then "gvn" :: "adce" :: passes else passes in
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

exception Syntax_error of Lexing.position * Lexing.position

let parse_program lexbuf =
  try
    Parser.program Lexer.token lexbuf
  with Parser.Error ->
    let start_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    raise (Syntax_error (start_pos, end_pos))

let compile_file fn =
  fn
  |> lexbuf_from_file
  |> parse_program
  |> Typecheck.program
  |> Compile.program
  |> Irep.transl_program
  |> opt
  |> dump
  |> write_bitcode_file fn
  |> Llvm.dispose_module

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

let program_name = "tc"

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
      Printf.eprintf "%s: error: %s\n%!" program_name s;
      exit 1
  | Syntax_error (start_pos, _end_pos) ->
      let sourcefile = start_pos.Lexing.pos_fname in
      let lineno = start_pos.Lexing.pos_lnum in
      let column = start_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol + 1 in
      Printf.eprintf "%s:%i:%i: syntax error\n%!" sourcefile lineno column;
      exit 2
  | Typecheck.Error {loc; desc} ->
      Printf.eprintf "error: %s:%i:%i: %s\n%!"
        loc.Lexing.pos_fname loc.Lexing.pos_lnum
        (loc.Lexing.pos_cnum - loc.Lexing.pos_bol + 1) (Typecheck.string_of_error desc);
      exit 3
  | exn ->
      Printf.eprintf "%s: unexpected error\n\n%s\n%!" program_name (Printexc.to_string exn);
      Printexc.print_backtrace stderr;
      exit 4
