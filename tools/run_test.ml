let cmd = ref ""
let runtime = ref ""
let out_file = ref ""
let err_file = ref ""

let run fn =
  let base = Filename.basename fn |> Filename.chop_extension in
  let openfile fn =
    Unix.openfile fn [O_CREAT; O_WRONLY; O_TRUNC; O_SHARE_DELETE; O_CLOEXEC] 0o644 in
  let out_file = openfile !out_file in
  let err_file = openfile !err_file in
  let run_process cmd args =
    let pid = Unix.create_process cmd (Array.of_list (cmd :: args)) Unix.stdin out_file err_file in
    match Unix.waitpid [] pid with
    | _, WEXITED n -> n
    | _, (WSIGNALED n | WSTOPPED n) -> 128 + n
  in
  let code = run_process !cmd ["-dllvm"; fn] in
  if code = 0 then begin
    let exe_name = base ^ ".exe" in
    let code = run_process "cc" [base ^ ".o"; !runtime; "-o"; exe_name] in
    if code = 0 then ignore (run_process ("./" ^ exe_name) [exe_name])
  end;
  Unix.close out_file;
  Unix.close err_file

let () =
  let spec =
    [ "-cmd", Arg.Set_string cmd, " Command name";
      "-runtime", Arg.Set_string runtime, " Runtime C file name";
      "-out", Arg.Set_string out_file, " Output file";
      "-err", Arg.Set_string err_file, " Error file" ]
  in
  Arg.parse (Arg.align spec) run "Test runner"
