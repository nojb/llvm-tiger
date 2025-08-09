let output_stanza oc fn =
  let base = Filename.basename fn |> Filename.chop_extension in
  Printf.fprintf oc {|
(rule
 (targets %s.out.gen %s.err.gen)
 (action (run ../tools/run_test.exe -cmd %%{dep:../src/main.exe} -runtime %%{dep:../runtime/runtime.c} -out %s.out.gen -err %s.err.gen %%{dep:%s.tig})))

(rule
 (alias runtest)
 (action (diff %s.out %s.out.gen)))

(rule
 (alias runtest)
 (action (diff %s.err %s.gen)))
|} base base base base base base base base base

let () =
  Sys.readdir Filename.current_dir_name
  |> Array.to_list
  |> List.filter (String.ends_with ~suffix:".tig")
  |> List.iter (output_stanza stdout)
