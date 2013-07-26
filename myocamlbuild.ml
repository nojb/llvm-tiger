open Ocamlbuild_plugin;;

ocaml_lib ~extern:true "llvm";;
ocaml_lib ~extern:true "unix" ~tag_name: "use_unix_fix";;
ocaml_lib ~extern:true "llvm_bitwriter";;
(* ocaml_lib ~extern:true "llvm_executionengine";; *)
ocaml_lib ~extern:true "llvm_scalar_opts";;
(* ocaml_lib ~extern:true "llvm_target";; *)

flag ["link"; "ocaml"; "g++"] (S[A"-cc"; A"g++"]);;
