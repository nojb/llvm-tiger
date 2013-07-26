let optimize = ref false

let program m =
  if !optimize then begin
    let fpm = Llvm.PassManager.create_function m in
    Llvm_scalar_opts.add_memory_to_register_promotion fpm;
    Llvm_scalar_opts.add_constant_propagation fpm;
    Llvm_scalar_opts.add_sccp fpm;
    Llvm_scalar_opts.add_gvn fpm;
    Llvm_scalar_opts.add_reassociation fpm;
    Llvm_scalar_opts.add_instruction_combination fpm;
    Llvm_scalar_opts.add_dead_store_elimination fpm;
    Llvm_scalar_opts.add_aggressive_dce fpm;
    Llvm_scalar_opts.add_cfg_simplification fpm;
    ignore (Llvm.PassManager.initialize fpm);
    Llvm.iter_functions (fun f ->
      ignore (Llvm.PassManager.run_function f fpm)) m;
    ignore (Llvm.PassManager.finalize fpm);
    Llvm.PassManager.dispose fpm
  end
