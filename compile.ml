let compile name = 
  let program = Inout.read_file name in
  let _ = print_endline "Parse OK" in
  let _ = print_endline (Ast_print.program2str program) in
  
  let vprogram = Ast_valid.vprogram program in
  let _ = print_endline "Ast_valid.vprogram OK" in
  let _ = print_endline (Ast_print.program2str vprogram) in
  
  let tprogram = Typing.tprogram vprogram in
  let _ = print_endline "Typing.tprogram OK" in
  let _ = print_endline (Core_print.program2str tprogram) in
  
  let mprogram = Monomorphise.core2mono tprogram in
  let _ = print_endline "Monomorphise.core2mono OK" in
  let _ = print_endline (Mono_print.program2str mprogram) in

  let code = Translate.program2code mprogram in
  let _ = print_endline "Translate.program2code OK" in
  let _ = Inout.write_file (name^".exe") ("Machine code:\n"^(Mach.code2str code)) in
  
  let machine = Mach.createMachine code in
  let _ = Mach.execute (Inout.append_file (name^".exe")) machine in
  let _ = print_endline "Execution OK" in
  let _ = print_endline ("Please read "^name^".exe"^" for details.") in
  ()
;;

compile Sys.argv.(1);;
