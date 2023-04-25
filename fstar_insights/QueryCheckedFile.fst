module QueryCheckedFile
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.CheckedFiles
module BU = FStar.Compiler.Util
module SMT = FStar.SMTEncoding.Solver
module TcEnv = FStar.TypeChecker.Env
module TcTerm = FStar.TypeChecker.TcTerm
module Rel = FStar.TypeChecker.Rel
module NBE = FStar.TypeChecker.NBE
module List = FStar.Compiler.List

let run (filename:string) = 
  try
    match FStar.CheckedFiles.unsafe_raw_load_tc_result_from_checked_file filename with
    | None -> 
      BU.print1 "Failed to load %s\n" filename
    | Some tc_result ->
      BU.print1 "Successfully loaded checked file for module %s\n"
                (FStar.Ident.string_of_lid tc_result.checked_module.name)
  with
  | e when false ->
    match FStar.Errors.issue_of_exn e with
    | None -> BU.print_string "Unknown error"; raise e
    | Some issue -> 
      BU.print_string (FStar.Errors.format_issue issue)

let main () = 
  let args = FStar.Getopt.cmdline () in
  let filenames =
    match args with
    | _::_::_ -> List.tl args
    | _ -> 
      BU.print_string "Usage: fstar_insights.exe file1.checked ... filen.checked\n";
      exit 1
  in
  List.iter run filenames
  
#push-options "--warn_error -272"
let _ = main()
#pop-options
