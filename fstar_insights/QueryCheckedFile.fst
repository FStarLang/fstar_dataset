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
open FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst

let is_lemma_type (t:typ) =
    let _, comp = U.arrow_formals_comp_ln t in
    Ident.lid_equals (U.comp_effect_name comp)
                     (FStar.Parser.Const.effect_Lemma_lid)

let is_simple_definition (t:term) : ML bool =
  let t = U.unascribe t in 
  let _, body, _ = U.abs_formals_maybe_unascribe_body true t in
  let rec aux body : ML bool = 
    let body = U.unascribe body in
    match (SS.compress body).n with
    | Tm_bvar _
    | Tm_name _
    | Tm_fvar _
    | Tm_uinst _
    | Tm_constant _
    | Tm_type _
    | Tm_arrow _
    | Tm_refine _
    | Tm_quoted _ -> true
    | Tm_app(_, args) ->
      List.for_all (fun (x, _) -> aux x) args
    | Tm_let((false, [lb]), body) ->
      aux lb.lbdef && aux body
    | Tm_meta(t, _) ->
      aux t
    | _ -> false
  in
  aux body

let is_simple_lemma (se:sigelt) =
  match se.sigel with
  | Sig_let ((false, [lb]), [name]) ->
    (* non-recursive definition *)
    if is_lemma_type lb.lbtyp 
    then (
      BU.print_string "--------------------------------------------------------------------------------\n";
      if is_simple_definition lb.lbdef
      then (BU.print1 "%s is a simple lemma\n" (Ident.string_of_lid name);
            BU.print1 "%s\n" (FStar.Syntax.Print.sigelt_to_string se))
      else BU.print1 "%s is a complex lemma\n" (Ident.string_of_lid name)
    )
         
  | _ -> ()

let run (filename:string) = 
  try
    match FStar.CheckedFiles.unsafe_raw_load_tc_result_from_checked_file filename with
    | None -> 
      BU.print1 "Failed to load %s\n" filename
    | Some tc_result ->
      BU.print1 "Successfully loaded checked file for module %s\n"
                (FStar.Ident.string_of_lid tc_result.checked_module.name);
      List.iter is_simple_lemma tc_result.checked_module.declarations
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
