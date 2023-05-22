module QueryCheckedFile
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.CheckedFiles
open FStar.Compiler.List
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

let includes : ref (list string) = BU.mk_ref []
let interactive : ref bool = BU.mk_ref false
let add_include s = includes := s :: !includes
let set_interactive () = interactive := true
let simple_lemmas : ref bool = BU.mk_ref false
let set_simple_lemmas () = simple_lemmas := true
let options : list FStar.Getopt.opt = 
  let open FStar.Getopt in
  [
    (noshort, "include", OneArg (add_include, "include"), "include path");
    (noshort, "find_simple_lemmas", ZeroArgs set_simple_lemmas, "scan a file for simple lemmas, dump output as json");
    (noshort, "interactive", ZeroArgs set_interactive, "interactive mode");    
  ]

let find_file_in_path f =
  match List.tryFind (fun i -> BU.file_exists (BU.concat_dir_filename i f)) !includes with
  | None -> None
  | Some i -> Some (BU.concat_dir_filename i f)

let is_tot_arrow (t:typ) =
    let _, comp = U.arrow_formals_comp_ln t in
    U.is_total_comp comp

let is_gtot_arrow (t:typ) =
    let _, comp = U.arrow_formals_comp_ln t in
    not (U.is_total_comp comp) &&
    U.is_tot_or_gtot_comp comp

let is_lemma_arrow (t:typ) =
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
    | Tm_app { args } ->
      List.for_all (fun (x, _) -> aux x) args
    | Tm_let { lbs=(false, [lb]); body } ->
      aux lb.lbdef && aux body
    | Tm_meta { tm=t } ->
      aux t
    | _ -> false
  in
  aux body

let is_simple_lemma (se:sigelt) =
  match se.sigel with
  | Sig_let { lbs=(false, [lb]); lids=[name] } ->
    is_lemma_arrow lb.lbtyp &&
    is_simple_definition lb.lbdef
  | _ -> false

let check_type (se:sigelt) (f:typ -> bool) =
  match se.sigel with
  | Sig_let { lbs=(_, lbs) } ->
    BU.for_all (fun lb -> f lb.lbtyp) lbs
  | Sig_declare_typ { t } -> f t
  | _ -> false

let is_sigelt_tot (se:sigelt) = check_type se is_tot_arrow
let is_sigelt_ghost (se:sigelt) = check_type se is_gtot_arrow
let is_sigelt_lemma (se:sigelt) = check_type se is_lemma_arrow

let checked_file_content = list string & modul
let checked_files : BU.smap checked_file_content = BU.smap_create 100
let print_stderr f l = BU.fprint BU.stderr f l

let read_checked_file (source_filename:string)
  : option checked_file_content 
  = let checked_file = 
      if BU.ends_with source_filename ".fst"
      then source_filename ^ ".checked"
      else source_filename ^ ".fst.checked"
    in
    print_stderr "Loading %s\n" [checked_file];
    match find_file_in_path checked_file with
    | None ->
      print_stderr "Could not find %s\n" [checked_file];
      None
    | Some checked_file_path -> (
      match FStar.CheckedFiles.unsafe_raw_load_checked_file checked_file_path with
      | None -> 
        print_stderr "Could not load %s\n" [checked_file_path];
        None
      | Some (deps, tc_result) ->
        BU.smap_add checked_files source_filename (deps, tc_result.checked_module);
        Some (deps, tc_result.checked_module)
    )

let load_dependences (cfc:checked_file_content)
  : list checked_file_content
  = let dependence_exclusions = ["prims"; "fstar.pervasives.native"; "fstar.pervasives"] in
    let should_exclude dep =
        BU.for_some (fun x -> String.lowercase dep = x) dependence_exclusions
    in
    let deps, _ = cfc in
    let all_deps = BU.smap_create 42 in
    let add_dep d = BU.smap_add all_deps d true in
    let dep_exists d =
        match BU.smap_try_find all_deps d with
        | Some _ -> true
        | _ -> false
    in
    List.iter add_dep deps;
    let rec aux (remaining_deps:list string)
                (modules:list checked_file_content)
      : list checked_file_content
      = match remaining_deps with
        | [] -> modules
        | dep::deps ->
          if should_exclude dep 
          then aux deps modules
          else (
          match BU.smap_try_find checked_files dep with
          | Some m -> aux deps (m::modules)
          | None -> (
            match read_checked_file dep with
            | None -> 
              (* file not found, reported warning, continue *)
              aux deps modules
              
            | Some cfc ->
              let more_deps = 
                List.filter 
                  (fun d -> 
                     if dep_exists d 
                     then false
                     else (add_dep d; true))
                  (fst cfc)
              in
              aux (deps@more_deps) (cfc::modules)
            )
          )
    in
    aux deps []


let dependences_of_definition (source_file:string) (name:string)
  : list sigelt                              
  = print_stderr "Loading deps of %s:%s\n" [source_file; name];
    let cfc =
        match read_checked_file source_file with
        | None -> 
          print_stderr "Could not find checked file for %s\n" [source_file];
          exit 1
        | Some cfc -> cfc
    in
    let name = Ident.lid_of_str name in
    let module_deps = load_dependences cfc in
    let _, m = cfc in
    let rec prefix_until_name out ses =
      match ses with
      | [] -> List.rev out
      | se :: ses -> (
        match se.sigel with
        | Sig_let { lids = names } ->
          if BU.for_some (Ident.lid_equals name) names
          then List.rev out //found it
          else prefix_until_name (se :: out) ses
        | _ -> 
          prefix_until_name (se :: out) ses
      )
    in
    let ses = List.collect (fun (_, m) -> m.declarations) module_deps in
    let local_deps = prefix_until_name [] m.declarations in
    local_deps @ ses

let filter_sigelts (ses:list sigelt) = 
  List.filter
    (fun se -> is_sigelt_tot se || is_sigelt_ghost se || is_sigelt_lemma se)
    ses

open FStar.Json
let find_simple_lemmas (source_file:string) : list sigelt = 
  try
    match read_checked_file source_file with
    | None -> exit 1
    | Some (deps, modul) ->
      List.filter is_simple_lemma modul.declarations
  with
  | e ->
    match FStar.Errors.issue_of_exn e with
    | None ->
      BU.print1 "Exception: %s" (BU.print_exn e);
      exit 1
    | Some issue -> 
      BU.print_string (FStar.Errors.format_issue issue);
      exit 1

let range_as_json_list (r:Range.range)
  : list (string & json)
  = let start_pos = Range.start_of_range r in
    let end_pos = Range.end_of_range r in
    ["file_name", JsonStr (Range.file_of_range r);
     "start_line", JsonInt (Range.line_of_pos start_pos);
     "start_col", JsonInt (Range.col_of_pos start_pos);                
     "end_line", JsonInt (Range.line_of_pos end_pos);                
     "end_col", JsonInt (Range.col_of_pos end_pos)]
        
let simple_lemma_as_json
      (source_file:string)
      (se:sigelt)
 : json
 = match se.sigel with
   | Sig_let { lbs=(_, [lb]); lids=[name] } -> 
     let name = JsonStr (Ident.string_of_lid name) in
     let lemma_statement = FStar.Syntax.Print.term_to_string lb.lbtyp in
     let criterion = JsonStr "simple lemma" in
     JsonAssoc (["source_file", JsonStr source_file;
                 "name", name;
                 "lemma_statement", JsonStr lemma_statement;
                 "criterion", criterion]@range_as_json_list se.sigrng)
   | _ -> JsonNull

let dep_as_json (se:sigelt)
  : list json
  = let rng = range_as_json_list se.sigrng in
    let with_name lid = JsonAssoc (["name", JsonStr (Ident.string_of_lid lid)]@rng) in
    match se.sigel with
    | Sig_let { lids=names } -> List.map with_name names
    | Sig_declare_typ { lid=name; t } -> [with_name name]
    | _ -> []

let dump_simple_lemmas_as_json (source_file:string)
  = let simple_lemmas = 
        List.map (simple_lemma_as_json source_file)
                 (find_simple_lemmas source_file)
    in
    match simple_lemmas with
    | [] -> ()
    | _ -> BU.print_string (string_of_json (JsonList simple_lemmas))

module JU = FStar.Interactive.JsonHelper

let run_json_cmd (j:json) =
  let ja = JU.js_assoc j in
  match JU.try_assoc "command" ja with
  | Some (JsonStr "find_deps") -> (
    let open JU in
    let payload = js_assoc (assoc "payload" ja) in
    let source_file = js_str (assoc "source_file" payload) in
    let name = js_str (assoc "name" payload) in
    let ses = dependences_of_definition source_file name in
    let json = JsonList (List.collect dep_as_json ses) in
    BU.print_string (string_of_json json);
    BU.print_string "\n"
   )
  | Some j -> 
    print_stderr "Unknown command: %s" [string_of_json j]
  | None -> 
    print_stderr "command not found" []
  
let interact () =
    let stdin = BU.open_stdin () in
    let rec go () =
      match BU.read_line stdin with
      | None -> ()
      | Some line ->
        match Json.json_of_string line with
        | None -> print_stderr "Could not parse json: %s\n" [line]; exit 1
        | Some cmd -> 
          run_json_cmd cmd;
          go()
    in
    go()
           
let main () = 
  let usage () =
    print_stderr "Usage: fstar_insights.exe (--interactive | --find_simple_lemmas) --include path1 ... --include path_n source_file.(fst|fsti)\n" []
  in
  let filenames = BU.mk_ref [] in
  let res = FStar.Getopt.parse_cmdline options (fun s -> filenames :=  s::!filenames; Getopt.Success) in
  match res with
  | Getopt.Success -> 
    let files = !filenames in
    if !simple_lemmas
    then List.iter dump_simple_lemmas_as_json files
    else if !interactive
    then interact ()
    else (usage (); exit 1)
  | _ ->
    usage();
    exit 1
  
#push-options "--warn_error -272"
let _ = 
  try 
    FStar.Main.setup_hooks();
    let _ = FStar.Options.set_options "--print_implicits" in
    main()
  with 
  | e -> 
    print_stderr "Exception: %s\n" [BU.print_exn e];
    exit 1
#pop-options
