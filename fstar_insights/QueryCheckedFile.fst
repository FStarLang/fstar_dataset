(*
Produces a processed json file from `fst`/`fsti` plus a `queries.jsonl`, where the
`queries.jsonl` has been produced from the raw `smt2` queries that are sent to Z3.
These raw `smt2` queries must have been gathered with an invocation with
  $ export OTHERFLAGS="--z3refresh --log_queries" <build-command-such-as-`make`>.
Authors: Nikhil Swamy, Saikat Chakrabory, Siddharth Bhat
*)
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
module P = FStar.Syntax.Print

let includes : ref (list string) = BU.mk_ref []
let interactive : ref bool = BU.mk_ref false
let add_include s = includes := s :: !includes
let set_interactive () = interactive := true
let simple_lemmas : ref bool = BU.mk_ref false
let set_simple_lemmas () = simple_lemmas := true
let all_defs_and_premises : ref bool = BU.mk_ref false
let set_all_defs_and_premises () = all_defs_and_premises := true
let options : list FStar.Getopt.opt =
  let open FStar.Getopt in
  [
    (noshort, "include", OneArg (add_include, "include"), "include path");
    (noshort, "find_simple_lemmas", ZeroArgs set_simple_lemmas, "scan a file for simple lemmas, dump output as json");
    (noshort, "all_defs_and_premises", ZeroArgs set_all_defs_and_premises, "scan a file for all definitions, dump their names, defs, types, premises, etc. as json");
    (noshort, "interactive", ZeroArgs set_interactive, "interactive mode");
  ]

let load_file_names () =
  let fns =
    List.collect
      (fun inc -> List.map (fun fn -> String.lowercase fn, fn)
                        (BU.readdir inc))
      !includes
  in
  fns

let map_file_name =
  let files = BU.mk_ref None in
  let find_file f files =
    let fsti = f ^ ".fsti.checked" in
    match List.assoc fsti files with
    | None -> List.assoc #string #string (f ^ ".fst.checked") files
    | Some f -> Some f
  in
  fun f ->
    match !files with
    | None ->
      let fns = load_file_names () in
      files := Some fns;
      find_file f fns
    | Some fns ->
      find_file f fns

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
  match (SS.compress body).n with
  | Tm_constant _ -> false //too simple
  | _ -> aux body

let is_lemma (se:sigelt) =
  match se.sigel with
  | Sig_let { lbs=(_, lbs) } ->
    List.for_all (fun lb -> is_lemma_arrow lb.lbtyp) lbs
  | _ -> false

let is_def (se:sigelt) =
  match se.sigel with
  | Sig_let _ -> true
  | Sig_bundle _ -> true
  | Sig_assume _ -> true
  | Sig_declare_typ _ -> true
  | _ -> false

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
  : option (string * checked_file_content)
  = let checked_file =
      if BU.ends_with source_filename ".checked"
      then source_filename
      (* TODO: check that we do not have an fst associated to this fsti. If we do have an fst, then we should ignore
         the fsti! *)
      else if BU.ends_with source_filename ".fst" || BU.ends_with source_filename ".fsti"
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
        Some (checked_file_path, (deps, tc_result.checked_module))
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
          let fn =
            match map_file_name dep with
            | None -> dep
            | Some f -> f
          in
          match BU.smap_try_find checked_files fn with
          | Some m -> aux deps (m::modules)
          | None -> (
            match read_checked_file fn with
            | None ->
              (* file not found, reported warning, continue *)
              aux deps modules

            | Some (_cfc_path, cfc) ->
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

//[(lemma_1, [premises;in;lemma1]); ... (lemma_n, ...)]
//where lemma_1 ...lemma_n are mutually defined
type defs_and_premises = {
  definition:string;
  eff: string;
  eff_flags: list string;
  mutual_with:list string;
  name: string;
  premises: list string;
  proof_features: list string;
  source_range: Range.range;
  typ: string;
}

open FStar.Json

let range_as_json_list (r:Range.range)
  : list (string & json)
  = let start_pos = Range.start_of_range r in
    let end_pos = Range.end_of_range r in
    ["file_name", JsonStr (Range.file_of_range r);
     "start_line", JsonInt (Range.line_of_pos start_pos);
     "start_col", JsonInt (Range.col_of_pos start_pos);
     "end_line", JsonInt (Range.line_of_pos end_pos);
     "end_col", JsonInt (Range.col_of_pos end_pos)]

let defs_and_premises_as_json (l:defs_and_premises) =
  JsonAssoc ((range_as_json_list l.source_range) @
             [
              ("definition", JsonStr l.definition);
              ("effect", JsonStr l.eff);
              ("effect_flags", JsonList (List.map JsonStr l.eff_flags));
              ("mutual_with", JsonList (List.map JsonStr l.mutual_with));
              ("name", JsonStr l.name);
              ("premises", JsonList (List.map JsonStr l.premises));
              ("proof_features", JsonList (List.map JsonStr l.proof_features));
              ("type", JsonStr l.typ);
              ])



let rec functions_called_by_user_in_def (se:sigelt)
  : list defs_and_premises
  = match se.sigel with
    | Sig_declare_typ data ->
        [{ source_range = se.sigrng;
          name = Ident.string_of_lid data.lid;
          typ = P.term_to_string data.t;
          definition = "<DECLARETYP>";
          premises = [];
          eff = "" ;
          eff_flags = []; (* if a declare typ does not have an assume qualified, then the def will show up *)
          mutual_with = [];
          proof_features = [] ;
        }]
    | Sig_assume data ->
        [{ source_range = se.sigrng;
          name = Ident.string_of_lid data.lid;
          typ = P.term_to_string data.phi;
          definition = "<ASSUME>";
          premises = [];
          eff = "" ;
          eff_flags = [];
          mutual_with = [];
          proof_features = [] ;
        }]
    |  Sig_inductive_typ { params; t; lid; mutuals } ->
        let arr = FStar.Syntax.Util.arrow params (mk_Total t)
        in
        [{ source_range = se.sigrng;
          name = Ident.string_of_lid lid;
          typ = P.term_to_string arr;
          definition = "<INDUCTIVETYP>";
          premises = [];
          eff = "" ;
          eff_flags = [];
          mutual_with = List.map Ident.string_of_lid mutuals;
          proof_features = [] ;
        }]
    | Sig_bundle bundle -> List.collect functions_called_by_user_in_def bundle.ses
    | Sig_datacon data ->
        let _, comp = U.arrow_formals_comp data.t in
        let flags = U.comp_flags comp in
        let name = Ident.string_of_lid data.lid  in
        [{ source_range = se.sigrng;
          name = name;
          typ = P.term_to_string data.t;
          definition = "<DATACON>";
          premises = List.map Ident.string_of_lid
                              (BU.set_elements (FStar.Syntax.Free.fvars data.t));
          eff = "" ;
          eff_flags = [];
          mutual_with = List.map Ident.string_of_lid data.mutuals ;
          proof_features = [] ;
        }]
    | Sig_let { lbs=(is_rec, lbs) } ->
      let maybe_rec =
        match lbs with
        | _::_::_ -> ["mutual recursion"]
        | _ -> if is_rec then ["recursion"] else []
      in
      let mutual_with =
        match lbs with
        | []
        | [_] -> []
        | _ -> List.map (fun lb -> P.lbname_to_string lb.lbname) lbs
      in
      let lbname_to_string (lbname: lbname) =
        match lbname with
        | Inl _ -> failwith "Unexpected lb name"
        | Inr fv -> Ident.string_of_lid fv.fv_name.v
      in
      List.map (fun lb ->
        let _, comp = U.arrow_formals_comp lb.lbtyp in
        let flags = U.comp_flags comp in
        let name = lbname_to_string lb.lbname in
        { source_range = lb.lbpos;
          name;
          typ = P.term_to_string lb.lbtyp;
          definition = P.term_to_string lb.lbdef;
          premises = List.map Ident.string_of_lid
                              (BU.set_elements (FStar.Syntax.Free.fvars lb.lbdef));
          eff = Ident.string_of_lid (U.comp_effect_name comp);
          eff_flags = List.map P.cflag_to_string flags;
          mutual_with;
          proof_features = maybe_rec;
        })
        lbs
    | _ -> []

let dependences_of_definition (source_file:string) (name:string)
  : list string & list sigelt
  = print_stderr "Loading deps of %s:%s\n" [source_file; name];
    let cfc =
        match read_checked_file source_file with
        | None ->
          print_stderr "Could not find checked file for %s\n" [source_file];
          exit 1
        | Some (_cfc_path, cfc) -> cfc
    in
    let name = Ident.lid_of_str name in
    let module_deps = load_dependences cfc in
    let _, m = cfc in
    let rec prefix_until_name out ses =
      match ses with
      | [] -> [], List.rev out
      | se :: ses -> (
        match se.sigel with
        | Sig_let { lids = names } ->
          if BU.for_some (Ident.lid_equals name) names
          then List.flatten (List.map (fun l -> l.premises) (functions_called_by_user_in_def se)),
               List.rev out //found it
          else prefix_until_name (se :: out) ses
        | _ ->
          prefix_until_name (se :: out) ses
      )
    in
    let ses = List.collect (fun (_, m) -> m.declarations) module_deps in
    let user_called_lemmas, local_deps = prefix_until_name [] m.declarations in
    user_called_lemmas, local_deps @ ses

let filter_sigelts (ses:list sigelt) =
  List.filter
    (fun se -> is_sigelt_tot se || is_sigelt_ghost se || is_sigelt_lemma se)
    ses

let read_module_sigelts (source_file:string) : list sigelt =
  try
    match read_checked_file source_file with
    | None -> exit 1
    | Some (_cfc_path, (deps, modul)) -> modul.declarations
  with
  | e ->
    match FStar.Errors.issue_of_exn e with
    | None ->
      BU.print1 "Exception: %s" (BU.print_exn e);
      exit 1
    | Some issue ->
      BU.print_string (FStar.Errors.format_issue issue);
      exit 1

let find_simple_lemmas (source_file:string) : list sigelt =
  let sigelts = read_module_sigelts source_file in
  List.filter is_simple_lemma sigelts

let find_defs_and_premises (source_file:string)
  : list defs_and_premises =
  let sigelts = read_module_sigelts source_file in
  List.collect functions_called_by_user_in_def sigelts

let simple_lemma_as_json
      (source_file:string)
      (se:sigelt)
 : json
 = match se.sigel with
   | Sig_let { lbs=(_, [lb]); lids=[name] } ->
     let name = JsonStr (Ident.string_of_lid name) in
     let lemma_statement = P.term_to_string lb.lbtyp in
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

let dump_all_lemma_premises_as_json (source_file:string)
  = List.map defs_and_premises_as_json (find_defs_and_premises source_file)



(* prefer an `fsti` over an `fst` *)
let dump_dependency_info_as_json (source_file:string)
  =
    match read_checked_file source_file with
    | None -> exit 1
    | Some (cfc_path, (deps, modul))  ->
        [JsonAssoc [("source_file", JsonStr source_file);
                    ("checked_file", JsonStr cfc_path);
                    ("dependencies", JsonList (List.map
                      (fun dep -> JsonStr (BU.dflt "<UNK>" (BU.bind_opt (map_file_name dep) find_file_in_path))) (List.tail deps)));
                    ("depinfo", JsonBool true)]] (* tag that this is dependency information. Poor man's sum type *)

module JU = FStar.Interactive.JsonHelper

let run_json_cmd (j:json) =
  let ja = JU.js_assoc j in
  match JU.try_assoc "command" ja with
  | Some (JsonStr "find_deps") -> (
    let open JU in
    let payload = js_assoc (assoc "payload" ja) in
    let source_file = JU.js_str (assoc "source_file" payload) in
    let name = js_str (assoc "name" payload) in
    let user_called_lemmas, ses = dependences_of_definition source_file name in
    let user_called_lemmas = JsonList (List.map JsonStr user_called_lemmas) in
    let json = JsonList (List.collect dep_as_json ses) in
    let out = JsonAssoc [("user_called_lemmas", user_called_lemmas);
                         ("dependences", json)] in
    BU.print_string (string_of_json out);
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
    print_stderr "Usage: fstar_insights.exe (--interactive | --find_simple_lemmas | --all_defs_and_premises) --include path1 ... --include path_n source_file.(fst|fsti)\n" []
  in
  let filenames = BU.mk_ref [] in
  let res = FStar.Getopt.parse_cmdline options (fun s -> filenames :=  s::!filenames; Getopt.Success) in
  match res with
  | Getopt.Success ->
    let files = !filenames in
    if !all_defs_and_premises
    then
      let lemmas_premises = List.concatMap dump_all_lemma_premises_as_json files in
      let deps = List.concatMap dump_dependency_info_as_json files in
      BU.print_string (string_of_json (JsonAssoc [("defs", JsonList lemmas_premises); ("dependencies", JsonList deps)]))
    else if !simple_lemmas
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

(* Things that we would like to extract


  {
    "file_name": "FStar.BV.fst",
    "start_line": 59,
    "start_col": 2,
    "end_line": 59,
    "end_col": 49,
    "name": "int2bv_shl",
    "type": "...",
    "definition": "let int2bv_shl ...",
    "premises": [
      "Prims.pos",
      "FStar.UInt.uint_t",
      "FStar.BV.bv_t",
      "Prims.squash",
      "Prims.eq2",
      "FStar.BV.bvshl",
      "FStar.BV.int2bv",
      "FStar.BV.inverse_vec_lemma",
      "Prims.unit"
    ],
    "smt_premises": [
     (* read from hints file *)
     Do we want the actual SMT2 text for each premise and the query?
     It gets pretty big
     http://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html#unsat-core-and-hints
    ]
    "effects": [
      "Lemma", "Ghost", "ST", ...
    ],
    "mutual_with": [ ... ];
    "decreases": string;
    "proof_features": [
      "induction on parameter k",
      "case split on ... ",
      "arithmetic",
      "sequences",
      "maps",
      "separation logic",
      "smt pats"
    ],

  },


*)
