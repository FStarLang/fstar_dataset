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
  let print_checked_deps_flag = BU.mk_ref false
  let digest_flag = BU.mk_ref false
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
      (noshort, "print_checked_deps", ZeroArgs (fun _ -> print_checked_deps_flag := true), "dump info from checked file");
      (noshort, "digest", ZeroArgs (fun _ -> digest_flag := true), "print digest of file");
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
    let find_file f files is_friend =
      if is_friend
      then List.assoc #string #string (f ^ ".fst.checked") files
      else (//prefer .fsti
        let fsti = f ^ ".fsti.checked" in
        match List.assoc fsti files with
        | None -> List.assoc #string #string (f ^ ".fst.checked") files
        | Some f -> Some f
      )
    in
    fun f is_friend ->
      match !files with
      | None ->
        let fns = load_file_names () in
        files := Some fns;
        find_file f fns is_friend
      | Some fns ->
        find_file f fns is_friend

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

  type checked_file_content = {
    friends:list string;
    deps:list string;
    m:modul
  }
  let checked_files : BU.smap checked_file_content = BU.smap_create 100
  let source_file_lines = list string
  let source_files : BU.smap source_file_lines = BU.smap_create 100
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
      // print_stderr "Loading %s\n" [checked_file];
      match find_file_in_path checked_file with
      | None ->
        print_stderr "Could not find checked file named %s\n" [checked_file];
        None
      | Some checked_file_path -> (
        match FStar.CheckedFiles.unsafe_raw_load_checked_file checked_file_path with
        | None ->
          print_stderr "Could not load %s\n" [checked_file_path];
          None
        | Some (parsing_data, deps, tc_result) ->
          let cfc = {friends=List.map Ident.string_of_lid (FStar.Parser.Dep.friends parsing_data); deps; m = tc_result.checked_module} in
          BU.smap_add checked_files source_filename cfc;
          Some (checked_file_path, cfc)
      )

  let read_source_file (source_filename:string)
    : option (string & source_file_lines)
    = match find_file_in_path (BU.basename source_filename) with 
      | None ->
        print_stderr "Could not find source file named %s\n" [BU.basename source_filename];
        None
      | Some full_path ->
        match BU.smap_try_find source_files full_path with
        | Some lines -> Some (full_path, lines)
        | None -> 
          let lines = BU.file_get_lines full_path in
          BU.smap_add source_files full_path lines;
          Some (full_path, lines)        


  let range_start_end (r:Range.range)
    : (int & int) & (int & int)
    = let start_pos = Range.start_of_range r in
      let end_pos = Range.end_of_range r in
      (Range.line_of_pos start_pos, Range.col_of_pos start_pos),
      (Range.line_of_pos end_pos, Range.col_of_pos end_pos)

  let rec drop (n:int) (l:list 'a) : list 'a = 
      if n <= 0 then l
      else match l with
           | [] -> []
           | _::tl -> drop (n - 1) tl

  let take (n:int) (l:list 'a) : list 'a = 
    let rec aux (n:int) (l:list 'a) (out:list 'a) = 
      if n <= 0 then List.rev out
      else match l with 
           | [] -> List.rev out
           | hd::tl -> aux (n - 1) tl (hd::out)
    in
    aux n l []

let max a b = if a < b then b else a

let substring str start fin = 
  let lstr = String.strlen str in
  if start >= lstr then ""
  else let len = min (max (fin - start) 0) (lstr - start) in
       String.substring str start len


  let read_source_file_range (r:Range.range) 
    : option string
    = if Range.file_of_range r = "dummy" then None
      else match read_source_file (Range.file_of_range r) with
      | None -> None
      | Some (_, lines) ->
        let (start_line, start_col), (end_line, end_col) = range_start_end r in
        let lines = drop (start_line - 1) lines in
        let lines = take (end_line - start_line + 1) lines in
        let lines = 
          match lines with
          | [] -> []
          | [start_line] ->
            [substring start_line start_col end_col]
          | start_line::rest ->
            let lines = substring start_line start_col (String.strlen start_line) :: rest in
            let prefix, [last] = List.splitAt (List.length lines - 1) lines in
            let last = substring last 0 end_col in
            prefix @ [last]
        in
        Some (String.concat "\n" lines)
      
let is_friend cfc dep = 
     List.existsb (fun f -> f = dep) cfc.friends

let load_dependences (cfc:checked_file_content)
  : list checked_file_content
  = let dependence_exclusions = ["prims"; "fstar.pervasives.native"; "fstar.pervasives"] in
    let should_exclude dep =
        BU.for_some (fun x -> String.lowercase dep = x) dependence_exclusions
    in
    let {friends;deps} = cfc in
    let all_deps = BU.smap_create 42 in
    let add_dep d = BU.smap_add all_deps d true in
    let dep_exists d =
        match BU.smap_try_find all_deps d with
        | Some _ -> true
        | _ -> false
    in
    List.iter add_dep deps;
    let is_friend = is_friend cfc in
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
            match map_file_name dep (is_friend dep) with
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
                  cfc.deps
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
  source_typ:string;
  source_def:string;
  prompt:string;
  expected_response:string;
  opens_and_abbrevs:list (either string (string & string));
  vconfig: option VConfig.vconfig
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

let open_or_abbrev_as_json (d:either string (string & string)) = 
  match d with
  | Inl m ->
    //open m
    JsonAssoc [("open", JsonStr m)]

  | Inr (m, n) ->
    //module m = n
    JsonAssoc [("abbrev", JsonBool true); ("key", JsonStr m); ("value", JsonStr n)]

let vconfig_as_json (v:VConfig.vconfig) =
  let open FStar.VConfig in
  JsonAssoc [
    "initial_fuel", JsonInt v.initial_fuel;
    "max_fuel", JsonInt v.max_fuel;
    "initial_ifuel", JsonInt v.initial_ifuel;
    "max_ifuel", JsonInt v.max_ifuel;
    "detail_errors", JsonBool v.detail_errors;
    "detail_hint_replay", JsonBool v.detail_hint_replay;
    "no_smt", JsonBool v.no_smt;
    "quake_lo", JsonInt v.quake_lo;
    "quake_hi", JsonInt v.quake_hi;
    "quake_keep", JsonBool v.quake_keep;
    "retry", JsonBool v.retry;
    "smtencoding_elim_box", JsonBool v.smtencoding_elim_box;
    "smtencoding_nl_arith_repr", JsonStr v.smtencoding_nl_arith_repr;
    "smtencoding_l_arith_repr", JsonStr v.smtencoding_l_arith_repr;
    "smtencoding_valid_intro", JsonBool v.smtencoding_valid_intro;
    "smtencoding_valid_elim", JsonBool v.smtencoding_valid_elim;
    "tcnorm", JsonBool v.tcnorm;
    "no_plugins", JsonBool v.no_plugins;
    "no_tactics", JsonBool v.no_tactics;
    "z3cliopt", JsonList (List.map JsonStr v.z3cliopt);
    "z3smtopt", JsonList (List.map JsonStr v.z3smtopt);
    "z3refresh", JsonBool v.z3refresh;
    "z3rlimit", JsonInt v.z3rlimit;
    "z3rlimit_factor", JsonInt v.z3rlimit_factor;
    "z3seed", JsonInt v.z3seed;
    "z3version", JsonStr v.z3version;
    "trivial_pre_for_unannotated_effectful_fns", JsonBool v.trivial_pre_for_unannotated_effectful_fns;
    "reuse_hint_for", (match v.reuse_hint_for with None -> JsonNull | Some s -> JsonStr s)
  ]


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
              ("source_type", JsonStr l.source_typ);
              ("source_definition", JsonStr l.source_def);              
              ("prompt", JsonStr l.prompt);
              ("expected_response", JsonStr l.expected_response);
              ("opens_and_abbrevs", JsonList (List.map open_or_abbrev_as_json l.opens_and_abbrevs));
              ("vconfig", (match l.vconfig with None -> JsonNull | Some vc -> vconfig_as_json vc));
              ])



(* some definitions, such as those arising from metaprogramming and autogenerated
   inductive helpers such as projectors and discriminators have "dummy" as their file name.
   We heal these imprecise ranges, as we in fact know the files that these definitions arose
   from *)
let heal_dummy_file_name (file_name : string) (r : Range.range) : Range.range
 =
  Range.mk_range (if Range.file_of_range r = "dummy" then file_name else Range.file_of_range r)
         (Range.start_of_range r) (Range.end_of_range r)

module Parser = FStar.Parser.ParseIt
let extract_def_and_typ_from_source_lines rng =
  let source_lines = read_source_file_range rng in
  match source_lines with
  | None -> "<UNK>", None
  | Some lines -> 
    let open Parser in
    let (start_line, start_col), _ = range_start_end rng in
    let frag = {
      frag_fname = Range.file_of_range rng;
      frag_text = lines;
      frag_line = 1;
      frag_col = 0
    } in
    let parse_result = parse (Toplevel frag) in
    lines, Some parse_result

module AST = FStar.Parser.AST

let rec spat (p: AST.pattern) =
  let open AST in
  match p.pat with
  | PatWild _ -> "PatWild"
  | PatConst _ -> "PatConst"
  | PatApp (p, pats) -> BU.format2 "(PatApp (%s, [%s]))" (spat p) (List.map spat pats |> String.concat "; ")
  | PatVar (i, _, _) -> BU.format1 "(PatVar %s)" (Ident.string_of_id i)
  | PatName l -> BU.format1 "(PatName %s)" (Ident.string_of_lid l)
  | PatTvar (i, _, _) -> BU.format1 "(PatTVar %s)" (Ident.string_of_id i)
  | PatList pats -> BU.format1 "(PatList [%s])"  (List.map spat pats |> String.concat "; ")
  | PatTuple (pats, _) -> BU.format1 "(PatTuple [%s])"  (List.map spat pats |> String.concat "; ")
  | PatRecord pats -> BU.format1 "(PatTuple [%s])"  (List.map (fun (l, p) -> BU.format2 "%s=%s" (Ident.string_of_lid l) (spat p)) pats  |> String.concat "; ")
  | PatAscribed (p, _) -> BU.format1 "(PatAscribed %s)" (spat p)
  | PatOr pats ->  BU.format1 "(PatOr [%s])"  (List.map spat pats |> String.concat "; ")
  | PatOp i -> BU.format1 "(PatOp %s)" (Ident.string_of_id i)
  | PatVQuote _ -> "PatVQuote"

let mk_arrow (b: AST.binder') (q: option AST.arg_qualifier) (attr: list AST.term) (body: AST.term) : AST.term =
  let open AST in
  { body with tm = AST.Product ([{ b = b; brange = body.range; blevel = body.level; aqual = q; battributes = attr }], body) }

let rec val_of_ascribed_pat (p: AST.pattern) (t: AST.term) : option (Ident.ident * AST.term) =
  let open AST in
  match p.pat with
  | PatVar (id, _, _) -> Some (id, t)
  | PatApp (p, args) -> val_of_pat_app p (List.rev args) t
  | _ -> None
and val_of_pat_app (p: AST.pattern) (args: list AST.pattern) (t: AST.term) : option (Ident.ident * AST.term) =
  let open AST in
  match args with
  | [] -> val_of_ascribed_pat p t
  | a::args -> match a.pat with
    | PatTuple ([], _) | PatConst Const.Const_unit ->
      val_of_pat_app p args (mk_arrow (NoName { t with tm = Var Parser.Const.unit_lid }) None [] t)
    | PatAscribed ({ pat = PatWild (q, attr) }, (s, _)) ->
      val_of_pat_app p args (mk_arrow (NoName s) q attr t)
    | PatAscribed ({ pat = PatVar (x, q, attr) }, (s, _)) ->
      val_of_pat_app p args (mk_arrow (Annotated (x, s)) q attr t)
    | PatTvar (x, q, attr) ->
      val_of_pat_app p args (mk_arrow (TVariable x) q attr t)
    | PatVar (x, q, attr) ->
      // FIXME: this produces `val foo (#a: _) ..` instead of `val foo #a`
      let wild = mk_term Wild FStar.Compiler.Range.dummyRange Un in
      val_of_pat_app p args (mk_arrow (Annotated (x, wild)) q attr t)
    | _ -> None

let val_of_let (p: AST.pattern) : option (Ident.ident * AST.term) =
  let open AST in
  match p.pat with
  | PatAscribed (p, (t, _)) -> val_of_ascribed_pat p t
  | _ -> None
    // let wild = mk_term Wild FStar.Compiler.Range.dummyRange Un in
    // val_of_ascribed_pat p wild

let extract_from_parse_result_of_let_binding lid parse_result_opt 
  : option (option string
            & string
            & string) =
  let open Parser in
  let open FStar.Parser.AST in
  match parse_result_opt with
  | None -> None //"not parse result"
  | Some pr -> (
    match pr with
    | ParseError(re, msg, r) ->
      None // BU.format2 "Parse error: %s @ %s" msg (Range.string_of_range r)
    | Term _ -> None // "unexpected term"
    | IncrementalFragment _ -> None //"unexpected incremental fragment"
    | ASTFragment (Inl file, _) -> None //"unexpected file result"
    | ASTFragment (Inr (_::_::_), _) -> None //"unexpected multi decl"
    | ASTFragment (Inr [], _) -> None //"unexpected empty decl"    
    | ASTFragment (Inr [decl], _) -> (
      match decl.d with
      | TopLevelLet (letqual, decls) -> (
        let rec name_of_pat_matches (p:pattern) =
          match p.pat with
          | PatAscribed (p, _) -> name_of_pat_matches p
          | PatApp (p, _) -> name_of_pat_matches p
          | PatName l -> Ident.lid_equals l lid
          | PatVar (i, _, _) -> Ident.ident_equals i (Ident.ident_of_lid lid)
          | _ -> false
        in
        let pdef = 
          List.tryFind (fun (p, def) ->
           name_of_pat_matches p)
          decls
        in
        match pdef with
        | None -> 
          print_stderr "Could not find type of %s\n" [Ident.string_of_lid lid];
          None
        | Some (p, d) -> (
          let wild = mk_term Wild FStar.Compiler.Range.dummyRange Un in
          let prompt =
            let decl = { decl with d = TopLevelLet (letqual, [p, wild]) } in
            let doc = FStar.Parser.ToDocument.decl_to_document decl in
            let str = FStar.Pprint.pretty_string (BU.float_of_string "1.0") 100 doc in
            let str = if BU.ends_with str "_" then BU.substring str 0 (String.strlen str - 1) else str in
            BU.trim_string str ^ "\n  " in
          let response = FStar.Parser.ToDocument.term_to_document d in
          let response = FStar.Pprint.pretty_string (BU.float_of_string "1.0") 100 response in
          match val_of_let p with
          | Some val_decl ->
            let doc = FStar.Parser.ToDocument.decl_to_document { decl with d = Val val_decl } in
            let str = FStar.Pprint.pretty_string (BU.float_of_string "1.0") 100 doc in
            Some (Some str, prompt, response)
          | None ->
            (match p.pat with | AST.PatAscribed _ -> print_stderr "Could not convert pattern to val: %s %s\n" [AST.pat_to_string p; spat p] | _ -> ());
            Some (None, prompt, response)
        )
      )
      | _ ->
        None //"not a top-level let"
      )
    | _ -> failwith "Unexpected parse result"
    )

  | _ -> None //"not an ast fragment"

let extract_opens_and_abbrevs (l:list (either open_module_or_namespace module_abbrev)) =
  List.map 
    (function 
     | Inl (m, _) -> Inl (Ident.string_of_lid m)
     | Inr (m, n) -> Inr (Ident.string_of_id  m, Ident.string_of_lid n))
    l

let find_type_from_val_decl (l:Ident.lident) (decls:list sigelt)
  : option string
  = let d =
        List.tryFind
          (fun se ->
            match se.sigel with
            | Sig_declare_typ data -> Ident.lid_equals l data.lid
            | _ -> false)
          decls
    in
    match d with
    | Some se ->
      let source_def, _ = extract_def_and_typ_from_source_lines se.sigrng in
      Some source_def
    | _ -> None 
  
let rec functions_called_by_user_in_def (file_name : string) (modul:list sigelt) (se:sigelt)
  : list defs_and_premises
  = let source_def, parse_result_opt = extract_def_and_typ_from_source_lines se.sigrng in
    let source_typ = "<UNK>" in
    let prompt = "<UNK>" in
    let expected_response = "<UNK>" in
    let opens_and_abbrevs = extract_opens_and_abbrevs se.sigopens_and_abbrevs in
    let vconfig = se.sigopts in
    match se.sigel with
    | Sig_declare_typ data ->
        [{ source_range = heal_dummy_file_name file_name se.sigrng;
          name = Ident.string_of_lid data.lid;
          typ = P.term_to_string data.t;
          definition = "<DECLARETYP>";
          premises = [];
          eff = "" ;
          eff_flags = []; (* if a declare typ does not have an assume qualified, then the def will show up *)
          mutual_with = [];
          proof_features = [] ;
          source_typ;
          source_def;
          prompt;
          expected_response;
          opens_and_abbrevs;
          vconfig
        }]
    | Sig_assume data ->
        [{ source_range = heal_dummy_file_name file_name se.sigrng;
          name = Ident.string_of_lid data.lid;
          typ = P.term_to_string data.phi;
          definition = "<ASSUME>";
          premises = [];
          eff = "" ;
          eff_flags = [];
          mutual_with = [];
          proof_features = [] ;
          source_typ;
          source_def;
          prompt;
          expected_response;
          opens_and_abbrevs;
          vconfig          
        }]
    |  Sig_inductive_typ { params; t; lid; mutuals } ->
        let arr = FStar.Syntax.Util.arrow params (mk_Total t)
        in
        [{ source_range = heal_dummy_file_name file_name se.sigrng;
          name = Ident.string_of_lid lid;
          typ = P.term_to_string arr;
          definition = "<INDUCTIVETYP>";
          premises = [];
          eff = "" ;
          eff_flags = [];
          mutual_with = List.map Ident.string_of_lid mutuals;
          proof_features = [] ;
          source_typ;
          source_def;
          prompt;
          expected_response;
          opens_and_abbrevs;
          vconfig          
        }]
    | Sig_bundle bundle -> List.collect (functions_called_by_user_in_def file_name modul) bundle.ses
    | Sig_datacon data ->
        let _, comp = U.arrow_formals_comp data.t in
        let flags = U.comp_flags comp in
        let name = Ident.string_of_lid data.lid  in
        [{ source_range = heal_dummy_file_name file_name se.sigrng;
          name = name;
          typ = P.term_to_string data.t;
          definition = "<DATACON>";
          premises = List.map Ident.string_of_lid
                              (BU.set_elements (FStar.Syntax.Free.fvars data.t));
          eff = "" ;
          eff_flags = [];
          mutual_with = List.map Ident.string_of_lid data.mutuals ;
          proof_features = [] ;
          source_typ;
          source_def;
          prompt;
          expected_response;
          opens_and_abbrevs;
          vconfig          
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
        let source_typ, prompt, expected_response =
          let Inr fv = lb.lbname in
          let st_opt = extract_from_parse_result_of_let_binding (FStar.Syntax.Syntax.lid_of_fv fv) parse_result_opt in
          let st_opt =
            match find_type_from_val_decl (FStar.Syntax.Syntax.lid_of_fv fv) modul with
            | None -> (
              match st_opt with
              | None -> None
              | Some (Some p, q, r) -> Some (p, q, r)
              | Some (None, q, r) -> Some (source_typ, q, r)
            )
            | Some p ->
              match st_opt with
              | None -> Some (p, prompt, expected_response)
              | Some (_, prompt, expected_response) ->
                Some (p, prompt, expected_response)
          in
          BU.dflt (source_typ, prompt, expected_response) st_opt
        in
        { source_range = heal_dummy_file_name file_name lb.lbpos;
          name;
          typ = P.term_to_string lb.lbtyp;
          definition = P.term_to_string lb.lbdef;
          premises = List.map Ident.string_of_lid
                              (BU.set_elements (FStar.Syntax.Free.fvars lb.lbdef));
          eff = Ident.string_of_lid (U.comp_effect_name comp);
          eff_flags = List.map P.cflag_to_string flags;
          mutual_with;
          proof_features = maybe_rec;
          source_typ;
          source_def;
          prompt;
          expected_response;
          opens_and_abbrevs;
          vconfig          
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
    let rec prefix_until_name out ses =
      match ses with
      | [] -> [], List.rev out
      | se :: ses -> (
        match se.sigel with
        | Sig_let { lids = names } ->
          if BU.for_some (Ident.lid_equals name) names
          then List.collect (fun l -> l.premises) 
                            (functions_called_by_user_in_def source_file cfc.m.declarations se),
               List.rev out //found it
          else prefix_until_name (se :: out) ses
        | _ ->
          prefix_until_name (se :: out) ses
      )
    in
    let ses = List.collect (fun cfc -> cfc.m.declarations) module_deps in
    let user_called_lemmas, local_deps = prefix_until_name [] cfc.m.declarations in
    user_called_lemmas, local_deps @ ses

let filter_sigelts (ses:list sigelt) =
  List.filter
    (fun se -> is_sigelt_tot se || is_sigelt_ghost se || is_sigelt_lemma se)
    ses

let read_module_sigelts (source_file:string) : list sigelt =
  try
    match read_checked_file source_file with
    | None -> exit 1
    | Some (_cfc_path, cfc) -> cfc.m.declarations
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
  List.collect (functions_called_by_user_in_def source_file sigelts) sigelts

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
    | Some (cfc_path, cfc) ->
        [JsonAssoc [("source_file", JsonStr source_file);
                    ("checked_file", JsonStr cfc_path);
                    ("dependencies", JsonList (
                          List.map
                             (fun dep -> JsonStr (BU.dflt ("<UNK>:"^dep) (BU.bind_opt (map_file_name dep (is_friend cfc dep)) find_file_in_path)))
                             (List.tail cfc.deps)));
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

// Same as in FStar.CheckedFiles
type checked_file_entry_stage1 = {
  version: int;
  digest: string;
  parsing_data: Parser.Dep.parsing_data;
}
type checked_file_entry_stage2 = {
  deps_dig: list (string * string);
  tc_res: tc_result;
}

let print_checked_deps (filenames : list string) =
  match filenames with | [filename] ->
  let entry : option (checked_file_entry_stage1 * checked_file_entry_stage2) = BU.load_2values_from_file filename in
  match entry with | Some ((s1,s2)) ->
  let json_of_digest (digest : string) =
    let digest = BU.base64_encode digest in
    JsonStr digest in
  let json_of_dep (file_name, digest) = JsonAssoc [
    "module_name", JsonStr file_name;
    "digest", json_of_digest digest;
  ] in
  BU.print_string (string_of_json (JsonAssoc [
    "source_digest", json_of_digest s1.digest;
    "deps_digest", JsonList (List.map json_of_dep s2.deps_dig);
  ]))

let print_digest (filenames : list string) =
  match filenames with | [filename] ->
  BU.print_string (BU.base64_encode (BU.digest_of_file filename))

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
    else if !print_checked_deps_flag then print_checked_deps !filenames
    else if !digest_flag then print_digest !filenames
    else (usage (); exit 1)
  | _ ->
    usage();
    exit 1

#push-options "--warn_error -272"
let _ =
  try
    FStar.Main.setup_hooks();
    main()
  with
  | e -> //when false ->
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
    "source_type": "...",
    "source_definition": "...",
    "prompt":"...",
    "expected_response":"...",
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
