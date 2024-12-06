(*
--------------------------------------------------------------------------------------------
Copyright (c) Microsoft Corporation. All rights reserved.
Licensed under the MIT License. See LICENSE in the project root for license information.
--------------------------------------------------------------------------------------------

Produces a processed json file from `fst`/`fsti` plus a `queries.jsonl`, where the
  `queries.jsonl` has been produced from the raw `smt2` queries that are sent to Z3.
  These raw `smt2` queries must have been gathered with an invocation with
    $ export OTHERFLAGS="--z3refresh --log_queries" <build-command-such-as-`make`>.

Authors: Nikhil Swamy, Saikat Chakrabory, Siddharth Bhat, Gabriel Ebner
*)

module QueryCheckedFile
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.CheckedFiles
open FStar.Compiler.List
module Set = FStar.Compiler.RBSet
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

let includes:ref (list string) = BU.mk_ref []
let add_include s = includes := s :: !includes
let print_checked_deps_flag = BU.mk_ref false
let digest_flag = BU.mk_ref false
let all_defs_and_premises:ref bool = BU.mk_ref false
let set_all_defs_and_premises () = all_defs_and_premises := true

let options:list FStar.Getopt.opt =
  let open FStar.Getopt in
  [
    // include path
    (noshort, "include", OneArg (add_include, "include"));
    // scan a file for all definitions, dump their names, defs, types, premises, etc. as json
    (noshort,
      "all_defs_and_premises",
      ZeroArgs set_all_defs_and_premises);
    // dump info from checked file
    (noshort,
      "print_checked_deps",
      ZeroArgs (fun _ -> print_checked_deps_flag := true));
    // print digest of file
    (noshort, "digest", ZeroArgs (fun _ -> digest_flag := true));
  ]

let load_file_names () =
  let fns =
    List.collect (fun inc -> List.map (fun fn -> String.lowercase fn, fn) (BU.readdir inc))
      !includes
  in
  fns

let map_file_name =
  let files = BU.mk_ref None in
  let find_file f files is_friend =
    if is_friend
    then List.assoc #string #string (f ^ ".fst.checked") files
    else
      //prefer .fsti
      (let fsti = f ^ ".fsti.checked" in
        match List.assoc fsti files with
        | None -> List.assoc #string #string (f ^ ".fst.checked") files
        | Some f -> Some f)
  in
  fun f is_friend ->
    match !files with
    | None ->
      let fns = load_file_names () in
      files := Some fns;
      find_file f fns is_friend
    | Some fns -> find_file f fns is_friend

let find_file_in_path f =
  match List.tryFind (fun i -> BU.file_exists (BU.concat_dir_filename i f)) !includes with
  | None -> None
  | Some i -> Some (BU.concat_dir_filename i f)

let is_tot_arrow (t: typ) =
  let _, comp = U.arrow_formals_comp_ln t in
  U.is_total_comp comp

let is_gtot_arrow (t: typ) =
  let _, comp = U.arrow_formals_comp_ln t in
  not (U.is_total_comp comp) && U.is_tot_or_gtot_comp comp

let is_lemma_arrow (t: typ) =
  let _, comp = U.arrow_formals_comp_ln t in
  Ident.lid_equals (U.comp_effect_name comp) (FStar.Parser.Const.effect_Lemma_lid)

let is_div_typ (t: typ) =
  let _, comp = U.arrow_formals_comp_ln t in
  not (U.is_total_comp comp || U.is_pure_or_ghost_comp comp)

(* has Lemma effect / return type is literally squash *)
let rec is_propish (t : typ) =
  let bs, comp = U.arrow_formals_comp_ln t in
  let n, r, a = U.comp_eff_name_res_and_args comp in
  Ident.lid_equals n Parser.Const.effect_Lemma_lid
    || Some? (U.is_squash r)
    (* TODO(gabriel): it would be cool to check whether the type has type prop, but we don't load the dependencies yet *)
    || (bs <> [] && is_propish r)

let is_type (t: typ) =
  let bs, comp = U.arrow_formals_comp_ln t in
  let n, r, a = U.comp_eff_name_res_and_args comp in
  match (SS.compress r).n with
  | Tm_type _ -> true
  | Tm_fvar {fv_name={v}} ->
    Ident.lid_equals v Parser.Const.prop_lid ||
      Ident.lid_equals v Parser.Const.logical_lid
  | _ -> false

let rec is_simple_type (t: typ) =
  let bs, comp = U.arrow_formals_comp t in
  let rec all_simple_types = function
    | [] -> true
    | b::bs -> is_simple_type b.binder_bv.sort && all_simple_types bs in
  let rec is_fv t =
    match (SS.compress t).n with
    | Tm_uinst (t, _) -> is_fv t
    | Tm_fvar _ -> true
    | _ -> false in
  let r = U.comp_result comp in
  U.is_total_comp comp && all_simple_types bs &&
    (is_fv r || // Assume that referenced fvars have simple types
      (match (SS.compress r).n with
      | Tm_type _ -> true
      | Tm_name {sort} -> (match (SS.compress sort).n with | Tm_type _ -> true | _ -> false)
      | Tm_app {hd; args} ->
        let rec all_simple_types = function
          | [] -> true
          | b::bs -> is_simple_type (fst b) && all_simple_types bs in
        is_fv hd // Assume that referenced fvars have simple types
          && all_simple_types args
      | _ -> false))

let is_simple_definition (t: term) : ML bool =
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
    | Tm_app { args = args } -> List.for_all (fun (x, _) -> aux x) args
    | Tm_let { lbs = false, [lb] ; body = body } -> aux lb.lbdef && aux body
    | Tm_meta { tm = t } -> aux t
    | _ -> false
  in
  match (SS.compress body).n with
  | Tm_constant _ -> false //too simple
  | _ -> aux body

let is_lemma (se: sigelt) =
  match se.sigel with
  | Sig_let { lbs = _, lbs } -> List.for_all (fun lb -> is_lemma_arrow lb.lbtyp) lbs
  | _ -> false

let is_def (se: sigelt) =
  match se.sigel with
  | Sig_let _ -> true
  | Sig_bundle _ -> true
  | Sig_assume _ -> true
  | Sig_declare_typ _ -> true
  | _ -> false

let is_simple_lemma (se: sigelt) =
  match se.sigel with
  | Sig_let { lbs = false, [lb] ; lids = [name] } ->
    is_lemma_arrow lb.lbtyp && is_simple_definition lb.lbdef
  | _ -> false

type checked_file_content = {
  friends:list string;
  deps:list string;
  m:modul
}

let checked_files:BU.smap checked_file_content = BU.smap_create 100

let source_file_lines = list string

let source_files:BU.smap source_file_lines = BU.smap_create 100

let print_stderr f l = BU.fprint BU.stderr f l

let read_checked_file (source_filename: string) : option (string * checked_file_content) =
  let checked_file =
    if BU.ends_with source_filename ".checked"
    then source_filename
    else
      (* TODO: check that we do not have an fst associated to this fsti. If we do have an fst, then we should ignore
             the fsti! *)
      if BU.ends_with source_filename ".fst" || BU.ends_with source_filename ".fsti"
      then source_filename ^ ".checked"
      else source_filename ^ ".fst.checked"
  in
  // print_stderr "Loading %s\n" [checked_file];
  match find_file_in_path checked_file with
  | None ->
    print_stderr "Could not find checked file named %s\n" [checked_file];
    None
  | Some checked_file_path ->
    (match FStar.CheckedFiles.unsafe_raw_load_checked_file checked_file_path with
      | None ->
        print_stderr "Could not load %s\n" [checked_file_path];
        None
      | Some (parsing_data, deps, tc_result) ->
        let cfc =
          {
            friends = List.map Ident.string_of_lid (FStar.Parser.Dep.friends parsing_data);
            deps = deps;
            m = tc_result.checked_module
          }
        in
        BU.smap_add checked_files source_filename cfc;
        Some (checked_file_path, cfc))

let read_source_file (source_filename: string) : option (string & source_file_lines) =
  match find_file_in_path (BU.basename source_filename) with
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

let range_start_end (r: Range.range) : (int & int) & (int & int) =
  let start_pos = Range.start_of_range r in
  let end_pos = Range.end_of_range r in
  (Range.line_of_pos start_pos, Range.col_of_pos start_pos),
  (Range.line_of_pos end_pos, Range.col_of_pos end_pos)

let rec drop (n: int) (l: list 'a) : list 'a =
  if n <= 0
  then l
  else
    match l with
    | [] -> []
    | _ :: tl -> drop (n - 1) tl

let take (n: int) (l: list 'a) : list 'a =
  let rec aux (n: int) (l out: list 'a) =
    if n <= 0
    then List.rev out
    else
      match l with
      | [] -> List.rev out
      | hd :: tl -> aux (n - 1) tl (hd :: out)
  in
  aux n l []

let max a b = if a < b then b else a

let substring str start fin =
  let lstr = String.strlen str in
  if start >= lstr
  then ""
  else
    let len = min (max (fin - start) 0) (lstr - start) in
    String.substring str start len

let read_source_file_range (r: Range.range) : option string =
  if Range.file_of_range r = "dummy"
  then None
  else
    match read_source_file (Range.file_of_range r) with
    | None -> None
    | Some (_, lines) ->
      let (start_line, start_col), (end_line, end_col) = range_start_end r in
      let lines = drop (start_line - 1) lines in
      let lines = take (end_line - start_line + 1) lines in
      let lines =
        match lines with
        | [] -> []
        | [start_line] -> [substring start_line start_col end_col]
        | start_line :: rest ->
          let lines = substring start_line start_col (String.strlen start_line) :: rest in
          let prefix, [last] = List.splitAt (List.length lines - 1) lines in
          let last = substring last 0 end_col in
          prefix @ [last]
      in
      Some (String.concat "\n" lines)

let is_friend cfc dep = List.existsb (fun f -> f = dep) cfc.friends

let load_dependences (cfc: checked_file_content) : list checked_file_content =
  let dependence_exclusions = ["prims"; "fstar.pervasives.native"; "fstar.pervasives"] in
  let should_exclude dep = BU.for_some (fun x -> String.lowercase dep = x) dependence_exclusions in
  let { friends = friends ; deps = deps } = cfc in
  let all_deps = BU.smap_create 42 in
  let add_dep d = BU.smap_add all_deps d true in
  let dep_exists d =
    match BU.smap_try_find all_deps d with
    | Some _ -> true
    | _ -> false
  in
  List.iter add_dep deps;
  let is_friend = is_friend cfc in
  let rec aux (remaining_deps: list string) (modules: list checked_file_content)
      : list checked_file_content =
    match remaining_deps with
    | [] -> modules
    | dep :: deps ->
      if should_exclude dep
      then aux deps modules
      else
        (let fn =
            match map_file_name dep (is_friend dep) with
            | None -> dep
            | Some f -> f
          in
          match BU.smap_try_find checked_files fn with
          | Some m -> aux deps (m :: modules)
          | None ->
            (match read_checked_file fn with
              | None -> aux deps modules (* file not found, reported warning, continue *)
              | Some (_cfc_path, cfc) ->
                let more_deps =
                  List.filter (fun d ->
                        if dep_exists d
                        then false
                        else
                          (add_dep d;
                            true))
                    cfc.deps
                in
                aux (deps @ more_deps) (cfc :: modules)))
  in
  aux deps []

module JH = JsonHelper

open FStar.Json

let jh_of_range (r: Range.range) : JH.range =
  let start_pos = Range.start_of_range r in
  let end_pos = Range.end_of_range r in
  {
    file_name1 = Range.file_of_range r;
    start_line = Range.line_of_pos start_pos;
    start_col = Range.col_of_pos start_pos;
    end_line = Range.line_of_pos end_pos;
    end_col = Range.col_of_pos end_pos
  }

let jh_of_vconfig (v: VConfig.vconfig) : JH.vconfig1 =
  let open FStar.VConfig in
  {
    initial_fuel = v.initial_fuel;
    max_fuel = v.max_fuel;
    initial_ifuel = v.initial_ifuel;
    max_ifuel = v.max_ifuel;
    detail_errors = v.detail_errors;
    detail_hint_replay = v.detail_hint_replay;
    no_smt = v.no_smt;
    quake_lo = v.quake_lo;
    quake_hi = v.quake_hi;
    quake_keep = v.quake_keep;
    retry = v.retry;
    smtencoding_elim_box = v.smtencoding_elim_box;
    smtencoding_nl_arith_repr = v.smtencoding_nl_arith_repr;
    smtencoding_l_arith_repr = v.smtencoding_l_arith_repr;
    smtencoding_valid_intro = v.smtencoding_valid_intro;
    smtencoding_valid_elim = v.smtencoding_valid_elim;
    tcnorm = v.tcnorm;
    no_plugins = v.no_plugins;
    no_tactics = v.no_tactics;
    z3cliopt = v.z3cliopt;
    z3smtopt = v.z3smtopt;
    z3refresh = v.z3refresh;
    z3rlimit = v.z3rlimit;
    z3rlimit_factor = v.z3rlimit_factor;
    z3seed = v.z3seed;
    z3version = v.z3version;
    trivial_pre_for_unannotated_effectful_fns = v.trivial_pre_for_unannotated_effectful_fns;
    reuse_hint_for = v.reuse_hint_for;
  }

(* some definitions, such as those arising from metaprogramming and autogenerated
   inductive helpers such as projectors and discriminators have "dummy" as their file name.
   We heal these imprecise ranges, as we in fact know the files that these definitions arose
   from *)

let heal_dummy_file_name (file_name: string) (r: Range.range) : Range.range =
  Range.mk_range (if Range.file_of_range r = "dummy" then file_name else Range.file_of_range r)
    (Range.start_of_range r)
    (Range.end_of_range r)

module Parser = FStar.Parser.ParseIt

let extract_def_and_typ_from_source_lines rng =
  let source_lines = read_source_file_range rng in
  match source_lines with
  | None -> "<UNK>", None
  | Some lines ->
    let open Parser in
    let (start_line, start_col), _ = range_start_end rng in
    let frag =
      { frag_fname = Range.file_of_range rng; frag_text = lines; frag_line = 1; frag_col = 0 }
    in
    let parse_result = parse (Toplevel frag) in
    lines, Some parse_result

module AST = FStar.Parser.AST

let rec spat (p: AST.pattern) =
  let open AST in
  match p.pat with
  | PatWild _ -> "PatWild"
  | PatConst _ -> "PatConst"
  | PatApp (p, pats) ->
    BU.format2 "(PatApp (%s, [%s]))" (spat p) (List.map spat pats |> String.concat "; ")
  | PatVar (i, _, _) -> BU.format1 "(PatVar %s)" (Ident.string_of_id i)
  | PatName l -> BU.format1 "(PatName %s)" (Ident.string_of_lid l)
  | PatTvar (i, _, _) -> BU.format1 "(PatTVar %s)" (Ident.string_of_id i)
  | PatList pats -> BU.format1 "(PatList [%s])" (List.map spat pats |> String.concat "; ")
  | PatTuple (pats, _) -> BU.format1 "(PatTuple [%s])" (List.map spat pats |> String.concat "; ")
  | PatRecord pats ->
    BU.format1 "(PatTuple [%s])"
      (List.map (fun (l, p) -> BU.format2 "%s=%s" (Ident.string_of_lid l) (spat p)) pats |>
        String.concat "; ")
  | PatAscribed (p, _) -> BU.format1 "(PatAscribed %s)" (spat p)
  | PatOr pats -> BU.format1 "(PatOr [%s])" (List.map spat pats |> String.concat "; ")
  | PatOp i -> BU.format1 "(PatOp %s)" (Ident.string_of_id i)
  | PatVQuote _ -> "PatVQuote"

let mk_arrow (b: AST.binder') (q: option AST.arg_qualifier) (attr: list AST.term) (body: AST.term)
    : AST.term =
  let open AST in
  {
    body with
    tm
    =
    AST.Product
    ([{ b = b; brange = body.range; blevel = body.level; aqual = q; battributes = attr }], body)
  }

let rec val_of_ascribed_pat (p: AST.pattern) (t: AST.term) : option (Ident.ident * AST.term) =
  let open AST in
  match p.pat with
  | PatVar (id, _, _) -> Some (id, t)
  | PatApp (p, args) -> val_of_pat_app p (List.rev args) t
  | _ -> None
and val_of_pat_app (p: AST.pattern) (args: list AST.pattern) (t: AST.term)
    : option (Ident.ident * AST.term) =
  let open AST in
  match args with
  | [] -> val_of_ascribed_pat p t
  | a :: args ->
    match a.pat with
    | PatTuple ([], _)
    | PatConst Const.Const_unit ->
      val_of_pat_app p
        args
        (mk_arrow (NoName ({ t with tm = Var Parser.Const.unit_lid })) None [] t)
    | PatAscribed ({ pat = PatWild (q, attr) }, (s, _)) ->
      val_of_pat_app p args (mk_arrow (NoName s) q attr t)
    | PatAscribed ({ pat = PatVar (x, q, attr) }, (s, _)) ->
      val_of_pat_app p args (mk_arrow (Annotated (x, s)) q attr t)
    | PatTvar (x, q, attr) -> val_of_pat_app p args (mk_arrow (TVariable x) q attr t)
    | PatVar (x, q, attr) ->
      let wild =
        // FIXME: this produces `val foo (#a: _) ..` instead of `val foo #a`
        mk_term Wild FStar.Compiler.Range.dummyRange Un
      in
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
    : option (option string & string & string) =
  let open Parser in
  let open FStar.Parser.AST in
  match parse_result_opt with
  | None -> None //"not parse result"
  | Some pr ->
    (match pr with
      | ParseError (re, msg, r) ->
        None // BU.format2 "Parse error: %s @ %s" msg (Range.string_of_range r)
      | Term _ -> None // "unexpected term"
      | IncrementalFragment _ -> None //"unexpected incremental fragment"
      | ASTFragment (Inl file, _) -> None //"unexpected file result"
      | ASTFragment (Inr (_ :: _ :: _), _) -> None //"unexpected multi decl"
      | ASTFragment (Inr [], _) -> None //"unexpected empty decl"    
      | ASTFragment (Inr [decl], _) ->
        (match decl.d with
          | TopLevelLet (letqual, decls) ->
            (let rec name_of_pat_matches (p: pattern) =
                match p.pat with
                | PatAscribed (p, _) -> name_of_pat_matches p
                | PatApp (p, _) -> name_of_pat_matches p
                | PatName l -> Ident.lid_equals l lid
                | PatVar (i, _, _) -> Ident.ident_equals i (Ident.ident_of_lid lid)
                | _ -> false
              in
              let pdef = List.tryFind (fun (p, def) -> name_of_pat_matches p) decls in
              match pdef with
              | None ->
                print_stderr "Could not find type of %s\n" [Ident.string_of_lid lid];
                None
              | Some (p, d) ->
                (let wild = mk_term Wild FStar.Compiler.Range.dummyRange Un in
                  let prompt =
                    let decl = { decl with d = TopLevelLet (letqual, [p, wild]) } in
                    let doc = FStar.Parser.ToDocument.decl_to_document decl in
                    let str = FStar.Pprint.pretty_string (BU.float_of_string "1.0") 100 doc in
                    let str =
                      if BU.ends_with str "_"
                      then BU.substring str 0 (String.strlen str - 1)
                      else str
                    in
                    BU.trim_string str ^ "\n  "
                  in
                  let response = FStar.Parser.ToDocument.term_to_document d in
                  let response =
                    FStar.Pprint.pretty_string (BU.float_of_string "1.0") 100 response
                  in
                  match val_of_let p with
                  | Some val_decl ->
                    let doc =
                      FStar.Parser.ToDocument.decl_to_document ({ decl with d = Val val_decl })
                    in
                    let str = FStar.Pprint.pretty_string (BU.float_of_string "1.0") 100 doc in
                    Some (Some str, prompt, response)
                  | None ->
                    (match p.pat with
                      | AST.PatAscribed _ ->
                        print_stderr "Could not convert pattern to val: %s %s\n"
                          [AST.pat_to_string p; spat p]
                      | _ -> ());
                    Some (None, prompt, response)))
          | _ ->
            //"not a top-level let"
            None)
      | _ -> failwith "Unexpected parse result")
  | _ ->
    //"not an ast fragment"
    None

let extract_opens_and_abbrevs (l: list (either open_module_or_namespace module_abbrev))
    : list (either JH.open_ JH.abbrev_) =
  List.map (function
      | Inl (m, _) -> Inl ({ JH.open_1 = Ident.string_of_lid m })
      | Inr (m, n) ->
        Inr ({ JH.abbrev_1 = Ident.string_of_id m; JH.full_module = Ident.string_of_lid n }))
    l

let find_type_from_val_decl (l: Ident.lident) (decls: list sigelt) : option string =
  let d =
    List.tryFind (fun se ->
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

let rec functions_called_by_user_in_def (file_name: string) (modul: list sigelt) (se: sigelt)
    : list JH.definition =
  let source_definition, parse_result_opt = extract_def_and_typ_from_source_lines se.sigrng in
  let source_type = "<UNK>" in
  let prompt = "<UNK>" in
  let expected_response = "<UNK>" in
  let opens_and_abbrevs = extract_opens_and_abbrevs se.sigopens_and_abbrevs in
  let vconfig = Option.map jh_of_vconfig se.sigopts in
  let interleaved = BU.basename file_name <> BU.basename (Range.file_of_range se.sigrng) in
  match se.sigel with
  | Sig_declare_typ data ->
    [
      {
        JH.source_range = jh_of_range (heal_dummy_file_name file_name se.sigrng);
        file_name = file_name;
        interleaved = interleaved;
        name = Ident.string_of_lid data.lid;
        type_ = P.term_to_string data.t;
        free_names_in_type = List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars data.t));
        definition1 = "<DECLARETYP>";
        premises = [];
        effect_ = "";
        effect_flags
        =
        (* if a declare typ does not have an assume qualified, then the def will show up *)
        [];
        mutual_with = [];
        proof_features = [];
        is_simple_lemma = false;
        is_div = is_div_typ data.t;
        is_proof = is_propish data.t;
        is_simply_typed = is_simple_type data.t;
        is_type = is_type data.t;
        source_type = source_type;
        source_definition = source_definition;
        prompt = prompt;
        expected_response = expected_response;
        opens_and_abbrevs = opens_and_abbrevs;
        vconfig = vconfig
      }
    ]
  | Sig_assume data ->
    [
      {
        JH.source_range = jh_of_range (heal_dummy_file_name file_name se.sigrng);
        file_name = file_name;
        interleaved = interleaved;
        name = Ident.string_of_lid data.lid;
        type_ = P.term_to_string data.phi;
        free_names_in_type = List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars data.phi));
        definition1 = "<ASSUME>";
        premises = [];
        effect_ = "";
        effect_flags = [];
        mutual_with = [];
        proof_features = [];
        is_simple_lemma = false;
        is_div = is_div_typ data.phi;
        is_proof = is_propish data.phi;
        is_simply_typed = is_simple_type data.phi;
        is_type = is_type data.phi;
        source_type = source_type;
        source_definition = source_definition;
        prompt = prompt;
        expected_response = expected_response;
        opens_and_abbrevs = opens_and_abbrevs;
        vconfig = vconfig
      }
    ]
  | Sig_inductive_typ { params = params ; t = t ; lid = lid ; mutuals = mutuals } ->
    let arr = FStar.Syntax.Util.arrow params (mk_Total t) in
    [
      {
        JH.source_range = jh_of_range (heal_dummy_file_name file_name se.sigrng);
        file_name = file_name;
        interleaved = interleaved;
        name = Ident.string_of_lid lid;
        type_ = P.term_to_string arr;
        free_names_in_type = List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars arr));
        definition1 = "<INDUCTIVETYP>";
        premises = [];
        effect_ = "";
        effect_flags = [];
        mutual_with = List.map Ident.string_of_lid mutuals;
        proof_features = [];
        is_simple_lemma = false;
        is_div = is_div_typ t;
        is_proof = is_propish t;
        is_simply_typed = is_simple_type t;
        is_type = is_type t;
        source_type = source_type;
        source_definition = source_definition;
        prompt = prompt;
        expected_response = expected_response;
        opens_and_abbrevs = opens_and_abbrevs;
        vconfig = vconfig
      }
    ]
  | Sig_bundle bundle -> List.collect (functions_called_by_user_in_def file_name modul) bundle.ses
  | Sig_datacon data ->
    let _, comp = U.arrow_formals_comp data.t in
    let flags = U.comp_flags comp in
    let name = Ident.string_of_lid data.lid in
    [
      {
        JH.source_range = jh_of_range (heal_dummy_file_name file_name se.sigrng);
        file_name = file_name;
        interleaved = interleaved;
        name = name;
        type_ = P.term_to_string data.t;
        free_names_in_type = List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars data.t));
        definition1 = "<DATACON>";
        premises = List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars data.t));
        effect_ = "";
        effect_flags = [];
        mutual_with = List.map Ident.string_of_lid data.mutuals;
        proof_features = [];
        is_simple_lemma = false;
        is_div = is_div_typ data.t;
        is_proof = is_propish data.t;
        is_simply_typed = is_simple_type data.t;
        is_type = is_type data.t;
        source_type = source_type;
        source_definition = source_definition;
        prompt = prompt;
        expected_response = expected_response;
        opens_and_abbrevs = opens_and_abbrevs;
        vconfig = vconfig
      }
    ]
  | Sig_let { lbs = is_rec, lbs } ->
    let maybe_rec =
      match lbs with
      | _ :: _ :: _ -> ["mutual recursion"]
      | _ -> if is_rec then ["recursion"] else []
    in
    let mutual_with =
      match lbs with
      | [] | [_] -> []
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
          let source_type, prompt, expected_response =
            let Inr fv = lb.lbname in
            let st_opt =
              extract_from_parse_result_of_let_binding (FStar.Syntax.Syntax.lid_of_fv fv)
                parse_result_opt
            in
            let st_opt =
              match find_type_from_val_decl (FStar.Syntax.Syntax.lid_of_fv fv) modul with
              | None ->
                (match st_opt with
                  | None -> None
                  | Some (Some p, q, r) -> Some (p, q, r)
                  | Some (None, q, r) -> Some (source_type, q, r))
              | Some p ->
                match st_opt with
                | None -> Some (p, prompt, expected_response)
                | Some (_, prompt, expected_response) -> Some (p, prompt, expected_response)
            in
            BU.dflt (source_type, prompt, expected_response) st_opt
          in
          {
            JH.source_range = jh_of_range (heal_dummy_file_name file_name se.sigrng);
            file_name = file_name;
            interleaved = interleaved;
            name = name;
            type_ = P.term_to_string lb.lbtyp;
            free_names_in_type = List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars lb.lbtyp));
            definition1 = P.term_to_string lb.lbdef;
            premises
            =
            List.map Ident.string_of_lid (Set.elems (FStar.Syntax.Free.fvars lb.lbdef));
            effect_ = Ident.string_of_lid (U.comp_effect_name comp);
            effect_flags = List.map P.cflag_to_string flags;
            is_simple_lemma = is_simple_lemma se;
            is_div = is_div_typ lb.lbtyp;
            is_proof = is_propish lb.lbtyp;
            is_simply_typed = is_simple_type lb.lbtyp;
            is_type = is_type lb.lbtyp;
            mutual_with = mutual_with;
            proof_features = maybe_rec;
            source_type = source_type;
            source_definition = source_definition;
            prompt = prompt;
            expected_response = expected_response;
            opens_and_abbrevs = opens_and_abbrevs;
            vconfig = vconfig
          })
      lbs
  | _ -> []

let read_module_sigelts (source_file: string) : list sigelt =
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

let find_defs_and_premises (source_file: string) : list JH.definition =
  let sigelts = read_module_sigelts source_file in
  List.collect (functions_called_by_user_in_def source_file sigelts) sigelts

let dump_all_lemma_premises_as_json (source_file: string) = find_defs_and_premises source_file

(* prefer an `fsti` over an `fst` *)
let dump_dependency_info_as_json (source_file: string) : JH.dependency =
  match read_checked_file source_file with
  | None -> exit 1
  | Some (cfc_path, cfc) ->
    {
      source_file = source_file;
      checked_file = cfc_path;
      interface_file = List.contains "interface" cfc.deps;
      dependencies1
      =
      List.filter_map (fun dep ->
            BU.bind_opt (map_file_name dep (is_friend cfc dep)) find_file_in_path)
        (List.tail cfc.deps)
    }

// Same as in FStar.CheckedFiles
type checked_file_entry_stage1 = {
  version:int;
  digest:string;
  parsing_data:Parser.Dep.parsing_data
}
type checked_file_entry_stage2 = {
  deps_dig:list (string * string);
  tc_res:tc_result
}

let print_checked_deps (filename: string) =
  let entry:option (checked_file_entry_stage1 * checked_file_entry_stage2) =
    BU.load_2values_from_file filename
  in
  match entry with
  | Some (s1, s2) ->
    let json_of_digest (digest: string) =
      let digest = BU.base64_encode digest in
      JsonStr digest
    in
    let json_of_dep (file_name, digest) =
      JsonAssoc ["module_name", JsonStr file_name; "digest", json_of_digest digest]
    in
    BU.print_string (string_of_json (JsonAssoc
            [
              "source_digest", json_of_digest s1.digest;
              "deps_digest", JsonList (List.map json_of_dep s2.deps_dig)
            ]))

let print_digest (filename: string) =
  BU.print_string (BU.base64_encode (BU.digest_of_file filename))

let main () =
  let usage () =
    print_stderr "Usage: fstar_insights.exe (--all_defs_and_premises | --print_checked_deps | --digest) --include path1 ... --include path_n source_file.(fst|fsti)\n"
      []
  in
  let filenames = BU.mk_ref [] in
  let res =
    FStar.Getopt.parse_cmdline options
      (fun s ->
          filenames := s :: !filenames;
          Getopt.Success)
  in
  match !filenames, res with
  | [filename], Getopt.Success ->
    if !all_defs_and_premises
    then
      let lemmas_premises = dump_all_lemma_premises_as_json filename in
      let deps = dump_dependency_info_as_json filename in
      BU.print_string (string_of_json (JH.json_of_insightfilefirstpass ({
                    defs = lemmas_premises;
                    dependencies = deps
                  })))
    else
      if !print_checked_deps_flag
      then print_checked_deps filename
      else
        if !digest_flag
        then print_digest filename
        else
          (usage ();
            exit 1)
  | _ ->
    usage ();
    exit 1

let _ =
  try
    (FStar.Main.setup_hooks ();
      main ())
  with
  | e ->
    //when false ->
    print_stderr "Exception: %s\n" [BU.print_exn e];
    exit 1
