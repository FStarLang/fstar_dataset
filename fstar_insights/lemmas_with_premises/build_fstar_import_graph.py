#!/usr/bin/env python3
# Script to build the import checked2imports_graph when pointed at a Fstar
# directory structure. Pass path to `src`, will collect paths.
# $ ./build_fstar_import_graph.py ~/temp/fstarscraper_old_2/everest ./dataset/
# to see one of the dataset files, perform '$ jq "" dataset/Vale.PPC64LE.InsVector.json  | vim -'
# jq "" dataset/Vale.PPC64LE.InsVector.json  | vim -

import pathlib
import itertools
import glob
from tqdm import tqdm
import networkx as nx
from loguru import logger
import matplotlib.pyplot as plt
import json
import argparse
from typing import *
import gzip
from loguru import logger

class Globber:
    # checked file -> iported checked files.
    checked2imports: dict[str, List[str]]
    # source fst/fsti <-> checked file
    source2checked: dict[str, str]
    checked2source: dict[str, str]
    # number of <unk> dependencies for a checked file
    checked2num_unk : dict[str, int]
    # import graphs
    checked2imports_graph : nx.DiGraph
    checked2imports_graph_trans : nx.DiGraph
    # source/checked file name -> json path
    source2jsonpath: dict[str, pathlib.Path]
    checked2jsonpath: dict[str, pathlib.Path]
    # defn name -> paths
    name2checked_defn : Dict[str, str] = dict()
    name2checked_decl : Dict[str, str] = dict()
    name2source : Dict[str, str] = dict()
    # name2jsonpath : Dict[str, pathlib.Path] = dict()

    # defn name -> def
    # name2defn : Dict[str, Dict[str, Any]] = dict()

    def __init__(self):
        self.checked2imports = dict()
        self.source2checked = dict()
        self.source2jsonpath = dict()
        self.checked2jsonpath = dict()

        self.name2checked_defn = dict()
        self.name2checked_decl = dict()
        # self.name2source = dict()
        # self.name2jsonpath = dict()
        # self.name2defn = dict()

        self.checked2source = dict()
        self.checked2num_unk = dict()
        self.checked2imports_graph = nx.DiGraph()

    def _process_dependency(self, path : pathlib.Path, dep : dict[str, Any]):
        source_name = pathlib.Path(dep["source_file"]).name
        checked_name = pathlib.Path(dep["checked_file"]).name
        # checked_name = checked_name.replace(".fst.checked", ".fsti.checked") # cheat and point everything to `fsti`.

        # if the previous def came from an fsti file, then replace the previous def, but not the previous location!
        if source_name in self.source2checked:
            assert source_name in self.source2jsonpath
            logger.warning(f"duplicates of source name '{source_name}' from '{str(path)}'. Previously from '{self.source2jsonpath[source_name]}'")
            assert False

        if checked_name in self.checked2source:
            assert checked_name in self.checked2jsonpath
            logger.warning(f"duplicates of checked name '{checked_name}' from '{str(path)}'. Previous from '{self.checked2jsonpath[checked_name]}'")
            assert False

        self.source2jsonpath[source_name] = path
        self.checked2jsonpath[checked_name] = path

        self.checked2source[checked_name] = source_name
        self.source2checked[source_name] = checked_name
        self.checked2imports_graph.add_node(checked_name)
        # self.checked2imports_graph.add_edge(checked_name, "dummy.checked")
        self.checked2imports_graph.add_edge(checked_name, "prims.fst.checked") # TODO: shouldn't need this, is available?

        if ".fst.checked" in checked_name:
            fsti_dep = checked_name.split(".fst.checked")[0] + ".fsti.checked"
            logger.info(f"adding fst → fsti dep '{checked_name}' → '{fsti_dep}'")
            self.checked2imports_graph.add_edge(checked_name, fsti_dep) # make edge cur → dependency

        # TODO: this is a hack that adds a dependency of the fsti onto the fst x( 
        # if ".fsti.checked" in checked_name:
        #     fst_dep = checked_name.split(".fsti.checked")[0] + ".fst.checked"
        #     logger.info(f"adding fsti → fst dep '{checked_name}' → '{fst_dep}'")
        #     self.checked2imports_graph.add_edge(checked_name, fst_dep) # make edge cur → dependency

        imports = sorted(list(set([pathlib.Path(imp).name for imp in dep["dependencies"]])))
        self.checked2imports[checked_name] = imports

        num_unk = sum([impot == "<UNK>" for impot in imports])
        # name2nmissing[path] = 0 if len(imports) == 0 else nmissing / len(imports)
        self.checked2num_unk[checked_name] = num_unk

        for imp in imports:
            # imp = imp.replace(".fst.checked", ".fsti.checked") # cheat and only bind to fsti.
            # if "fst" in imp and "fsti" not in imp:
            #     logger.error(f"unexpected 'fst' import '{imp}' in file '{str(path)}'")
            self.checked2imports_graph.add_node(imp)
            self.checked2imports_graph.add_edge(checked_name, imp) # make edge cur → dependency
            logger.info(f"adding dependency {checked_name} → {imp}")


    def glob_files(self, subfolder : str):
        paths_str = list(glob.glob(f"{subfolder}/**/*.json", recursive=True))
        for path_str in tqdm(paths_str):
            path = pathlib.Path(path_str)
            dataset_str = open(path).read()
            if not dataset_str.strip(): continue # some files are empty
            dataset = json.loads(dataset_str)
            for dep in dataset["dependencies"]:
                self._process_dependency(path, dep)


        logger.info("--- missing statistics ---")
        for (checked, nmissing) in sorted(self.checked2num_unk.items(), key=lambda kv: kv[1]):
            logger.info(f"#missing {str(checked):50s} : {nmissing:4d}")
        logger.info("---")

        # Fstar has an import cycle?!
        if not nx.is_directed_acyclic_graph(self.checked2imports_graph):
            for cyc in nx.chordless_cycles(self.checked2imports_graph):
                logger.error(f"cycle: '{','.join(cyc):70}'")

        logger.info("building transitive closure of import graph...")
        self.checked2imports_graph_trans = nx.transitive_closure(self.checked2imports_graph, reflexive=True)
        logger.info("built!")
        self._verify_premise_def_relation(subfolder)

    def _raise_verification_error(self, old_def : Dict[str, Any], cur_def: Dict[str, Any]):
        logger.error(f"old: {old_def}")
        logger.error(f"cur: {cur_def}")

    @staticmethod
    def _is_same_record(old : Dict[str, Any], new : Dict[str, Any]):
        return (old["name"] == new["name"] and \
                old["start_line"] == new["start_line"] and \
                old["start_col"] == new["start_col"] and \
                pathlib.Path(old["file_name"]).name == pathlib.Path(new["file_name"]).name) or \
                old["definition"] == new["definition"] 

    def _verify_premise_def_relation(self, subfolder : str):
        dummy_def_names = set()
        all_def_names = set()
        paths = list(glob.glob(f"{subfolder}/**/*.json", recursive=True))
        for path_str in tqdm(paths):
            path = pathlib.Path(path_str)
            dataset_str = open(path).read()
            if not dataset_str.strip(): continue # some files are empty
            dataset = json.loads(dataset_str)
            for defn in dataset["defs"]:
                all_def_names.add(defn["name"])
                if "dummy" in defn["file_name"]:
                    dummy_def_names.add(defn["name"])
                    continue # skip all dummy defs.
                name = defn["name"]
                source_file_name = pathlib.Path(defn["file_name"]).name.strip()

                # === handle source location of declarations (self2checked) ===
                if source_file_name.endswith("fsti"): #fsti can override fsts
                    if name in self.name2checked_decl:
                        overriding_fst = self.name2checked_decl[name].endswith(".fst.checked") # make sure that we are only overriding an fst definition.
                        # TODO: Ask Nic why it is that we get duplicate defs that point to the same checked file.
                        checked_file_eq = self.name2checked_decl[name] == self.source2checked[source_file_name] # either that, or we have the same checked file.
                        if not overriding_fst and not checked_file_eq: # and not is_same:
                            logger.error(f"overriding_fst: {overriding_fst}")
                            logger.error(f"name: {name}")
                            logger.error(f"old checked: {self.name2checked_defn[name]}")
                            logger.error(f"new source file name: {source_file_name}")
                            logger.error(f"new checked: {self.source2checked[source_file_name]}")
                            assert False
                    self.name2checked_decl[name] = self.source2checked[source_file_name]
                elif name not in self.name2checked_decl: # only add stuff from fst once
                    assert source_file_name.endswith(".fst")
                    self.name2checked_decl[name] = self.source2checked[source_file_name]

                # === handle source location of definitions (self2checked) ===
                if source_file_name.endswith("fst"): #fst can override fsti
                    if name in self.name2checked_defn:
                        overriding_fsti = self.name2checked_defn[name].endswith(".fsti.checked") # make sure that we are only overriding an fst definition.
                        checked_file_eq = self.name2checked_defn[name] == self.source2checked[source_file_name]
                        if not overriding_fsti and not checked_file_eq: # and not is_same:
                            logger.error(f"overriding_fsti: {overriding_fsti}")
                            logger.error(f"name: {name}")
                            logger.error(f"old checked: {self.name2checked_defn[name]}")
                            logger.error(f"new source file name: {source_file_name}")
                            logger.error(f"new checked: {self.source2checked[source_file_name]}")
                            assert False
                    self.name2checked_defn[name] = self.source2checked[source_file_name]
                elif name not in self.name2checked_defn: # only add stuff from fsti once
                    assert source_file_name.endswith(".fsti")
                    self.name2checked_defn[name] = self.source2checked[source_file_name]

                assert name in self.name2checked_defn
                assert name in self.name2checked_decl

        num_without_correct_edges = 0
        num_total = 0
        incorrect_edges_dump = ""
        num_missing_edge = 0
        for path_str in tqdm(paths):
            path = pathlib.Path(path_str)
            dataset = open(path).read()
            if not dataset.strip(): continue # some files are empty
            dataset = json.loads(dataset)
            for defn in dataset["defs"]:
                name = defn["name"]
                if name not in self.name2checked_defn: continue
                def_checked = self.name2checked_defn[name]
                for premise in defn["premises"]:
                    if premise not in self.name2checked_decl:
                        logger.error(f"premise without checked declaration file '{premise}'")
                        continue
                    premise_checked = self.name2checked_decl[premise]
                    num_total += 1
                    if not self.checked2imports_graph_trans.has_edge(def_checked, premise_checked):
                        num_without_correct_edges += 1
                        logger.error(f"unable to find expected edge from def '{name}:{def_checked}' → premise '{premise}:{premise_checked}'")
                        # logger.error(f"  this was on account of def '{name}' for premise '{premise}' in '{str(path)}'")
                        num_missing_edge += 1
        logger.info(f"#defs without correct edges: {num_without_correct_edges}  / {num_total} = {num_without_correct_edges/num_total*100:4.2f} %%")
        num_dummy_defs = len(dummy_def_names); num_total_defs = len(all_def_names)
        logger.info(f"#dummy defs: {num_dummy_defs} / {num_total_defs} = {num_dummy_defs / num_total_defs * 100:4.2f} %%")

                

# def process_dataset_for_imports(file2imports: Dict[str, Set[str]]):
#     def2filename = dict()
#     for path in tqdm(glob.glob("./dataset/*.json", recursive=True)):
#         f = open(path).read().strip()
#         if not f.strip(): continue
#         for record in json.loads(f)["defs"]:
#             defn_name = record["name"]
#             filename = pathlib.Path(record["file_name"]).stem
#             def2filename[defn_name] = filename
# 
#     for path in tqdm(glob.glob("./dataset/*.json", recursive=True)):
#         f = open(path).read().strip()
#         if not f: continue
#         for record in json.loads(f)["defs"]:
#             for premise in record["premises"]:
#                 name = pathlib.Path(record["file_name"]).stem
#                 if name not in file2imports:
#                     file2imports[name] = set()
# 
#                 # for each premise, add premise into 
#                 # import list of name.
#                 for premise in record["premises"]:
#                     if premise not in def2filename: continue
#                     # logger.info(f"{name} → '{def2filename[premise]}'")
#                     file2imports[name].add(def2filename[premise])
#     return file2imports
    

# def verify_name2imports(file2imports: dict):
#     def2filename = dict()
# 
#     for path in tqdm(glob.glob("./dataset/*.json", recursive=True)):
#         f = open(path).read().strip()
#         if not f.strip(): continue
#         for record in json.loads(f)["defs"]:
#             defn_name = record["name"]
#             filename = pathlib.Path(record["file_name"]).stem
#             def2filename[defn_name] = filename
# 
#     for path in tqdm(glob.glob("./dataset/*.json", recursive=True)):
#         f = open(path).read().strip()
#         if not f: continue
#         for record in json.loads(f)["defs"]:
#             defn_name = record["name"]
#             assert defn_name in def2filename
#             for premise in record["premises"]:
#                 if premise not in def2filename:
#                     logger.warning("***missing premise: {premise}***")
#                 name = pathlib.Path(record["file_name"]).stem
#                 if name not in file2imports:
#                     file2imports[name] = set()
# 
#                 # for each premise, add premise into 
#                 # import list of name.
#                 for premise in record["premises"]:
#                     if premise not in def2filename: continue
#                     # logger.info(f"{name} → '{def2filename[premise]}'")
#                     file2imports[name].add(def2filename[premise])
#     return file2imports

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_folder", default="dataset/")
    parser.add_argument("--outpath", default="file_import_graph.json.gz")
    options = parser.parse_args()
    # file2imports = dict()
    # file2imports = process_dataset_for_imports(file2imports)
    # file2imports = glob_files(options.input_folder, file2imports)

    g = Globber()
    g.glob_files(options.input_folder)

    for checked in list(g.checked2imports.keys())[:10]:
        logger.info(f"{checked} → '{','.join(g.checked2imports[checked])}'")

    with gzip.open(options.outpath, "w") as f:
        records = [{"source": g.checked2source[checked], 
                    "checked": checked,
                    "imports": list(g.checked2imports[checked]) }
                   for checked in g.checked2imports]
        out = json.dumps(records)
        f.write(out.encode("utf-8"))

# {
#   "defs": [
#     {
#       "file_name": "/home/guido/r/everest/hacl-star/obj/Vale.PPC64LE.InsVector.fsti",
#       "start_line": 27,
#       "start_col": 2,
#       "end_line": 27,
#       "end_col": 22,
#       "definition": "fun b i v h ->\n  Vale.PPC64LE.Memory.buffer_write #Vale.PPC64LE.Memory.vuint128 b i v h\n  <:\n  Prims.Ghost Vale.PPC64LE.Memory.vale_heap",
#       "effect": "Prims.Ghost",
#       "effect_flags": [],
#       "mutual_with": [],
#       "name": "Vale.PPC64LE.InsVector.buffer128_write",
#       "premises": [
#         "Vale.PPC64LE.Memory.buffer128",
#         "Prims.int",
#         "Vale.PPC64LE.Memory.quad32",
#         "Vale.PPC64LE.Memory.vale_heap",
#         "Vale.PPC64LE.Memory.buffer_write",
#         "Vale.PPC64LE.Memory.vuint128",
#         "Prims.l_and",
#         "Vale.PPC64LE.Memory.buffer_readable",
#         "Vale.PPC64LE.Memory.buffer_writeable",
#         "Prims.l_True"
#       ],
#       "proof_features": [],
#       "type": "\n    b: Vale.PPC64LE.Memory.buffer128 ->\n    i: Prims.int ->\n    v: Vale.PPC64LE.Memory.quad32 ->\n    h: Vale.PPC64LE.Memory.vale_heap\n  -> Prims.Ghost Vale.PPC64LE.Memory.vale_heap"
#     },
#     ...
#   "dependencies": [
#     {
#       "source_file": "./raw_dataset/Vale.PPC64LE.InsVector.fst",
#       "checked_file": "././raw_dataset/Vale.PPC64LE.InsVector.fst.checked",
#       "dependencies": [
#         "<UNK>",
#         "./raw_dataset/Vale.SHA.PPC64LE.SHA_helpers.fsti.checked",
#         "./raw_dataset/Vale.PPC64LE.State.fsti.checked",
#         "./raw_dataset/Vale.PPC64LE.Semantics_s.fst.checked",
#         "./raw_dataset/Vale.PPC64LE.Memory_Sems.fsti.checked",
#         "./raw_dataset/Vale.PPC64LE.Machine_s.fst.checked",
#         "./raw_dataset/Vale.PPC64LE.Decls.fsti.checked",
#         "./raw_dataset/Vale.PPC64LE.Decls.fsti.checked",
#         "./raw_dataset/Vale.Def.Words_s.fsti.checked",
#         "./raw_dataset/Vale.Def.Types_s.fst.checked",
#         "./raw_dataset/Vale.Arch.Types.fsti.checked",
#         "./raw_dataset/Spec.SHA2.fsti.checked",
#         "./raw_dataset/Spec.Hash.Definitions.fst.checked",
#         "./raw_dataset/prims.fst.checked",
#         "./raw_dataset/FStar.Pervasives.Native.fst.checked",
#         "./raw_dataset/FStar.Pervasives.fsti.checked"
#       ],
#       "depinfo": true
#     }
#   ]
# a.fsti: provides a signature for 'val f'
# b.fst: make use of 'a.f'
# the defn of f is not in scope for b, only the signature is.
