#!/usr/bin/env python3
# Script to build the import graph when pointed at a Fstar
# directory structure. Pass path to `src`, will collect paths.
# $ ./build_fstar_import_graph.py ~/temp/fstarscraper_old_2/everest ./dataset/
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

def glob_files(subfolder : str, name2imports: Dict[str, Set[str]]):
    nlogged = 0
    graph = nx.DiGraph()
    globs = [f"{subfolder}/**/*.fst", f"{subfolder}/**/*.fsti"]
    logger.debug(f"globbing folders '{globs}'")
    for path in tqdm(itertools.chain(*[glob.glob(g, recursive=True) for g in globs])):
        nlogged += 1
        path = pathlib.Path(path)
        name = path.stem # 'Blah' from 'foo/bar/Blah.{fst,fsti}'
        logger.debug(f"stem: {path.stem:30} | path: {path}")
        with open(path, "r") as f:
            path = pathlib.Path(path)
            graph.add_node(name)
            imports = [line for line in f.readlines() if line.startswith("open")]
            imports = [line.split("open")[1].strip() for line in imports]
            if name not in name2imports:
                name2imports[name] = set()
            name2imports[name] = name2imports[name].union(imports)
            # logger.info(f"{name} → '{','.join(imports)}'")
            for dep in imports:
                graph.add_node(dep)
                graph.add_edge(name, dep) # make edge cur → dependency

            if nlogged <= 1:
                logger.debug(f"imports: {imports}")

    # Fstar has an import cycle?!
    if not nx.is_directed_acyclic_graph(graph):
        for cyc in nx.chordless_cycles(graph):
            logger.error(f"cycle: '{','.join(cyc):70}'")
    # assert nx.is_directed_acyclic_graph(graph)
    # nx.draw(graph)
    # plt.show()
    return name2imports

def process_dataset_for_imports(name2imports: Dict[str, Set[str]]):
    def2filename = dict()
    for path in tqdm(glob.glob("./dataset/*.json", recursive=True)):
        f = open(path).read().strip()
        if not f: continue
        for record in json.loads(f):
            defn_name = record["name"]
            filename = pathlib.Path(record["file_name"]).stem
            def2filename[defn_name] = filename

    for path in tqdm(glob.glob("./dataset/*.json", recursive=True)):
        f = open(path).read().strip()
        if not f: continue
        for record in json.loads(f):
            for premise in record["premises"]:
                name = pathlib.Path(record["file_name"]).stem
                if name not in name2imports:
                    name2imports[name] = set()

                # for each premise, add premise into 
                # import list of name.
                for premise in record["premises"]:
                    if premise not in def2filename: continue
                    # logger.info(f"{name} → '{def2filename[premise]}'")
                    name2imports[name].add(def2filename[premise])
    return name2imports
    

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("path", metavar="P")
    parser.add_argument("--outpath", default="file_import_graph.json.gz")
    options = parser.parse_args()
    name2imports = process_dataset_for_imports(dict())
    name2imports = glob_files(options.path, name2imports)

    for name in list(name2imports.keys())[:10]:
        logger.info(f"{name} → '{','.join(name2imports[name])}'")

    with gzip.open(options.outpath, "w") as f:
        records = [{"name": name, "imports": list(name2imports[name])} for name in name2imports]
        out = json.dumps(records)
        f.write(out.encode("utf-8"))
