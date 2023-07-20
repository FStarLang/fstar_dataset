#!/usr/bin/env python3
# Script to build the import graph when pointed at a Fstar
# directory structure. Pass path to `src`, will collect paths.
import pathlib
import itertools
import glob
from tqdm import tqdm
import networkx as nx
from loguru import logger
import matplotlib.pyplot as plt
import json
import argparse

def glob_files(subfolder : str):
    nlogged = 0
    graph = nx.DiGraph()
    globs = [f"{subfolder}/**/*.fst", f"{subfolder}/**/*.fsti"]
    logger.debug(f"globbing folders '{globs}'")
    name2imports = dict() # Stem -> List[Stem]
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
            name2imports[name] = imports
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




if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("path", metavar="P")
    parser.add_argument("--outpath", default="file_import_graph.json")
    options = parser.parse_args()
    out = glob_files(options.path)

    with open(options.outpath, "w") as f:
        json.dump(out, f)
