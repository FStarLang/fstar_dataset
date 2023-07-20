#!/usr/bin/env python3
# Summarize dataset (number of lemmas, number of defintions) from dataset
# extracted by `lemma_and_premises`

import json
import glob
from tqdm import tqdm
from dataclasses import dataclass


@dataclass
class Summary:
    nlemmas : int = 0
    ntotal : int = 0
    npremises_without_defs : int = 0


def summarize(dataset_glob_regex : str) -> Summary:
    summary = Summary()
    defs = set()
    premises = set()
    for fp in tqdm(glob.glob(dataset_glob_regex)):
        print(f"processing {fp}")
        with open(fp, "r") as f:
            fstr = f.read().strip()
            if not fstr:
                print("  empty file. skipping...")
                continue
            first_record = True
            records = json.loads(fstr)
            for record in records:
                if first_record:
                    print(f"record keys: '{record.keys()}'")
                defs.add(record["name"])
                summary.ntotal += 1
                premises.update(record["premises"])
                if "lemma" in record["effect_flags"]:
                    summary.nlemmas += 1
    summary.npremises_without_defs = len(premises) - len(premises.intersection(defs))

    return summary

    
out = summarize("./dataset/*.json")
print(out)



