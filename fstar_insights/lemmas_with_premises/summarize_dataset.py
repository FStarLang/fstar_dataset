#!/usr/bin/env python3
# Summarize dataset (number of lemmas, number of defintions) from dataset
# extracted by `lemma_and_premises`

import json
import glob
from tqdm import tqdm
from dataclasses import dataclass
from typing import *
from loguru import logger

@dataclass
class Summary:
    nlemmas : int = 0
    ntotal : int = 0
    npremises_without_defs : int = 0


def summarize(dataset_glob_regex : str) -> Summary:
    summary = Summary()
    defs = set()
    premises = set()
    premise2users :Dict[str, List[str]] = dict()
    for fp in tqdm(glob.glob(dataset_glob_regex)):
        logger.info(f"processing {fp}")
        with open(fp, "r") as f:
            fstr = f.read().strip()
            if not fstr:
                logger.info("  empty file. skipping...")
                continue
            first_record = True
            j = json.loads(fstr)
            records = j["defs"]
            for record in records:
                defs.add(record["name"])
                summary.ntotal += 1
                premises.update(record["premises"])
                for premise in record["premises"]:
                    if premise not in premise2users:
                        premise2users[premise] = []
                    premise2users[premise].append(f'{record["name"]}: {record["file_name"]}:{record["start_line"]}')
                if "lemma" in record["effect_flags"]:
                    summary.nlemmas += 1
    summary.npremises_without_defs = len(premises) - len(premises.intersection(defs))
    print("=========")
    for premise in sorted(premises):
        if premise not in defs:
            print(f"premise: {premise} | users:")
            for user in premise2users[premise]:
                print(f"  - {user}")
            print("----")

    return summary

    
out = summarize("./dataset/*.json")
print(out)


