#!/usr/bin/env python3
# Provide path to dataset/ as produced by `summarize_dataset.py`.
from typing import *
import tarfile
from tqdm import tqdm
import re
from pysmt.smtlib.parser import SmtLibParser
from dataclasses import dataclass, asdict
import json
from pathlib import Path
import glob

@dataclass
class DefinitionsDataset:
    name2def : Dict[str, Dict[str, Any]]

    def __init__(self, glob_regex : str):
        self.name2def = dict()
        self.load(glob_regex)

    def load(self, glob_regex : str):
        for fp in tqdm(glob.glob(glob_regex)):
            print(f"processing {fp}")
            with open(fp, "r") as f:
                fstr = f.read().strip()
                if not fstr:
                    print("  empty file. skipping...")
                    continue
                for record in json.loads(fstr):
                    assert record["name"] not in self.name2def
                    self.name2def[record["name"]] = record

## ; QUERY ID: (EverParse3d.Actions.All.action_field_ptr_after, 1)
## ; STATUS: unsat
## ; UNSAT CORE GENERATED: @MaxIFuel_assumption, @query, constructor_distinct_EverParse3d.Actions.Base.BackendFlagBuffer, constructor_distinct_EverParse3d.Actions.Base.BackendFlagExtern, equality_tok_EverParse3d.Actions.Base.BackendFlagBuffer@tok, equality_tok_EverParse3d.Actions.Base.BackendFlagExtern@tok, function_token_typing_EverParse3d.Actions.BackendFlagValue.backend_flag_value, refinement_interpretation_Tm_refine_1d84d00e87ebf3171eb432e6796020a1, refinement_interpretation_Tm_refine_6447c87b81c19e28ed89bc5dda0af8c5
## 
WRITE_FILE_OUT=True
def find_last_match(regex : Pattern[str], haystack : str) -> Optional[str]:
    matches = re.findall(regex, haystack)
    if matches:
        return matches[-1]
    return None

def find_last_substring_occurrence(substring : str, haystack : str) -> int:
    cur = -1
    while True:
        next_ = haystack.find(substring, cur+1)
        if next_ == -1:
            return cur
        else:
            cur = next_

def parse_next_sexpr(s : str) -> str:
    opens = []
    assert s[0] == '(', "expected s-expression"
    ix = 1
    opens.append(ix)
    while opens:
        assert ix < len(s)
        peek = s[ix]
        if peek == ')':
            opens.pop()
            if not opens:
                return s[:ix]
        if peek == '(':
            opens.append(ix)
        ix += 1

def sexpr_delete_comments(s : str) -> str:
    return " ".join([line.strip() for line in s.split("\n") if line.strip() and (";;" not in line)])


@dataclass
class Record:
    query_name : str
    query_ix : int
    assertion : str
    unsat_core : List[str]

def read_file(file_name, lines : List[str]) -> Record:
    print(f"file: '{file_name}': #lines: '{len(lines)}'")
    data = "".join(lines)
    global WRITE_FILE_OUT
    if WRITE_FILE_OUT:
        with open("sample.smt2", "w") as f: f.write(data)
        WRITE_FILE_OUT = False
    query_id = find_last_match(re.compile("QUERY ID: \((.*), (.*)\)"), data)
    query_name = query_id[0]
    query_ix = query_id[1]
    print(f"  query name: '{query_name}' | query index: '{query_ix}'")
    unsat_core = find_last_match(re.compile("UNSAT CORE GENERATED: (.*)"), data)
    assert unsat_core is not None, "expected valid unsat core"
    unsat_core = [s.strip() for s in unsat_core.split(",")]
    print("  unsat core: (" + ", ".join(map(lambda s : f"'{s}'", unsat_core)) + ")")

    # Make file way smaller by looking for the last occurrence of '(assert and trimming from there.
    assert_ix = find_last_substring_occurrence("(assert" , data)
    print(f"found '(assert' at '{assert_ix}'")
    assert assert_ix > -1, "Expected occurrence of '(assert' in data"
    assert_cmd = sexpr_delete_comments(parse_next_sexpr(data[assert_ix:]))
    print(f"  assert: '{assert_cmd}'")

    return Record(query_name=query_name,
                  query_ix=query_ix,
                  assertion=assert_cmd,
                  unsat_core=unsat_core)

def read_info(f : tarfile.TarFile, info : tarfile.TarInfo, defs : DefinitionsDataset, outf : IO):
    print(f"processing '{info.name}'")
    if not info.isfile: return
    print(f"reading '{info.name}'")
    data = f.extractfile(info)
    assert data is not None
    lines = [l.decode("utf-8") for l in data.readlines()]
    record = read_file(info.name, lines)

    out = asdict(record)
    if record.query_name not in defs.name2def:
        # all_defs_debug_print = "\n  -".join(defs.name2def.keys())
        # print(f"have defs for:\n{all_defs_debug_print}")
        print (f" NOT FOUND query_name: '{record.query_name}'")
        print (f" NOT FOUND assertion: '{record.assertion}'")
        return # give up on this record
    else:
        assert record.query_name in defs.name2def
        lemma_dict = defs.name2def[record.query_name]
        out.update(lemma_dict)
        json.dump(out, outf)
        outf.write("\n")
        outf.flush()

def read_tar(tarpath : str, defs : DefinitionsDataset, outpath : str):
    print("opening tarfile...")
    f = tarfile.open(tarpath)
    outf = open(outpath, "w")
    for info in tqdm(f):
        try:
            read_info(f, info, defs, outf)
        except AssertionError as e:
            print(f"  Failed info. Error: '{e}'. continuing...")


# read_tar("./all_queries_sorted_2023-07-13T19:40:21-07:00.tgz", "all_queries.jsonl")
read_tar("/home/t-sibhat/guido-everest-dataset/all_queries_sorted_2023-07-13T19:40:21-07:00.tgz",
         DefinitionsDataset("./dataset/*.json"),
         "unsat_core_dataset.jsonl")
