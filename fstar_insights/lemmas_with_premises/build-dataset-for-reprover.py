#!/usr/bin/env python3
# build dataset for reprover.
# also build jsonl file from the fstar premises.
# Based off of https://github.com/openai/openai-cookbook/blob/main/examples/Obtain_dataset.ipynb

# {
#   "file_name": "/home/t-sibhat/projects/proofml/neural-premise-selection/src/Projects/premise-selection/fstarscraper/everest/hacl-star/providers/evercrypt/EverCrypt.AEAD.fsti",
#   "start_line": 58,
#   "start_col": 2,
#   "end_line": 58,
#   "end_col": 33,
#   "definition": "fun #a s h0 h1 ->\n  EverCrypt.AEAD.freeable #a h0 s ==> EverCrypt.AEAD.freeable #a h1 s <: Prims.Tot Type0",
#   "effect": "Prims.Tot",
#   "effect_flags": [
#     "total"
#   ],
#   "hints": [],
#   "mutual_with": [],
#   "name": "EverCrypt.AEAD.preserves_freeable",
#   "premises": [
#     "Spec.Agile.AEAD.alg",
#     "EverCrypt.AEAD.state",
#     "FStar.Monotonic.HyperStack.mem",
#     "Prims.l_imp",
#     "EverCrypt.AEAD.freeable"
#   ],
#   "proof_features": [],
#   "type": "\n    #a: Spec.Agile.AEAD.alg ->\n    s: EverCrypt.AEAD.state a ->\n    h0: FStar.Monotonic.HyperStack.mem ->\n    h1: FStar.Monotonic.HyperStack.mem\n  -> Prims.Tot Type0"
# }


import os
import openai
import json
import pandas as pd
import tiktoken
from pathlib import Path
import gzip, pickle
from tqdm import tqdm
from typing import *

from openai.embeddings_utils import get_embeddings


def cleanup(s : str) -> str:
    # strip excessive spaces, tabs, newlines
    return ' '.join(s.split())

@dataclass
class Pos:
    line : int
    col : int
    ix : Optional[int]

@dataclass
class Range:
    start : Pos
    end : Pos

@dataclass
class Def:
    # name : typ := body
    name : str # name of the definition
    typ : str # type of the definition
    body : str # body of the definition
    filename : str # file this definition came from.
    file_range : Range # range in file.

@dataclass
class Corpus:
    files : List[File]

class PremiseSelectionRecord:
    defn : str # object that is defined.
    uses : List[str] # premises that are used.

class Dataset:
    corpus : Corpus
    records : List[PremiseSelectionRecord]
    # premise selection examples.
    def write_jsonl(self, records : List[Dict[str, Any]], path : Path):
        with open(path, "w") as f:
            for record in records:
                json.dump(record, f)
                f.write("\n")

    def write_json(self, records : List[Dict[str, Any]], path : Path):
        with open(path, "w") as f:
            json.dump(records, f)

    def build_random(self):
        DATASET_FOLDER = Path("./dataset/")
        nfiles_nonempty = 0
        nfiles_total = 0
        nlemmas = 0
        vocab = set()
        records = []
        records_sample = [] # small sample of records
        for p in tqdm(DATASET_FOLDER.glob("*.json")):
            print(f"reading file '{p}'")
            with open(p, "r") as f:
                nfiles_total += 1
                contents = f.read()
                if not contents:
                    print(" empty")
                    continue
                nfiles_nonempty += 1
                j = json.loads(contents)
                records_sample = [] # small sample of records from a single file
                file = File()
                for content in tqdm(j):
                    content["definition"] = cleanup(content["definition"])
                    content["premises"] = list(map(cleanup, content["premises"]))
                    content["type"] = cleanup(content["type"])
                    is_lemma = "lemma" in content["effect_flags"]
                    nlemmas += int(is_lemma)
                    content["is_lemma"] = is_lemma
                    vocab.add(content["definition"])
                    vocab.add(content["type"])
                    for premise in content["premises"]:
                        vocab.add(premise)
                        records.append(content)
                        records_sample.append(content)
        print(f"read '{nfiles_total}' with #nonempty '{nfiles_nonempty}'. Percentage '{100. * nfiles_nonempty/nfiles_total : 4.2f}'")
        print(f"read '{len(records)}' records with #lemmas '{nlemmas}', Percentage '{100. * nlemmas / len(records) : 4.2f}'")

        for (dataset_path, dataset) in [("dataset_random", records), ("dataset_random_small", records_sample)]:
            TRAIN_SPLIT_IX = int(0.8 * len(dataset))
            TEST_SPLIT = int(0.9 * len(dataset))
            OUT_FOLDER = Path(".") / dataset_path
            os.makedirs(OUT_FOLDER, exist_ok=True) 
            self.write_json(dataset[:TRAIN_SPLIT_IX], OUT_FOLDER / "train.json")        
            self.write_json(dataset[TRAIN_SPLIT_IX:TEST_SPLIT], OUT_FOLDER / "test.json")        
            self.write_json(dataset[TRAIN_SPLIT_IX:TEST_SPLIT], OUT_FOLDER / "validate.json")        

def build_embeds(vocab : Set[str]):
    # embedding model parameters
    embedding_model = "text-embedding-ada-002"
    embedding_encoding = "cl100k_base"  # this the encoding for text-embedding-ada-002
    # encoder = tiktoken.get_encoding(embedding_encoding)
    # max_tokens = 8000  # the maximum for text-embedding-ada-002 is 8191

    openai.organization = "org-BkKFe6jDEL6tnBM8uzo3q0MC"
    openai.api_key = os.getenv("OPENAI_EMBEDDINGS_API_KEY")
    print("openAI models:")
    openai.Model.list()
    print("-----")

    embeds = {}


    class Batcher:
        def __init__(self, vocab : Iterable[str]):
            self.vocab = vocab
            print("building batches...")
            self.batches = list(tqdm(Batcher.chunk_into_tokens(self.vocab)))

        def __iter__(self):
            return self.batches.__iter__()
        def __len__(self):
            return self.batches.__len__()

        @classmethod
        def chunk_into_tokens(cls, words, max_tokens=5000, batch_size=2000):
            # actual max tokens is 8192
            # actual batch size is 2048
            # TODO: use tiktoken to count number of tokens
            it = iter(words)
            while True:
                ws = []
                ntokens = 0
                try:
                    while ntokens < max_tokens and len(ws) < batch_size:
                        w = next(it)
                        # encoding is super expensive, skip it.
                        # ntokens += len(encoder.encode(w))
                        ntokens += len(w)
                        ws.append(w)
                    yield ws
                except StopIteration:
                    return ws # found everything


    embeds = {}
    print(f"total number of words in vocab: {len(vocab)}")
    for ws in tqdm(Batcher(vocab)):
        maxlen = max(map(len, ws))
        print(f"chunk size: {len(ws)} | max word size: {maxlen}")
        if maxlen > 8000:
            print("skipping...")
            print(ws)
            continue # unable to create embedding for this word.


        vecs = get_embeddings(ws, engine=embedding_model)
        print(f"nvecs: {len(vecs)}, dim vec: {len(vecs[0])}")
        for i, w in enumerate(ws):
            embeds[w] = vecs[i]

    with gzip.open("embeddings.pickle.gz", "wb") as f:
        pickle.dump(embeds, f)

if False:
    build_embeds()

if __name__ == "__main__":
    ds = Dataset()
    ds.build_random()
