#!/usr/bin/env python3
import json
import tqdm
import glob

names = set()
for fpath in tqdm.tqdm(list(glob.glob("*.json"))):
    data  = open(fpath, "rb").read()
    if not data.strip(): continue
    # print(f"processing '{fpath}'")
    f = json.loads(data)
    for entry in f["defs"]:
        if entry["file_name"].strip() == "dummy":
            full_name = entry["name"]
            name = full_name.split(".")[-1]
            # print(name)
            if name.startswith("__proj__"): continue
            if "uu___" in name: continue
            print(f"name: '{full_name:30s}' file: '{fpath:40s}'")
            names.add(full_name)
print("\n".join(sorted(list(set(names)))))

