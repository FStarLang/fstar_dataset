#!/usr/bin/env python3
import glob
import sys
import shutil
import os.path

def stripext(fn): return os.path.splitext(fn)[0]
basename = os.path.basename

os.makedirs('dataset', exist_ok=True)

already_copied = {}
for dirn in sys.argv[1:]:
    fst_files = { basename(fn): fn for fn in glob.iglob(f'{dirn}/**/*.fst', recursive=True) }
    fsti_files = { basename(fn): fn for fn in glob.iglob(f'{dirn}/**/*.fsti', recursive=True) }
    checked_files = { stripext(basename(fn)): fn for fn in glob.iglob(f'{dirn}/**/*.checked', recursive=True, include_hidden=True) }
    for bn, cfn in checked_files.items():
        if bn in already_copied:
            print(f'{cfn} already seen before: {already_copied[bn]}')
            continue
        src = fst_files.get(bn) or fsti_files.get(bn)
        if not src:
            print(f'{cfn} does not have associated source file')
            continue
        shutil.copy(src, 'dataset/')
        shutil.copy(cfn, 'dataset/')
        already_copied[bn] = cfn
