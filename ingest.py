#!/usr/bin/env python3
import glob
import sys
import shutil
import os.path

def stripext(fn): return os.path.splitext(fn)[0]
basename = os.path.basename

os.makedirs('dataset', exist_ok=True)

def myglob(pat: str):
    for fn in glob.iglob(pat, recursive=True, include_hidden=True):
        if '/reclaimable/' in fn: continue
        if '/examples/' in fn: continue
        if '/.scripts/' in fn: continue
        if '/FStar/src/' in fn: continue
        yield fn

already_copied = {}
for dirn in sys.argv[1:]:
    fst_files = { basename(fn): fn for fn in myglob(f'{dirn}/**/*.fst') }
    fsti_files = { basename(fn): fn for fn in myglob(f'{dirn}/**/*.fsti') }
    checked_files = { stripext(basename(fn)): fn for fn in myglob(f'{dirn}/**/*.checked') }
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
