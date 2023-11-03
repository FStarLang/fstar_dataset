#!/usr/bin/env python3
from typing import Any
from functools import cache
import glob
import sys
import shutil
import os.path
import subprocess
import multiprocessing
import tqdm
import json

def run_insights(*args):
    return subprocess.check_output(['fstar_insights/ocaml/bin/fstar_insights.exe'] + list(args), encoding='utf-8')

def run_digest(fn) -> tuple[str, str]:
    return fn, run_insights('--digest', fn)

def run_print_checked_deps(fn) -> tuple[str, Any, str]:
    return fn, json.loads(run_insights('--print_checked_deps', fn)), run_insights('--digest', fn)

def run_extract(fn):
    out = run_insights('--include', 'dataset', '--all_defs_and_premises', fn)
    open(f'dataset/{fn}.json', 'w').write(out)

def main():
    os.makedirs('dataset', exist_ok=True)

    dirs = sys.argv[1:]

    pool = multiprocessing.Pool()

    fns = [ fn for dir in dirs for fn in glob.iglob(f'{dir}/**/*.fst*.checked', recursive=True, include_hidden=True) if not os.path.isdir(fn) ]
    checked_deps = tqdm.tqdm(pool.imap_unordered(run_print_checked_deps, fns), total=len(fns), desc='Parsing checked files')
    checked_deps = { dig: (fn, j) for fn, j, dig in checked_deps }
    expected_source_fns = set(os.path.splitext(os.path.basename(fn))[0] for fn, _ in checked_deps.values())

    fns = [ fn for dir in dirs for fn in glob.iglob(f'{dir}/**/*.fst*', recursive=True, include_hidden=True) \
        if not os.path.isdir(fn) and os.path.basename(fn) in expected_source_fns ]
    digs = list(tqdm.tqdm(pool.imap_unordered(run_digest, fns), total=len(fns), desc='Computing source digests'))
    digest2src: dict[str, list[str]] = {}
    for fn, dig in digs:
        if dig not in digest2src: digest2src[dig] = []
        digest2src[dig].append(fn)

    basename2files: dict[str, tuple[str, str]] = {}
    @cache
    def resolve_checked(dig: str) -> bool:
        if dig not in checked_deps: return False
        checked_fn, dep_info = checked_deps[dig]
        basename = os.path.splitext(os.path.basename(checked_fn))[0]
        if basename.startswith('Test.fst'):
            print(f'Skipping {checked_fn} because name causes lots of shadowing')
            return False
        if basename in basename2files:
            print(f'Skipping duplicate module {checked_fn} in favor of {basename2files[basename]}')
            return False
        src_fn = None
        for src_fn_cand in digest2src.get(dep_info['source_digest'], []):
            if os.path.basename(src_fn_cand) == basename:
                src_fn = src_fn_cand
                break
        if src_fn is None:
            print(f'Skipping {checked_fn} because of unavailable source file')
            return False
        for dep in dep_info['deps_digest']:
            if dep['module_name'] == 'source':
                assert dep['digest'] == dep_info['source_digest'] # duplicate info
            else:
                if not resolve_checked(dep['digest']):
                    print(f'Skipping {checked_fn} because of unavailable dependency {dep["module_name"]}')
                    return False
        if basename in basename2files:
            print(f'Skipping duplicate module {checked_fn} in favor of {basename2files[basename]}')
            return False
        basename2files[basename] = (checked_fn, src_fn)
        return True

    for dig in checked_deps.keys(): resolve_checked(dig)

    for checked_fn, src_fn in tqdm.tqdm(basename2files.values(), desc = 'Copying files'):
        shutil.copy(src_fn, 'dataset/')
        shutil.copy(checked_fn, 'dataset/')

    list(tqdm.tqdm(pool.imap_unordered(run_extract, basename2files.keys()), total=len(basename2files), desc='Extracting insights'))

if __name__ == '__main__':
    main()
