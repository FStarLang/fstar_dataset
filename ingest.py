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
from fstar_harness import InsightFile, InsightFileFirstPass

def run_insights(*args):
    return subprocess.check_output(['fstar_insights/ocaml/bin/fstar_insights.exe'] + list(args), encoding='utf-8')

def run_digest(fn) -> tuple[str, str]:
    return fn, run_insights('--digest', fn)

def run_print_checked_deps(fn) -> tuple[str, Any, str]:
    return fn, json.loads(run_insights('--print_checked_deps', fn)), run_insights('--digest', fn)

def run_extract(fn_orig_src_fn: tuple[str, str]):
    fn, orig_src_fn = fn_orig_src_fn
    try:
        out: InsightFileFirstPass = json.loads(run_insights('--include', 'dataset', '--all_defs_and_premises', fn))
    except:
        sys.stderr.write(f'Cannot extract {fn}\n'); sys.stderr.flush()
        return

    orig_dir = os.path.dirname(orig_src_fn)
    git_rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=orig_dir, encoding='utf-8').strip()
    git_repo_dir = subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=orig_dir, encoding='utf-8').strip()
    source_file_name = os.path.relpath(os.path.realpath(orig_src_fn), git_repo_dir)
    git_url = subprocess.check_output(['git', 'remote', 'get-url', 'origin'], cwd=orig_dir, encoding='utf-8').strip()
    git_url = git_url.replace('git@github.com:', 'https://github.com/')

    j: InsightFile = {
        **out,
        'source': {
            'project_name': os.path.basename(git_repo_dir),
            'file_name': source_file_name,
            'git_rev': git_rev,
            'git_url': git_url,
        },
    }
    json.dump(j, open(f'dataset/{fn}.json', 'w'))

def main():
    os.makedirs('dataset', exist_ok=True)

    dirs = sys.argv[1:]

    pool = multiprocessing.Pool()

    fns = [ fn for dir in dirs for fn in glob.iglob(f'{dir}/**/*.fst*.checked', recursive=True, include_hidden=True) if not os.path.isdir(fn) and os.path.getsize(fn) > 0 ]
    checked_deps = list(tqdm.tqdm(pool.imap_unordered(run_print_checked_deps, fns), total=len(fns), desc='Parsing checked files'))
    dig2checked: dict[str, list[tuple[str, Any]]] = {}
    for fn, j, dig in checked_deps:
        if dig not in dig2checked: dig2checked[dig] = []
        dig2checked[dig].append((fn, j))
    expected_source_fns = set(os.path.splitext(os.path.basename(fn))[0] for fn, _, _ in checked_deps)

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
        if dig not in dig2checked: return False
        error = None
        for checked_fn, dep_info in dig2checked[dig]:
            basename = os.path.splitext(os.path.basename(checked_fn))[0]
            if 'tls/cache/Karamel' in checked_fn:
                error = f'Skipping {checked_fn} because module name clashes with the Model variant'
                continue
            if basename.startswith('Test.fst'):
                error = f'Skipping {checked_fn} because name causes lots of shadowing'
                continue
            if ('FStar.' + basename) in expected_source_fns:
                error = f'Skipping {checked_fn} because module name clashes with FStar.{basename} with the default open'
                continue
            if basename in basename2files:
                error = f'Skipping duplicate module {checked_fn} in favor of {basename2files[basename]}'
                continue
            src_fn = None
            for src_fn_cand in digest2src.get(dep_info['source_digest'], []):
                if os.path.basename(src_fn_cand) == basename:
                    src_fn = src_fn_cand
                    break
            if src_fn is None:
                error = f'Skipping {checked_fn} because of unavailable source file {basename}'
                continue
            for dep in dep_info['deps_digest']:
                if dep['module_name'] == 'source':
                    assert dep['digest'] == dep_info['source_digest'] # duplicate info
                else:
                    if not resolve_checked(dep['digest']):
                        error = f'Skipping {checked_fn} because of unavailable dependency {dep["module_name"]}'
                        continue
            if basename in basename2files:
                error = f'Skipping duplicate module {checked_fn} in favor of {basename2files[basename]}'
                continue
            basename2files[basename] = (checked_fn, src_fn)
            return True
        print(error)
        return False

    for dig in dig2checked.keys(): resolve_checked(dig)

    for checked_fn, src_fn in tqdm.tqdm(basename2files.values(), desc = 'Copying files'):
        shutil.copy(src_fn, 'dataset/')
        shutil.copy(checked_fn, 'dataset/')

    list(tqdm.tqdm(pool.imap_unordered(run_extract, [ (bn, fn[1]) for bn, fn in basename2files.items() ]),
        total=len(basename2files), desc='Extracting insights'))

if __name__ == '__main__':
    main()
