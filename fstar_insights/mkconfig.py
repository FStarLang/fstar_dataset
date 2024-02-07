#!/usr/bin/env python3
import subprocess, json

# Make behaves super weirdly when called from inside make,
# and prints warning messages to stdout!
import os
del os.environ['MAKE_TERMERR']
del os.environ['MAKELEVEL']

opts = subprocess.run(['make', 'QueryCheckedFile.fst-in'], capture_output=True, check=True).stdout.decode('UTF-8').strip().split(' ')
opts.reverse()

new_opts = []
includes = []
while len(opts) > 0:
    opt = opts.pop()
    if opt == '--include':
        includes.append(opts.pop())
    else:
        new_opts.append(opt)

print(json.dumps({
    'fstar_exe': 'fstar.exe',
    'options': new_opts,
    'include_dirs': includes,
}))