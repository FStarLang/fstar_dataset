# --------------------------------------------------------------------------------------------
# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT License. See LICENSE in the project root for license information.
# --------------------------------------------------------------------------------------------

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
import fstar_harness
from typing import Any, get_type_hints, Union, Optional
from functools import cache
from dataclasses import dataclass

FStarName = str
PyType = Any

@dataclass
class PTRes:
    fstar_type: str
    to_json: str

used: set[str] = set()
def fstarify(n: str):
    n = n.lower().replace('-', '_')
    if n in ('open', 'abbrev', 'effect', 'type'): n += '_'
    global used
    if n in used:
        i = 0
        while True:
            i += 1
            if n + str(i) not in used:
                n += str(i)
                break
    used.add(n)
    return n

@cache
def process_type(ty: PyType) -> PTRes:
    if ty == str: return PTRes(fstar_type = 'string', to_json = 'JsonStr')
    if ty == bool: return PTRes(fstar_type = 'bool', to_json = 'JsonBool')
    if ty == int: return PTRes(fstar_type = 'int', to_json = 'JsonInt')
    if ty == Any: return PTRes(fstar_type='json', to_json='(fun x -> x)')
    if ty == type(None): return PTRes(fstar_type='unit', to_json='(fun _ -> JsonNull)')
    if hasattr(ty, '__origin__'):
        if ty.__origin__ == list:
            arg = process_type(ty.__args__[0])
            return PTRes(fstar_type=f'(list {arg.fstar_type})', to_json=f'(fun xs -> JsonList (List.Tot.map ({arg.to_json}) xs))')
        if ty.__origin__ == Union and len(ty.__args__) == 2 and ty.__args__[1] == type(None):
            arg = process_type(ty.__args__[0])
            return PTRes(fstar_type=f'(option {arg.fstar_type})', to_json=f'(fun x -> match x with | Some x -> {arg.to_json} x | None -> JsonNull)')
        if ty.__origin__ == Union:
            arg1, arg2 = map(process_type, ty.__args__) # TODO: more
            return PTRes(fstar_type=f'(either {arg1.fstar_type} {arg2.fstar_type})',
                to_json=f'(fun x -> match x with | Inl x -> {arg1.to_json} x | Inr x -> {arg2.to_json} x)')
        if ty.__origin__ == tuple:
            args = list(map(process_type, ty.__args__))
            fst_ty = '(' + ' * '.join(a.fstar_type for a in args) + ')'
            to_json = '(fun (' + ', '.join(f'x{i}' for i in range(len(args))) + ') -> JsonList [' + '; '.join(f'{a.to_json} x{i}' for i, a in enumerate(args)) + '])'
            return PTRes(fstar_type=fst_ty, to_json=to_json)

    fst_name = fstarify(ty.__name__)
    field_tys = get_type_hints(ty)
    field_map = { n: (fstarify(n), process_type(t)) for n, t in field_tys.items() }

    print(f'type {fst_name} = {{')
    for n, (fn, t) in field_map.items():
        print(f'  {fn}: {t.fstar_type};')
    print('}')

    to_json = f'json_of_{fst_name}'
    print(f'let {to_json} (x : {fst_name}) : Tot json =')
    print('  JsonAssoc ([')
    for n, (fn, t) in field_map.items():
        print(f'    "{n}", {t.to_json} x.{fn};')
    print('  ])')
    print()

    return PTRes(fstar_type=fst_name, to_json=to_json)

print('''
module JsonHelper
open FStar.Json
''')
# process_type(fstar_harness.Source)
# process_type(fstar_harness.Dependency)
# process_type(fstar_harness.OpenOrAbbrev)
process_type(fstar_harness.InsightFileFirstPass)
