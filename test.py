#!/usr/bin/env python3
import json
import fstar_harness
import sys

tests = [
    ('FStar.OrdSet.eq_lemma', '()', False), # SMT pattern for eq_lemma
    ('FStar.OrdSet.eq_lemma', 'FStar.OrdSet.eq_lemma s1 s2', False), # referencing lemma itself
    ('FStar.Seq.Base.init_aux', "init_aux'", True), # private definition
    ('FStar.Seq.Base.append_assoc', '()', False),
    ('FStar.Seq.Base.append_assoc', 'assume false; ()', False), # reject assumes
    ('FStar.Sequence.Base.length_of_empty_is_zero_lemma', '()', True), # support private names
]

to_check: list[fstar_harness.PoolTask] = []
for lid, prf, should_check in tests:
    mod_name, _ = lid.rsplit('.', 1)
    f: fstar_harness.InsightFile = json.load(open(f'dataset/{mod_name}.fst.json'))
    defn, = (defn for defn in f['defs'] if defn['name'] == lid and defn['definition'] != '<DECLARETYP>')
    prompt = defn['prompt']
    defn['source_definition'] = prompt + prf
    to_check.append(defn)

with fstar_harness.FStarPool('dataset') as p:
    harness_results = p.process_instances(to_check, progressbar=True)

results = []
for output, (lid, prf, should_check) in zip(harness_results, tests):
    passed = output['result']
    results.append(passed)
    if passed == should_check:
        print(f'    ok {lid} = {prf}')
    else:
        print(output['detail'])
        kind = 'FALSE ' + ('POSITIVE' if passed else 'NEGATIVE')
        print(f'NOT OK {lid} = {prf} ({kind})')

false_positives = len([() for actual, (_, _, expected) in zip(results, tests) if actual and not expected])
false_negatives = len([() for actual, (_, _, expected) in zip(results, tests) if not actual and expected])
if false_positives > 0 or false_negatives > 0:
    print(f'{false_positives} false positives, {false_negatives} false negatives')
    sys.exit(1)
