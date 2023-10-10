#!/usr/bin/env python3
import json
import fstar_harness
import sys

tests = [
    ('FStar.OrdSet.eq_lemma', '()', False),
    ('FStar.OrdSet.eq_lemma', 'FStar.OrdSet.eq_lemma s1 s2', False),
    # ('FStar.Seq.Base.init_aux', "init_aux'", True),
    ('FStar.Sequence.Base.length_of_empty_is_zero_lemma', '()', True),
]

results = []
for lid, prf, should_check in tests:
    mod_name, _ = lid.rsplit('.', 1)
    f: fstar_harness.InsightFile = json.load(open(f'dataset/{mod_name}.fst.json'))
    defn, = (defn for defn in f['defs'] if defn['name'] == lid and defn['definition'] != '<DECLARETYP>')
    prompt = defn['prompt']
    prompt = prompt[prompt.find('\nlet')+1:] # TODO!?!
    defn['source_definition'] = f'{prompt} = {prf}'
    f['defs'] = [defn]
    outputs = fstar_harness.send_queries_to_fstar(f, 'dataset')
    passed = outputs[0]['result']
    results.append(passed)
    if passed == should_check:
        print(f'    ok {lid} = {prf}')
    else:
        kind = 'FALSE ' + ('POSITIVE' if passed else 'NEGATIVE')
        print(f'NOT OK {lid} = {prf} ({kind})')

false_positives = len([() for actual, (_, _, expected) in zip(results, tests) if actual and not expected])
false_negatives = len([() for actual, (_, _, expected) in zip(results, tests) if not actual and expected])
if false_positives > 0 or false_negatives > 0:
    print(f'{false_positives} false positives, {false_negatives} false negatives')
    sys.exit(1)
