#!/usr/bin/env python3
import json
import fstar_harness

tests = [
    ('FStar.OrdSet.eq_lemma', '()', False),
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