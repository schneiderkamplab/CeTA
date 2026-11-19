"""Audit the exact zero-interface copy return paths; no production proof search."""
from pathlib import Path
import copy
import hashlib
import json
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[3]
TARGET = ROOT / 'ferrum-prolog-release/target'
transform_path = TARGET / 'checkpoint-full-residual-renamed-20261118/transformation.json'
renaming = json.loads(transform_path.read_text())['symbols']

def atom(e):
    assert e is not None and e.tag == 'funapp' and e[0].tag == 'name'
    assert all(c.tag == 'var' for c in list(e)[1:])
    return e[0].text, tuple(c.text for c in list(e)[1:])

def check(root, symbols, arity):
    selected=[]
    for j,(src,dst) in enumerate(zip(symbols,symbols[1:])):
        cs=[(i,c) for i,c in enumerate(root.find('program')) if c.findtext('head/funapp/name')==src
            and len(c.find('body'))==1 and atom(c.find('body')[0])[0]==dst]
        assert len(cs)==1
        i,c=cs[0]; h,b=atom(c.find('head/funapp')),atom(c.find('body')[0])
        assert len(h[1])==(arity if j==0 else 0) and len(set(h[1]))==len(h[1])
        assert b[1]==()
        triples=[t for t in root.find('triples') if t.findtext('head/funapp/name')==src and atom(t.find('head/funapp'))==h
                 and atom(t.find('call/funapp'))==b and len(t.find('prefix'))==0]
        assert len(triples)==1
        selected.append(i)
    return selected

records=[]
for variant,artifact in [('original',TARGET/'checkpoint-full-residual-20261118/child.xml'),
                         ('renamed',TARGET/'checkpoint-full-residual-renamed-20261118/result/child.xml')]:
    root=ET.parse(artifact).getroot()
    def encoded(name,arity):
        if variant=='renamed': name=renaming[name]
        return f'lp_in_{name.encode().hex()}_{arity}'
    source=TARGET/'source-contract-development'/variant/'states-28.xml'
    states=ET.parse(source).getroot()
    assert states.findtext('returnArity')=='0'
    assert len(states.find('returnStates'))==3
    for row in [0,1]:
        frame=states.find('returnStates')[row]
        assert len(frame)==1 and len(frame[0].find('outputs'))==0
    assert len(states.find('returnStates')[2])==0
    for name,arity in [('seg_region_0_25',6),('seg_region_35_5',2)]:
        symbols=[encoded(name,arity)]+[encoded(n,0) for n in ['seg_region_28_0','seg_region_28_1','seg_region_28_returned']]
        selected=check(root,symbols,arity)
        negatives=[]
        for mutation in ['missing_boundary','missing_cut','missing_return','invented_output','wrong_return_target']:
            bad=copy.deepcopy(root)
            if mutation.startswith('missing_'):
                index=selected[['missing_boundary','missing_cut','missing_return'].index(mutation)]
                bad.find('program').remove(bad.find('program')[index])
            elif mutation=='invented_output': ET.SubElement(bad.find('program')[selected[0]].find('body')[0],'var').text='forged'
            else: bad.find('program')[selected[2]].find('body/funapp/name').text=symbols[1]
            try: check(bad,symbols,arity)
            except (AssertionError,IndexError,AttributeError): negatives.append(mutation)
            else: raise AssertionError(mutation)
        records.append(dict(variant=variant,source=name,arity=arity,clauses=selected,symbols=symbols,rejected=negatives,
         artifacts={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [artifact,source,transform_path]}))
print(json.dumps(dict(scope='Exact zero-interface residual paths and empty module payload; caller contract remains unproved',records=records),indent=2))
