"""Audit the five source coordinates used by the cons observation assembly."""
import copy
import hashlib
import json
from pathlib import Path
import xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[3]/'ferrum-prolog-release/target/source-contract-development'

def variable(e):assert e.tag=='var';return e.text

def verify(states,actions,subject,row):
    resolve=actions[row].find('resolve'); clause=subject.find('program')[int(resolve.findtext('index'))]
    h=clause.find('head/funapp');cons=h[1];assert cons.findtext('user')=='2:prolog_data_2e'
    source=[variable(cons[1]),variable(h[2]),None,variable(cons[2]),variable(h[3])]
    assert len(set(v for v in source if v is not None))==4
    calls=clause.findall('body/atom/funapp');assert len(calls)==2
    source[2]=variable(calls[0][3]);assert source[2] not in {v.text for v in h.iter('var')}
    link=resolve.findall('link')[0];target=int(link.findtext('target'));l=int(resolve.findtext('clausePrefix'))
    goals=states.find('returnStates')[target].findall('frame/goals/atom/funapp');assert len(goals)==2
    slots=[variable(goals[0][1]),variable(goals[0][2]),variable(goals[0][3]),variable(goals[1][1]),variable(goals[1][3])]
    assert variable(goals[1][2])==slots[2] and len(set(slots))==5
    bindings={variable(b[0]):b[1] for b in link.find('bindings')};assert len(bindings)==len(link.find('bindings'))
    for slot,source_var in zip(slots,source):assert variable(bindings[slot])=='$'*l+source_var
    return target,slots

records=[]
for variant in ['original','renamed']:
 for region,row in [('0',23),('35',3)]:
    paths=[ROOT/variant/f'{kind}-{region}.xml' for kind in ['states','actions','subject']]
    roots=[ET.parse(p).getroot() for p in paths];target,slots=verify(*roots,row)
    rejected=[]
    for idx in range(5):
     for kind in ['missing','wrong']:
        states,actions,subject=copy.deepcopy(roots);bindings=actions[row].find('resolve/link/bindings')
        b=next(b for b in bindings if b[0].text==slots[idx])
        if kind=='missing':bindings.remove(b)
        else:b[1].text='stale_coordinate'
        try:verify(states,actions,subject,row)
        except (AssertionError,KeyError,IndexError,AttributeError):rejected.append(f'{kind}_{idx}')
        else:raise AssertionError((kind,idx))
    records.append(dict(variant=variant,region=region,row=row,target=target,slots=slots,rejected=rejected,
                       artifacts={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}))
print(json.dumps(dict(scope='Five cons successor coordinate maps only; full row and residual assembly remain open',records=records),indent=2))
