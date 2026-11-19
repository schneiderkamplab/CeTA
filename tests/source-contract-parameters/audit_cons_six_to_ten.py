"""Exact retained six-to-ten clause, variable freshness and triple audit."""
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import runpy
import xml.etree.ElementTree as ET
with contextlib.redirect_stdout(io.StringIO()):
    base=runpy.run_path(str(Path(__file__).with_name('audit_cons_observation_split.py')))
ROOT=base['ROOT'];name=base['name'];args=base['args'];var=base['var'];pattern=base['check']

def key(e):return e.tag,(e.text or '').strip(),tuple(key(c) for c in e)
def verify(root,i,renamed):
    c=root.find('program')[i];pattern(c,renamed,6)
    h=c.find('head/funapp');b=c.find('body')[0];hs=args(h);bs=args(b)
    headvars=[e.text for e in h.iter('var')]
    assert len(headvars)==7
    formals=headvars+[var(t) for t in bs[:5]]+[var(bs[7])]
    assert len(formals)==len(set(formals))==13
    triples=[t for t in root.find('triples') if key(t.find('head/funapp'))==key(h)
             and key(t.find('call/funapp'))==key(b) and len(t.find('prefix'))==0]
    assert len(triples)==1

records=[]
for variant,path in [('original',ROOT/'checkpoint-full-residual-20261118/child.xml'),('renamed',ROOT/'checkpoint-full-residual-renamed-20261118/result/child.xml')]:
    renamed=variant=='renamed';root=ET.parse(path).getroot()
    found=[i for i,c in enumerate(root.find('program')) if name(c.find('head/funapp'),renamed)==('seg_region_35_3',6)
           and args(c.find('head/funapp'))[3].tag=='funapp']
    assert len(found)==1;i=found[0];verify(root,i,renamed);rejected=[]
    for change in ['head_collision','body_data_collision','wrong_parameter_shadow','stale_fresh_shadow','missing_call','missing_triple']:
        bad=copy.deepcopy(root);c=bad.find('program')[i];h=c.find('head/funapp');b=c.find('body')[0];hs=args(h);bs=args(b)
        if change=='head_collision':hs[1].text=hs[0].text
        elif change=='body_data_collision':bs[0].text=hs[0].text
        elif change=='wrong_parameter_shadow':bs[6].text=bs[9].text
        elif change=='stale_fresh_shadow':bs[7].text=bs[6].text
        elif change=='missing_call':c.find('body').clear()
        else:
            triple=next(t for t in bad.find('triples') if key(t.find('head/funapp'))==key(h) and key(t.find('call/funapp'))==key(b))
            bad.find('triples').remove(triple)
        try:verify(bad,i,renamed)
        except (AssertionError,AttributeError,IndexError,KeyError):rejected.append(change)
        else:raise AssertionError(change)
    records.append(dict(variant=variant,clause=i,distinct_formals=13,rejected=rejected,artifact=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
print(json.dumps(dict(scope='Full six-to-ten residual clause and empty-prefix triple; source node contract remains open',records=records),indent=2))
