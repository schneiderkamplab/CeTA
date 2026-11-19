"""Audit equality success and duplicated return coordinates in pinned residuals."""
from pathlib import Path
import contextlib,io,json,runpy
import xml.etree.ElementTree as ET
with contextlib.redirect_stdout(io.StringIO()):
    base=runpy.run_path(str(Path(__file__).with_name('audit_global_boundary_projection.py')))
atom=base['atom']
def success(cl,symbol):
    h=atom(cl.find('head/funapp'));bs=cl.findall('body/funapp')
    if h is None or h[0]!=symbol or len(h[1])!=4 or len(set(h[1]))!=4 or len(bs)!=1:return False
    b=atom(bs[0])
    return b is not None and b[1]==[h[1][1],h[1][3]]
def returned(cl,symbol):
    h=atom(cl.find('head/funapp'));bs=cl.findall('body/funapp')
    if h is None or h[0]!=symbol or len(h[1])!=2 or len(set(h[1]))!=2 or len(bs)!=1:return False
    b=atom(bs[0])
    return b is not None and b[1]==[h[1][0],h[1][0],h[1][1],h[1][1]]
records=[]
for variant,path,digest in base['cases']:
    tree=ET.parse(path).getroot();clauses=list(tree.find('program'))
    targets={atom(c.find('body/funapp'))[0] for c in clauses if base['projection'](c)}
    assert len(targets)==1
    target=next(iter(targets))
    candidates=[(i,c) for i,c in enumerate(clauses) if success(c,target)]
    assert len(candidates)==1
    i,c=candidates[0];success_symbol=atom(c.find('body/funapp'))[0]
    returns=[(j,r) for j,r in enumerate(clauses) if returned(r,success_symbol)]
    assert len(returns)==1
    j,r=returns[0]
    triples=[]
    for clause in [c,r]:
        h,b=atom(clause.find('head/funapp')),atom(clause.find('body/funapp'))
        matches=[k for k,t in enumerate(tree.find('triples')) if atom(t.find('head/funapp'))==h
                 and atom(t.find('call/funapp'))==b and len(t.find('prefix'))==0]
        assert len(matches)==1;triples+=matches
    wrong=ET.fromstring(ET.tostring(c));wrong.find('body/funapp').findall('var')[1].text=atom(c.find('head/funapp'))[1][2]
    assert not success(wrong,target)
    wrong=ET.fromstring(ET.tostring(r));wrong.find('body/funapp').findall('var')[3].text=atom(r.find('head/funapp'))[1][0]
    assert not returned(wrong,success_symbol)
    missing=ET.fromstring(ET.tostring(r));missing.find('body').clear()
    assert not returned(missing,success_symbol)
    records.append(dict(variant=variant,success_clause=i,return_clause=j,triples=triples,
                        scalar_observation_reused=True,return_projection=[0,0,1,1],negative_controls=3,
                        artifact=str(path),sha256=digest))
print(json.dumps(dict(scope='Exact clauses/triples only; actual MGU and observer premises require kernel proofs',records=records),indent=2))
