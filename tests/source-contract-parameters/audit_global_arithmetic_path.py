"""Check the exact incoming arithmetic clauses paired with boundary projections."""
from pathlib import Path
import contextlib
import io
import json
import runpy
import xml.etree.ElementTree as ET
with contextlib.redirect_stdout(io.StringIO()):
    base = runpy.run_path(str(Path(__file__).with_name('audit_global_boundary_projection.py')))
atom, projection = base['atom'], base['projection']
def incoming(cl, target):
    h = atom(cl.find('head/funapp'))
    calls = cl.findall('body/funapp')
    if h is None or len(h[1]) != 4 or len(set(h[1])) != 4 or len(calls) != 1:
        return False
    b = atom(calls[0])
    if b is None or b[0] != target or len(b[1]) != 6:
        return False
    x,p,sx,sp = h[1]
    vals = b[1]
    return (vals[0] == x and vals[2] == p and vals[3] == sx and vals[5] == sp
            and vals[1] not in h[1] and vals[4] not in h[1] and vals[1] != vals[4])
records = []
for variant,path,digest in base['cases']:
    tree = ET.parse(path).getroot()
    clauses = list(tree.find('program'))
    boundaries = [(i,c) for i,c in enumerate(clauses) if projection(c)]
    for j,boundary in boundaries:
        target = atom(boundary.find('head/funapp'))[0]
        matches = [(i,c) for i,c in enumerate(clauses) if incoming(c,target)]
        assert len(matches) == 1
        i,cl = matches[0]
        h,b = atom(cl.find('head/funapp')),atom(cl.find('body/funapp'))
        triples = [k for k,t in enumerate(tree.find('triples'))
                   if atom(t.find('head/funapp')) == h and atom(t.find('call/funapp')) == b
                   and len(t.find('prefix')) == 0]
        assert len(triples) == 1
        for slot,wrong in [(3,h[1][3]),(1,h[1][0]),(4,h[1][2])]:
            damaged = ET.fromstring(ET.tostring(cl))
            damaged.find('body/funapp').findall('var')[slot].text = wrong
            assert not incoming(damaged,target)
        records.append(dict(variant=variant,arithmetic_clause=i,arithmetic_triple=triples[0],
                            boundary_clause=j,output_observation_preserved=True,
                            parameter_observation_preserved=True,fresh_scalar_pair=True,
                            negative_controls=3,artifact=str(path),sha256=digest))
print(json.dumps(dict(scope='Exact retained clause and empty-prefix triple audit; no complete source simulation',
                      records=records),indent=2))
