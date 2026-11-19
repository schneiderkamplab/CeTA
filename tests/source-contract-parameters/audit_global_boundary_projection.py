"""Check exact boundary projections in immutable certified residual artifacts."""
from pathlib import Path
import copy
import hashlib
import json
import xml.etree.ElementTree as ET
root = Path(__file__).resolve().parents[3]
base = root / 'ferrum-prolog-release/target'
cases = [('original', base/'checkpoint-full-residual-20261118/child.xml',
          'b68ee3bb365e3f61bc984bda7edc52a117463923b23d0251c5d09d9a40434c21'),
         ('renamed', base/'checkpoint-full-residual-renamed-20261118/result/child.xml',
          '187c1f6f45c1a3618bcba629edda6fd7324b7d9f7c0a6105aa317c3c2ffe62aa')]
def atom(e):
    if e is None or e.tag != 'funapp':
        return None
    children = list(e)
    if children[0].tag != 'name' or any(x.tag != 'var' for x in children[1:]):
        return None
    return children[0].text, [x.text for x in children[1:]]
def projection(cl):
    h = atom(cl.find('head/funapp'))
    body = cl.findall('body/funapp')
    if h is None or len(body) != 1:
        return False
    b = atom(body[0])
    return (b is not None and len(h[1]) == 6 and len(set(h[1])) == 6
            and b[1] == [h[1][i] for i in (0, 1, 3, 4)])
records = []
for variant, path, expected_hash in cases:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == expected_hash
    tree = ET.parse(path).getroot()
    clauses = list(tree.find('program'))
    selected = [(i, cl) for i, cl in enumerate(clauses) if projection(cl)]
    assert len(selected) == 2
    for i, cl in selected:
        h, b = atom(cl.find('head/funapp')), atom(cl.find('body/funapp'))
        matches = [j for j,t in enumerate(tree.find('triples'))
                   if atom(t.find('head/funapp')) == h and atom(t.find('call/funapp')) == b
                   and len(t.find('prefix')) == 0]
        assert len(matches) == 1
        damaged = copy.deepcopy(cl)
        damaged.find('body/funapp').findall('var')[2].text = h[1][5]
        assert not projection(damaged)
        collision = copy.deepcopy(cl)
        collision.find("head/funapp").findall("var")[3].text = h[1][0]
        assert not projection(collision)
        missing = copy.deepcopy(cl)
        missing.find('body').clear()
        assert not projection(missing)
        records.append(dict(variant=variant, clause_index=i, triple_index=matches[0],
                            source=h[0], target=b[0], projection=[0,1,3,4],
                            runtime_variables=h[1][:3], structural_variables=h[1][3:],
                            structural_variables_disjoint=True, colliding_structural_variable_rejected=True,
                            wrong_structural_coordinate_rejected=True, missing_call_rejected=True,
                            artifact=str(path), sha256=digest))
print(json.dumps(dict(scope='Exact clauses and empty-prefix triples; no source simulation or fresh certification',
                      records=records), indent=2))
