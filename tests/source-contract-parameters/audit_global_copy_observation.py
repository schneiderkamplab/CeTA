"""Match both copy-success coordinate patterns in the pinned residuals."""
from pathlib import Path
import contextlib
import copy
import io
import json
import runpy
import xml.etree.ElementTree as ET

with contextlib.redirect_stdout(io.StringIO()):
    base = runpy.run_path(str(Path(__file__).with_name('audit_global_boundary_projection.py')))
atom = base['atom']


def pattern(clause):
    head = atom(clause.find('head/funapp'))
    body = clause.findall('body/funapp')
    if head is None or len(body) != 1:
        return None
    target = atom(body[0])
    if target is None:
        return None
    h, b = head[1], target[1]
    if len(set(h)) != len(h):
        return None
    if len(h) == 6 and len(b) == 2 and b[0] not in h and b[1] == h[4]:
        return 'six_to_two'
    if (len(h) == 10 and len(b) == 6 and b[:2] == [h[1], h[3]]
            and b[3:5] == [h[6], h[8]] and b[2] not in h and b[5] not in h
            and b[2] != b[5]):
        return 'ten_to_six'
    return None


records = []
for variant, path, digest in base['cases']:
    tree = ET.parse(path).getroot()
    selected = [(i, c, pattern(c)) for i, c in enumerate(tree.find('program')) if pattern(c)]
    assert sorted(p for _, _, p in selected) == ['six_to_two', 'ten_to_six']
    for i, clause, kind in selected:
        h, b = atom(clause.find('head/funapp')), atom(clause.find('body/funapp'))
        matches = [j for j, t in enumerate(tree.find('triples'))
                   if atom(t.find('head/funapp')) == h and atom(t.find('call/funapp')) == b
                   and len(t.find('prefix')) == 0]
        assert len(matches) == 1
        wrong_shadow = copy.deepcopy(clause)
        wrong_shadow.find('body/funapp').findall('var')[1 if kind == 'six_to_two' else 3].text = h[1][len(h[1])//2+2]
        assert pattern(wrong_shadow) is None
        wrong_parameter = copy.deepcopy(clause)
        wrong_parameter.find('body/funapp').findall('var')[0].text = h[1][0]
        assert pattern(wrong_parameter) is None
        collision = copy.deepcopy(clause)
        collision.find('head/funapp').findall('var')[-1].text = h[1][0]
        assert pattern(collision) is None
        missing = copy.deepcopy(clause)
        missing.find('body').clear()
        assert pattern(missing) is None
        records.append(dict(variant=variant, kind=kind, clause=i, triple=matches[0],
                            source=h[0], target=b[0], source_coordinates=h[1], target_coordinates=b[1],
                            negative_controls=4, artifact=str(path), sha256=digest))
print(json.dumps(dict(scope='Exact copy-success clauses and triples; source MGU, mode and observer premises remain semantic proof obligations', records=records), indent=2))
