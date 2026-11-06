#!/usr/bin/env python3
"""Exercise native stable-bound certificates or adapt retained integer fixtures.

This adapts test evidence, not development guidance or native search. Acceptance
is not a new benchmark gain. A real bound-coordinate cohort remains required.
"""
import argparse
import copy
import json
import subprocess
from pathlib import Path
import xml.etree.ElementTree as ET

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--baseline', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
r = ET.parse(a.baseline).getroot()
native = r.tag == 'prologEstablishedStableSEGGuardedProof'
if not native:
    assert r.tag == 'prologEstablishedFiniteSEGGuardedProof'
    r.tag = 'prologEstablishedStableSEGGuardedProof'
    c = r.find('prologNumericComponent')
    assert c is not None
    c.tag = 'prologStableNumericComponent'
    modes = ET.Element('coordinateModes')
    for entry in c.find('coordinates'):
        out = ET.SubElement(modes, 'entry')
        out.append(copy.deepcopy(entry.find('predicate')))
        ms = ET.SubElement(out, 'modes')
        for _ in entry.find('names'):
            ET.SubElement(ms, 'integerCoordinate')
    c.insert(list(c).index(c.find('locations')), modes)
    replacements = {}
    for row in c.find('rows'):
        path = row.find('prologNumericPath')
        old_formula = ET.tostring(path.find('formula'))
        bindings = {b[0].text: copy.deepcopy(b[1]) for b in path.find('bindings')}
        equalities = []
        for endpoint in path.find('inputs'):
            equality = ET.Element('eq')
            ET.SubElement(equality, 'variableId').text = endpoint[0].text
            expression = endpoint[2]
            if expression.tag == 'var':
                equality.append(copy.deepcopy(bindings[expression.text]))
            else:
                assert expression.tag == 'integer'
                ET.SubElement(equality, 'constant').text = expression.text
            equalities.append(equality)
        conjunction = path.find('formula/conjunction')
        assert conjunction is not None
        for index, equality in enumerate(equalities):
            conjunction.insert(index, equality)
        replacements[old_formula] = copy.deepcopy(path.find('formula'))
        for direction in ['inputs', 'outputs']:
            for endpoint in path.find(direction):
                expression = endpoint[2]
                endpoint.remove(expression)
                ET.SubElement(endpoint, 'integerEndpoint').append(expression)
        for test in path.find('tests'):
            test.tag = 'integerCondition'
        for binding in path.find('bindings'):
            assert binding[0].tag == 'var'
            binding[0].tag = 'integerKey'
        row.remove(path)
        ET.SubElement(row, 'ground')
        for field in ['inputs', 'outputs', 'tests', 'bindings', 'formula']:
            row.append(path.find(field))
    for transition in c.findall('lts/transition'):
        old = transition.find('formula')
        replacement = replacements[ET.tostring(old)]
        transition.remove(old)
        transition.append(copy.deepcopy(replacement))

cases = [('positive-1', r, True), ('positive-2', r, True)]
for label, xpath in [
    ('missing-component', 'components/*'),
    ('missing-context', 'contexts/*'),
    ('missing-root', 'roots/*'),
    ('missing-child-triple', 'prologStableNumericComponent/triples/*'),
    ('missing-child', 'prologStableNumericComponent/ltsTerminationProof'),
    ('missing-row', 'prologStableNumericComponent/rows/row'),
    ('missing-type-fact', 'prologStableNumericComponent/rows/row/facts/*'),
    ('missing-descent', 'guardedDescents/*'),
    ('missing-projection', 'argumentProjection/entry'),
]:
    changed = copy.deepcopy(r)
    target = changed.find(xpath)
    assert target is not None, label
    parent = next(n for n in changed.iter() if target in list(n))
    parent.remove(target)
    cases.append((label, changed, False))
if native:
    for label, xpath in [
        ('missing-bound-ground', 'prologStableNumericComponent/rows/row/ground/var'),
        ('missing-upper-condition', 'prologStableNumericComponent/rows/row/tests/upperCondition'),
        ('missing-bound-binding', 'prologStableNumericComponent/rows/row/bindings/binding/boundKey'),
    ]:
        changed = copy.deepcopy(r)
        target = changed.find(xpath)
        assert target is not None, label
        parent = next(n for n in changed.iter() if target in list(n))
        parent.remove(target)
        cases.append((label, changed, False))
changed = copy.deepcopy(r)
role = changed.find('prologStableNumericComponent/coordinateModes/entry/modes/*')
role.tag = 'integerCoordinate' if role.tag == 'upperBoundCoordinate' else 'upperBoundCoordinate'
cases.append(('conflicting-coordinate-role', changed, False))
changed = copy.deepcopy(r)
changed.find('profile').text = 'unsupported-profile'
cases.append(('wrong-profile', changed, False))
results = []
for label, root, expected in cases:
    path = a.output / (label + '.xml')
    ET.ElementTree(root).write(path, encoding='unicode')
    run = subprocess.run([str(a.checker.resolve()), '--category', 'prolog', str(path.resolve())],
                         text=True, capture_output=True, timeout=60)
    (a.output / (label + '.log')).write_text(run.stdout + run.stderr)
    accepted = run.returncode == 0 and 'CERTIFIED SOURCE-BOUND PROLOG' in run.stdout
    results.append(dict(case=label, expected=expected, accepted=accepted, exit_code=run.returncode))
(a.output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
assert all(x['accepted'] == x['expected'] for x in results), results
print(f'{len(results)} stable source-constructor checks passed')
