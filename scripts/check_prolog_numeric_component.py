#!/usr/bin/env python3
"""Check native numeric-component envelopes and semantic mutations.

This is a diagnostic residual gate; it never issues a Prolog source verdict.
"""
import argparse
import copy
import json
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('certificates', nargs='+', type=Path)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
results = []

def check(label, root, expected):
    path = a.output / (label + '.xml')
    ET.ElementTree(root).write(path, encoding='unicode')
    for attempt in range(2):
        r = subprocess.run([str(a.checker.resolve()), str(path.resolve())],
                           capture_output=True, text=True, timeout=60)
        (a.output / f'{label}-{attempt}.log').write_text(r.stdout + r.stderr)
        accepted = r.returncode == 0 and 'VALID NUMERIC COMPONENT; NO SOURCE VERDICT' in r.stdout
        results.append(dict(label=label, attempt=attempt, accepted=accepted, expected=expected))
        if accepted != expected:
            (a.output / 'results.json').write_text(json.dumps(results, indent=2))
            raise SystemExit(f'{label}: expected {expected}, got {accepted}')

for i, source in enumerate(a.certificates):
    root = ET.parse(source).getroot()
    check(f'{i}-valid', root, True)
    mutations = {
        'missing-row': ('rows', None),
        'lost-type-facts': ('rows/row/facts', None),
        'missing-transition': ('lts/transition', None),
        'missing-entry': ('lts/initial', None),
        'wrong-input': ('rows/row/prologNumericPath/inputs/endpoint/coordinate', 'bad'),
        'wrong-output': ('rows/row/prologNumericPath/outputs/endpoint/coordinate', 'bad'),
        'wrong-location': ('locations/entry/locationId', 'bad'),
        'wrong-coordinate': ('coordinates/entry/names/coordinate', 'bad'),
        'wrong-transition-formula': ('lts/transition/formula', None),
        'missing-proof': ('ltsTerminationProof', None),
        'lost-observation': ('rows/row/prologNumericPath/observations', None),
        'conflicting-auxiliary': ('rows/row/prologNumericPath/bindings/binding/post/variableId', 'v0'),
    }
    for name, (xpath, value) in mutations.items():
        mutated = copy.deepcopy(root)
        node = mutated.find(xpath)
        if node is None:
            raise SystemExit(f'mutation {name} does not apply to {source}')
        if value is None:
            node.clear()
        else:
            node.text = value
        check(f'{i}-{name}', mutated, False)
(a.output / 'results.json').write_text(json.dumps(results, indent=2))
print(f'{len(results)} component checks passed; no source verdicts')
