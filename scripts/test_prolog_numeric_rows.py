#!/usr/bin/env python3
"""Check native numeric guard receipts and corruptions; never report root proofs."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--receipts', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
results = []
def check(name, tree, expected):
    path = a.output / (name + '.xml')
    ET.ElementTree(tree).write(path, encoding='unicode')
    run = subprocess.run([str(a.checker.resolve()), str(path.resolve())], text=True, capture_output=True, timeout=30)
    results.append(dict(name=name, expected=expected, accepted=run.returncode == 0,
                        returncode=run.returncode, stdout=run.stdout, stderr=run.stderr))
paths = sorted(a.receipts.glob('*-numeric-guard-*.xml'))
if not paths:
    raise SystemExit('no native numeric guard receipts')
for i, path in enumerate(paths):
    root = ET.parse(path).getroot()
    check(f'{i}-native', root, True)
    if len(root.find('known')):
        changed = copy.deepcopy(root)
        changed.find('known').clear()
        check(f'{i}-lost-integer-premise', changed, False)
        changed = copy.deepcopy(root)
        wanted = changed.find('known/var').text
        bindings = changed.find('bindings')
        for binding in list(bindings):
            if binding.find('var').text == wanted:
                bindings.remove(binding)
        check(f'{i}-missing-variable-binding', changed, False)
    changed = copy.deepcopy(root)
    bindings = changed.find('bindings')
    if len(bindings):
        bindings.append(copy.deepcopy(bindings[0]))
        check(f'{i}-duplicate-variable-binding', changed, False)
    changed = copy.deepcopy(root)
    op = changed.find('evidence')[0]
    op.tag = 'lessEqual' if op.tag == 'less' else 'less'
    check(f'{i}-changed-comparison', changed, False)
    changed = copy.deepcopy(root)
    evidence = changed.find('evidence')
    left, right = evidence[1], evidence[2]
    evidence.remove(left)
    evidence.append(left)
    if ET.tostring(left) != ET.tostring(right):
        check(f'{i}-swapped-operands', changed, False)
    changed = copy.deepcopy(root)
    variable = changed.find('formula//variableId')
    if variable is not None:
        variable.text = 'corrupted_coordinate'
        check(f'{i}-changed-target-coordinate', changed, False)
    changed = copy.deepcopy(root)
    constant = changed.find('formula//constant')
    if constant is not None:
        constant.text = str(int(constant.text) + 1)
        check(f'{i}-changed-target-constant', changed, False)
report = dict(source_certified=False, checker_sha256=hashlib.sha256(a.checker.read_bytes()).hexdigest(), results=results)
(a.output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
failed = [r['name'] for r in results if r['expected'] != r['accepted'] or r['returncode'] not in (0, 1)]
if failed:
    raise SystemExit('failed: ' + ', '.join(failed))
print(f'{len(results)} numeric guard correspondence checks passed; no source verdict')
