#!/usr/bin/env python3
"""Check complete native numeric rows and mutations, without source verdicts."""
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
    run = subprocess.run([str(a.checker.resolve()), str(path.resolve())], text=True,
                         capture_output=True, timeout=30)
    results.append(dict(name=name, expected=expected, accepted=run.returncode == 0,
                        returncode=run.returncode, stdout=run.stdout, stderr=run.stderr))
paths = sorted(a.receipts.glob('*-numeric-path-*.xml'))
if not paths:
    raise SystemExit('no native numeric path receipts')
for i, path in enumerate(paths):
    root = ET.parse(path).getroot()
    check(f'{i}-native', root, True)
    for tag in ('known', 'observations', 'tests', 'bindings', 'outputs'):
        changed = copy.deepcopy(root)
        if len(changed.find(tag)):
            changed.find(tag).clear()
            check(f'{i}-missing-{tag}', changed, False)
    for tag in ('inputs', 'outputs'):
        changed = copy.deepcopy(root)
        endpoint = changed.find(tag + '/endpoint')
        if endpoint is not None:
            endpoint.find('coordinate').text = 'corrupted_coordinate'
            check(f'{i}-changed-{tag}-coordinate', changed, False)
            changed = copy.deepcopy(root)
            changed.find(tag).append(copy.deepcopy(changed.find(tag + '/endpoint')))
            check(f'{i}-duplicate-{tag}', changed, False)
    conjunction = root.find('formula/conjunction')
    if conjunction is not None:
        for j in range(len(conjunction)):
            changed = copy.deepcopy(root)
            node = changed.find('formula/conjunction')
            node.remove(node[j])
            check(f'{i}-missing-formula-conjunct-{j}', changed, False)
    changed = copy.deepcopy(root)
    tests = changed.find('tests')
    if len(tests) > 1:
        first = tests[0]
        tests.remove(first)
        tests.append(first)
        check(f'{i}-reordered-observation-evidence', changed, False)
    changed = copy.deepcopy(root)
    local = changed.find('bindings/binding/post/variableId')
    output = changed.find('outputs/endpoint/coordinate')
    if local is not None and output is not None:
        auxiliary = local.text
        for coordinate in changed.findall('.//variableId'):
            if coordinate.text == auxiliary:
                coordinate.text = output.text
        check(f'{i}-auxiliary-aliases-output-with-matching-formula', changed, False)
report = dict(source_certified=False,
              checker_sha256=hashlib.sha256(a.checker.read_bytes()).hexdigest(), results=results)
(a.output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
failed = [r['name'] for r in results if r['expected'] != r['accepted'] or r['returncode'] not in (0, 1)]
if failed:
    raise SystemExit('failed: ' + ', '.join(failed))
print(f'{len(results)} numeric path correspondence checks passed; no source verdict')
