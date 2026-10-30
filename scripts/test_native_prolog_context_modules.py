#!/usr/bin/env python3
"""Check native contextual modules and semantic mutations; no source verdict."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
p.add_argument('modules', nargs='+', type=Path)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
results = []
def check(name, root, expected):
    path = a.output / (name + '.xml')
    ET.ElementTree(root).write(path, encoding='unicode')
    run = subprocess.run([str(a.checker.resolve()), str(path.resolve())], capture_output=True, text=True, timeout=30)
    results.append(dict(name=name, expected=expected, accepted=run.returncode == 0,
                        returncode=run.returncode, stdout=run.stdout, stderr=run.stderr))
for i, path in enumerate(a.modules):
    root = ET.parse(path).getroot()
    if root.tag != 'prologContextModule':
        raise SystemExit('expected native contextual module')
    for repeat in range(2):
        check(f'{i}-complete-{repeat}', root, True)
    for tag in ('nodes', 'returnStates', 'contexts', 'typings', 'actions'):
        changed = copy.deepcopy(root)
        changed.find(tag).remove(changed.find(tag)[0])
        check(f'{i}-missing-{tag}', changed, False)
    changed = copy.deepcopy(root)
    changed.find('residual').clear()
    check(f'{i}-missing-residual', changed, False)
    changed = copy.deepcopy(root)
    g = ET.SubElement(changed.find('contexts')[0].find('guards'), 'integerGuard')
    ET.SubElement(g, 'var').text = 'unproved'
    check(f'{i}-unproved-entry-domain', changed, False)
    changed = copy.deepcopy(root)
    action = changed.find('actions/integerTest')
    action.remove(action.find('link'))
    check(f'{i}-missing-integer-branch', changed, False)
    for j, action in enumerate(root.find('actions')):
        if action.tag in ('integerComparison', 'stagedIntegerEvaluation'):
            changed = copy.deepcopy(root)
            changed.find('typings')[j].clear()
            check(f'{i}-missing-pre-operation-type-{j}', changed, False)
        if action.tag == 'stagedIntegerEvaluation':
            changed = copy.deepcopy(root)
            changed.find('actions')[j].find('equality/link/target').text = '99999'
            check(f'{i}-invalid-equality-target-{j}', changed, False)
    # The same source table cannot certify another clause head.
    changed = copy.deepcopy(root)
    changed.find('program/clause/head/funapp/user').text = '0:changed_source'
    check(f'{i}-changed-source-head', changed, False)
report = dict(source_certified=False, checker_sha256=hashlib.sha256(a.checker.read_bytes()).hexdigest(),
              inputs=[dict(path=str(p.resolve()), sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in a.modules], results=results)
(a.output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
failed = [r['name'] for r in results if r['accepted'] != r['expected'] or r['returncode'] not in (0, 1)]
if failed:
    raise SystemExit('failed native module checks: ' + ', '.join(failed))
print(f'{len(results)} native contextual module checks passed; no source verdict')
