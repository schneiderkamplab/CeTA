#!/usr/bin/env python3
"""Mutation-check generated conditional-contract code against a native receipt.

This is a component test, not source certification. Keep all attempted XML and
checker output in a fresh output directory; no expected verdict authorizes a root.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--receipt', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
root = ET.parse(a.receipt).getroot()
cases = [('native', root, True)]

def mutate(name, fn):
    changed = copy.deepcopy(root)
    fn(changed)
    cases.append((name, changed, False))

def remove_first(r, path):
    parent = r.find(path)
    assert parent is not None and len(parent)
    parent.remove(parent[0])

def change_first(r, path, value):
    node = r.find(path)
    assert node is not None
    node.text = value

def erase_required(r):
    for context in r.findall('summaries/summary/contexts/context'):
        required = context.find('required')
        if len(required):
            required.clear()
            return
    raise AssertionError('fixture needs a conditional input')

def erase_helper_inputs(r):
    for inputs in r.findall('.//helperTransferFact/inputs'):
        if len(inputs):
            inputs.clear()
            return
    raise AssertionError('fixture needs a conditional helper use')

mutate('missing-clause-proof', lambda r: remove_first(r, 'proofs'))
mutate('missing-context-proof', lambda r: remove_first(r, 'proofs/clause/contexts'))
mutate('duplicate-summary', lambda r: r.find('summaries').append(copy.deepcopy(r.find('summaries/summary'))))
mutate('lost-input-premise', erase_required)
mutate('lost-helper-input-evidence', erase_helper_inputs)
mutate('bad-input-position', lambda r: change_first(r, './/inputFact/argument', '999999'))
mutate('bad-helper-rule', lambda r: change_first(r, './/helperTransferFact/rule', '999999'))
mutate('bad-helper-call', lambda r: change_first(r, './/helperTransferFact/call', '999999'))
mutate('bad-helper-output', lambda r: change_first(r, './/helperTransferFact/argument', '999999'))
mutate('bad-evaluation-result', lambda r: change_first(r, './/evaluationFact/result', 'unjustified_result'))
records = []
for name, tree, expected in cases:
    xml = ET.tostring(tree, encoding='utf-8')
    file = a.output / (name + '.xml')
    file.write_bytes(xml)
    checked = subprocess.run([str(a.checker.resolve()), str(file.resolve())], capture_output=True, text=True, timeout=30)
    accepted = checked.returncode == 0
    records.append(dict(name=name, expected=expected, accepted=accepted,
                        exit_code=checked.returncode, stdout=checked.stdout, stderr=checked.stderr,
                        sha256=hashlib.sha256(xml).hexdigest()))
result = dict(schema='ferrum.prolog-success-transfer-component.v1', source_certified=False,
              checker_sha256=hashlib.sha256(a.checker.read_bytes()).hexdigest(),
              receipt_sha256=hashlib.sha256(a.receipt.read_bytes()).hexdigest(), tests=records)
(a.output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
assert all(r['accepted'] == r['expected'] for r in records), 'component test mismatch; see retained evidence'
print(f'{len(records)} generated component checks passed; no source verdict')
