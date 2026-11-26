#!/usr/bin/env python3
"""ITS version/claim boundaries, historical opt-in, and malformed witness rejection."""
import argparse
import copy
import gzip
import hashlib
import json
import subprocess
from pathlib import Path
from lxml import etree as E

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
root = Path(__file__).resolve().parents[2]
fixtures = root/'tests/unified/cpf5-its'
schema = E.XMLSchema(E.parse(str(root/'xml/cpf5.xsd')))
checker = a.checker.resolve()
identity = hashlib.sha256(checker.read_bytes()).hexdigest()
results = []
for row in json.loads((fixtures/'manifest.json').read_text())['cases']:
    raw = gzip.decompress((fixtures/row['file']).read_bytes())
    assert hashlib.sha256(raw).hexdigest() == row['sha256']
    original = E.fromstring(raw)
    schema.assertValid(original)
    cases = [('cpf5', original, [], True)]
    for version in ('3', '3.0', '4', '4.0', '5.0', '6.0', '7.0'):
        doc = copy.deepcopy(original)
        doc.find('cpfVersion').text = version
        cases.append((version, doc, [], version in ('5.0', '6.0')))
        cases.append(('legacy-'+version, doc, ['--legacy'], version != '7.0'))
    for mutation in ('answer', 'property', 'empty-proof', 'missing-input'):
        doc = copy.deepcopy(original)
        if mutation == 'answer':
            doc.find('answer')[0].tag = 'no' if doc.find('answer/yes') is not None else 'yes'
        elif mutation == 'property':
            doc.find('property')[0].tag = 'confluence'
        elif mutation == 'empty-proof':
            doc.find('proof')[0].clear()
        else:
            doc.remove(doc.find('input'))
        cases.append((mutation, doc, [], False))
    for name, doc, flags, expected in cases:
        path = a.output/(row['name']+'-'+name+'.xml')
        path.write_bytes(E.tostring(doc))
        command = [str(checker), '--category', 'its', *flags, str(path)]
        q = subprocess.run(command, capture_output=True, text=True, timeout=60)
        accepted = q.returncode == 0 and q.stdout.strip() == 'CERTIFIED'
        results.append(dict(case=row['name']+'/'+name, command=command, expected=expected,
                            passed=accepted == expected, exit=q.returncode, stdout=q.stdout, stderr=q.stderr))
result = dict(checker_sha256=identity, checker_stable=hashlib.sha256(checker.read_bytes()).hexdigest() == identity,
              cases=len(results), passed=all(r['passed'] for r in results), results=results)
(a.output/'results.json').write_text(json.dumps(result, indent=2)+'\n')
print(result['cases'], result['passed'])
assert result['passed'] and result['checker_stable']
