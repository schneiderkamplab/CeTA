#!/usr/bin/env python3
"""Check inherited first-order CPF4 proof forms under CPF5 and CPF6 envelopes."""
import argparse
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
checker = a.checker.resolve()
identity = hashlib.sha256(checker.read_bytes()).hexdigest()
rows = []
for version in (4, 5, 6):
    schema = E.XMLSchema(E.parse(str(root/f'xml/cpf{version}.xsd')))
    for stem, category, flags in (
        ('cycle', 'cycle', []), ('conditional', 'conditional', ['--ordinary']),
        ('conditional-operational', 'conditional', []), ('erasure', 'conditional-erasure', [])):
        doc = E.parse(str(root/'tests/unified/cpf4-first-order'/f'{stem}.xml'))
        doc.find('cpfVersion').text = f'{version}.0'
        schema.assertValid(doc)
        for mutate in (False, True):
            if mutate:
                answer = doc.find('answer')[0]
                answer.tag = 'no' if answer.tag == 'yes' else 'yes'
            path = a.output/f'{stem}-{version}-{mutate}.xml'
            path.write_bytes(E.tostring(doc))
            command = [str(checker), '--category', category, *flags, str(path)]
            q = subprocess.run(command, capture_output=True, text=True, timeout=60)
            accepted = q.returncode == 0 and q.stdout.strip() == 'CERTIFIED'
            rows.append(dict(case=path.name, command=command, exit=q.returncode, stdout=q.stdout,
                             stderr=q.stderr, expected=not mutate, passed=accepted != mutate))
result = dict(checker_sha256=identity, passed=all(r['passed'] for r in rows), cases=rows)
assert hashlib.sha256(checker.read_bytes()).hexdigest() == identity
(a.output/'results.json').write_text(json.dumps(result, indent=2)+'\n')
print(len(rows), result['passed'])
assert result['passed']
