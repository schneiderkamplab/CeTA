#!/usr/bin/env python3
"""Check schema and semantics of CPF4 innermost CSR unhiding examples."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from lxml import etree

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--checker', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
checker = args.checker.resolve()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
identity = sha(checker)
schema = etree.XMLSchema(etree.parse(str(root / 'xml/cpf4.xsd')))
files = sorted((root / 'examples').glob('csr_innermost_unhiding*.cpf.xml'))
assert len(files) == 4
rows = []
for path in files:
    schema.assertValid(etree.parse(str(path)))
    expected = '.reject.' not in path.name
    for repeat in (1, 2):
        command = [str(checker), str(path)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=600)
        accepted = result.returncode == 0 and result.stdout.strip() == 'CERTIFIED'
        rows.append(dict(command=command, sha256=sha(path), repeat=repeat,
                         expected=expected, accepted=accepted, exit=result.returncode,
                         stdout=result.stdout, stderr=result.stderr))
assert sha(checker) == identity
report = dict(checker_sha256=identity, schema_valid=len(files), checks=rows,
              passed=all(r['expected'] == r['accepted'] for r in rows))
with args.output.open('x') as f:
    json.dump(report, f, indent=2)
    f.write('\n')
print(report['passed'], len(rows))
assert report['passed']
