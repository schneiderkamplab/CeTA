#!/usr/bin/env python3
"""Native higher-order witnesses require explicit legacy opt-in."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--samples', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
checker = a.checker.resolve()
identity = sha(checker)
rows = []
for sample in json.loads(a.samples.read_text()).values():
    assert sha(Path(sample['proof'])) == sample['proof_sha256']
    files = [sample['proof']]
    category = 'higher-order'
    if sample.get('child'):
        assert sha(Path(sample['child'])) == sample['child_sha256']
        files.append(sample['child'])
        category = 'higher-order-delegation'
    for legacy in (False, True):
        command = [str(checker), '--category', category, *(['--legacy'] if legacy else []), *files]
        q = subprocess.run(command, capture_output=True, text=True, timeout=60)
        accepted = q.returncode == 0 and q.stdout.startswith('CERTIFIED')
        rows.append(dict(command=command, exit=q.returncode, stdout=q.stdout,
                         stderr=q.stderr, expected=legacy, passed=accepted == legacy))
assert sha(checker) == identity
result = dict(checker_sha256=identity, samples_sha256=sha(a.samples), passed=all(r['passed'] for r in rows), cases=rows)
a.output.write_text(json.dumps(result, indent=2)+'\n')
print(len(rows), result['passed'])
assert result['passed']
