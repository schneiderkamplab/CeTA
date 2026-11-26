#!/usr/bin/env python3
"""Check retained CPF5 HO certificates through Ferrum's original-input boundary."""
import argparse
import concurrent.futures
import hashlib
import json
import subprocess
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--converted', type=Path, required=True)
p.add_argument('--ferrum', type=Path, required=True)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--workers', type=int, default=16)
a = p.parse_args()
assert 1 <= a.workers <= 32
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ferrum, checker = a.ferrum.resolve(), a.checker.resolve()
pins = dict(ferrum_sha256=sha(ferrum), checker_sha256=sha(checker), converted_sha256=sha(a.converted))
jobs = [json.loads(line) for line in a.converted.read_text().splitlines()]
jobs = [r for r in jobs if r['category'] == 'Higher_Order_Rewriting']
a.output.mkdir(parents=True, exist_ok=False)
(a.output/'pins.json').write_text(json.dumps(pins, indent=2)+'\n')

def run(row):
    command = [str(ferrum), 'cert', 'check-higher-order', row['source'], row['certificate'],
               '--answer', row['expected'], '--ceta', str(checker)]
    result = dict(root=row['root'], command=command, passed=False)
    try:
        assert sha(Path(row['source'])) == row['source_sha256']
        assert sha(Path(row['certificate'])) == row['certificate_sha256']
        q = subprocess.run(command, capture_output=True, text=True, timeout=600)
        result.update(exit=q.returncode, stdout=q.stdout, stderr=q.stderr)
        assert q.returncode == 0
        receipt = json.loads(q.stdout)
        assert receipt['certified'] and receipt['correspondence_checked']
        assert receipt['original_sha256'] == row['source_sha256']
        assert receipt['certificate_sha256'] == row['certificate_sha256']
        assert receipt['checker_sha256'] == pins['checker_sha256']
        assert receipt['answer'] == row['expected'].upper()
        result['passed'] = True
    except Exception as error:
        result['error'] = repr(error)
    return result

rows = []
with (a.output/'results.jsonl').open('w') as f, concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
    for row in pool.map(run, jobs):
        rows.append(row)
        f.write(json.dumps(row)+'\n')
        f.flush()
assert sha(ferrum) == pins['ferrum_sha256'] and sha(checker) == pins['checker_sha256']
result = dict(pins=pins, required=len(jobs), passed=sum(r['passed'] for r in rows),
              failures=[r for r in rows if not r['passed']])
(a.output/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
print(result['passed'], '/', result['required'])
assert not result['failures']
