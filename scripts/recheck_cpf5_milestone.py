#!/usr/bin/env python3
"""Check every converted retained CPF5 certificate twice, with resumable evidence."""
import argparse
import concurrent.futures
import hashlib
import json
import subprocess
import time
from pathlib import Path
from lxml import etree as E

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--converted', type=Path, required=True)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--workers', type=int, default=32)
p.add_argument('--timeout', type=int, default=600)
a = p.parse_args()
assert 1 <= a.workers <= 32
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
checker = a.checker.resolve()
identity = sha(checker)
summary = json.loads((a.converted/'summary.json').read_text())
assert summary['passed'] == summary['required'] and not summary['failures']
jobs = [json.loads(line) for line in (a.converted/'results.jsonl').read_text().splitlines()]
assert len(jobs) == summary['required']
for index, job in enumerate(jobs):
    job['index'] = index
    proof = Path(job['certificate'])
    assert sha(proof) == job['certificate_sha256']
    doc = E.parse(str(proof), E.XMLParser(huge_tree=True))
    constructor = doc.find('proof')[0].tag
    category = 'its' if job['category'] != 'Higher_Order_Rewriting' else (
        'higher-order-delegation' if constructor.startswith('ho-ceta-') else 'higher-order')
    job['command'] = [str(checker), '--category', category, str(proof)]
a.output.mkdir(parents=True, exist_ok=True)
pins = dict(checker=str(checker), checker_sha256=identity,
            converted_sha256=sha(a.converted/'results.jsonl'), workers=a.workers,
            timeout=a.timeout, passes=2, jobs=jobs)
manifest = a.output/'manifest.json'
if manifest.exists():
    assert json.loads(manifest.read_text()) == pins
else:
    manifest.write_text(json.dumps(pins, indent=2)+'\n')
journal = a.output/'results.jsonl'
done = {}
if journal.exists():
    for line in journal.read_text().splitlines():
        row = json.loads(line)
        assert row['index'] not in done
        done[row['index']] = row
assert set(done) <= set(range(len(jobs)))

def run(job):
    checks = []
    for repeat in (1, 2):
        start = time.monotonic()
        try:
            assert sha(Path(job['certificate'])) == job['certificate_sha256']
            q = subprocess.run(job['command'], capture_output=True, text=True, timeout=a.timeout)
            checks.append(dict(repeat=repeat, exit=q.returncode, stdout=q.stdout,
                               stderr=q.stderr, seconds=time.monotonic()-start,
                               passed=q.returncode == 0 and q.stdout.strip() in
                               ('CERTIFIED', 'CERTIFIED '+job['expected'].upper(),
                                'CERTIFIED HO TERMINATION' if job['expected'] == 'yes' else 'CERTIFIED HO LOOP')))
        except Exception as error:
            checks.append(dict(repeat=repeat, passed=False, error=repr(error),
                               seconds=time.monotonic()-start))
    return dict(index=job['index'], root=job['root'], checks=checks,
                passed=all(c['passed'] for c in checks))

with journal.open('a') as f, concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
    for row in pool.map(run, [j for j in jobs if j['index'] not in done]):
        done[row['index']] = row
        f.write(json.dumps(row)+'\n')
        f.flush()
        if len(done) % 100 == 0:
            print(len(done), '/', len(jobs), flush=True)
assert sha(checker) == identity
result = dict(required=len(jobs), completed=len(done), passed=sum(r['passed'] for r in done.values()),
              failures=[r for r in done.values() if not r['passed']], checker_sha256=identity,
              unresolved_inputs=summary['unresolved'])
(a.output/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
print(result['passed'], '/', result['required'])
assert not result['failures'] and len(done) == len(jobs)
