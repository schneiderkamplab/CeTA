#!/usr/bin/env python3
"""Audit complete CPF5 replay coverage, XML, source binding and checker identity."""
import argparse
import concurrent.futures
import hashlib
import json
import subprocess
from pathlib import Path
from lxml import etree as E

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--campaign', type=Path, required=True)
p.add_argument('--expected', type=Path, required=True)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--ferrum', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
checker, ferrum = a.checker.resolve(), a.ferrum.resolve()
identity, producer = sha(checker), sha(ferrum)
manifest = json.loads((a.campaign/'manifest.json').read_text())
assert manifest['pins']['checker'] == identity and manifest['pins']['binary'] == producer
sources_path = Path(manifest['root_manifest_path'])
assert sha(sources_path) == manifest['pins']['root_manifest']
sources = {r['root']: r for r in json.loads(sources_path.read_text())}
expected = {r['root']: r for r in json.loads(a.expected.read_text())}
results = json.loads((a.campaign/'results.json').read_text())
assert len(results) == len(expected) and {r['root'] for r in results} == set(expected)
paths = {}
for path in a.campaign.glob('*/*/result.json'):
    row = json.loads(path.read_text())
    assert row['root'] not in paths
    paths[row['root']] = path.parent
assert set(paths) == set(expected)
root = Path(__file__).resolve().parents[1]
schema = E.XMLSchema(E.parse(str(root/'xml/cpf5.xsd')))
a.output.mkdir(parents=True, exist_ok=False)

def audit(row):
    result = dict(root=row['root'], certified=row['certified'], passed=False)
    try:
        assert 'error' not in row, row.get('error')
        old = expected[row['root']]
        assert not old['certified'] or (row['certified'] and row['status'] == old['status'])
        source = Path(sources[row['root']]['source'])
        assert sha(source) == row['source_sha256'] == old['source_sha256']
        if not row['certified']:
            assert row['exit_code'] in (0, 124), 'infrastructure or producer failure'
            result['disposition'] = 'search-timeout' if row['exit_code'] == 124 else 'unknown'
            if row['exit_code'] == 124:
                resources = json.loads((paths[row['root']]/'search-resources.json').read_text())
                assert resources['limit_reason'] in ('search-wall-time', 'wall-time')
                result['resources'] = resources
        if row['certified']:
            result['disposition'] = 'certified'
            assert row['source_audit'] and row['exit_code'] == 0
            directory = paths[row['root']]
            ho = row['category'] == 'Higher_Order_Rewriting'
            proof = Path(row['native']['proof']) if ho else directory/'native/proof.cpf.xml'
            assert sha(proof) == row['certificate_sha256']
            doc = E.parse(str(proof), E.XMLParser(huge_tree=True))
            schema.assertValid(doc)
            assert doc.findtext('cpfVersion') == '5.0'
            assert doc.find('property')[0].tag == 'termination'
            assert doc.find('answer')[0].tag == row['status']
            if ho:
                assert proof.name.endswith('.cpf.xml')
                assert not row['native'].get('child_proof')
                assert len(row['checks']) == 2
                for i, check in enumerate(row['checks']):
                    assert check['code'] == 0 and check['stdout'].startswith('CERTIFIED')
                    command = json.loads((directory/f'check-{i}-command.json').read_text())
                    assert sha(Path(command[0])) == identity
                command = [str(ferrum), 'cert', 'check-higher-order', str(source), str(proof),
                           '--answer', row['status'], '--ceta', str(checker)]
            else:
                report = row['its_report']
                assert report['checker_sha256'] == identity
                assert report['certificate_sha256'] == row['certificate_sha256']
                assert len(report['checks']) == 2 and all(c['accepted'] and not c['timeout'] for c in report['checks'])
                command = [str(ferrum), 'its-audit', str(source), str(proof)]
            q = subprocess.run(command, capture_output=True, text=True, timeout=600)
            result.update(command=command, exit=q.returncode, stdout=q.stdout, stderr=q.stderr,
                          certificate=str(proof), certificate_sha256=sha(proof), schema_valid=True)
            assert q.returncode == 0
            if ho:
                receipt = json.loads(q.stdout)
                assert receipt['certified'] and receipt['correspondence_checked']
                assert receipt['checker_sha256'] == identity
                assert receipt['original_sha256'] == row['source_sha256']
                assert receipt['certificate_sha256'] == row['certificate_sha256']
                assert receipt['answer'].lower() == row['status']
        result['passed'] = True
    except Exception as error:
        result['error'] = repr(error)
    return result

rows = []
with (a.output/'results.jsonl').open('w') as f, concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    for row in pool.map(audit, results):
        rows.append(row)
        f.write(json.dumps(row)+'\n')
        f.flush()
assert sha(checker) == identity and sha(ferrum) == producer
summary = dict(checker_sha256=identity, ferrum_sha256=producer, roots=len(rows),
               certified=sum(r['certified'] for r in rows), unresolved=sum(not r['certified'] for r in rows),
               search_timeouts=sum(r.get('disposition') == 'search-timeout' for r in rows),
               passed=all(r['passed'] for r in rows), failures=[r for r in rows if not r['passed']])
(a.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
print(summary['roots'], summary['certified'], summary['passed'])
assert summary['passed']
