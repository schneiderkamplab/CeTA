#!/usr/bin/env python3
"""Twice-check a frozen supplemental campaign inventory, including NO answers.

Input correspondence and binary identity are mandatory. This is not a fresh
oracle-only replay and does not establish missing generation provenance.
"""
import argparse, concurrent.futures, gzip, json, os, pathlib, shutil
from replay import execute, certified, sha, write
from root_audit import compare


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for key in ['manifest', 'checker', 'output']:
        p.add_argument('--' + key, type=pathlib.Path, required=True)
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=float, default=1200)
    p.add_argument('--hpc-checker', type=pathlib.Path)
    a = p.parse_args()
    if a.jobs < 1 or a.timeout <= 0:
        p.error('Positive jobs and timeout required')
    manifest = a.manifest.resolve(); base = manifest.parent
    rows = json.loads(manifest.read_text())['roots']
    if len({r['id'] for r in rows}) != len(rows):
        raise ValueError('Duplicate certificate identities')
    out = a.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    checker = a.checker.resolve()
    env = {k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')}
    write(out / 'metadata.json', dict(manifest_sha256=sha(manifest),
        checker_sha256=sha(checker), hpc_checker_sha256=sha(a.hpc_checker) if a.hpc_checker else None,
        runner_sha256=sha(pathlib.Path(__file__)),
        audit_sha256=sha(pathlib.Path(__file__).with_name('root_audit.py')), timeout=a.timeout,
        scope='Frozen supplemental certificates; no Ferrum regeneration'))
    def one(row):
        run = out / row['id']; run.mkdir()
        result = dict(id=row['id'], root=row['root'], answer=row['answer'],
            proof_sha256=row['proof_sha256'], input_sha256=row['input_sha256'], checks=[], passed=False)
        try:
            inp = base / row['id'] / 'input.ari'; proof = run / 'proof.cpf.xml'
            with gzip.open(base / row['id'] / 'proof.cpf.xml.gz', 'rb') as src, proof.open('wb') as dest:
                shutil.copyfileobj(src, dest)
            if sha(proof) != row['proof_sha256'] or sha(inp) != row['input_sha256']:
                raise ValueError('Frozen input or certificate changed')
            result['audit'] = compare(inp.read_text(), proof, row['answer'], row['category'])
            binaries = [checker, checker] + ([a.hpc_checker.resolve()] if a.hpc_checker else [])
            for i, binary in enumerate(binaries):
                prefix = run / ('check-' + str(i))
                check = execute([str(binary), str(proof)], run,
                    env | {'HPCTIXFILE':str(run / 'coverage.tix')}, prefix, a.timeout)
                check['certified'] = certified(check, prefix)
                result['checks'].append(check)
            result['passed'] = all(c['certified'] for c in result['checks'])
        except Exception as e:
            result['error'] = type(e).__name__ + ': ' + str(e)
        write(run / 'result.json', result)
        return result
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        results = list(pool.map(one, rows))
    report = dict(results=results, passed=all(r['passed'] for r in results),
        expected_ids=sorted(r['id'] for r in rows),
        certified_ids=sorted(r['id'] for r in results if r['passed']),
        failures=[r['id'] for r in results if not r['passed']])
    write(out / 'summary.json', report)
    print(json.dumps(dict(roots=len(rows), passed=report['passed'], failures=report['failures'])))
    raise SystemExit(not report['passed'])


if __name__ == '__main__':
    main()
