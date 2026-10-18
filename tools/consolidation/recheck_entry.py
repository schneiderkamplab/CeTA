#!/usr/bin/env python3
"""Check one additional production entry point against exact frozen replay roots."""
import argparse, concurrent.futures, json, os, pathlib, time
from replay import execute, certified, sha, write
from run_logged import memory_used


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['source', 'manifest', 'checker', 'output']:
        p.add_argument('--' + name, type=pathlib.Path, required=True)
    p.add_argument('--jobs', type=int, default=8)
    p.add_argument('--timeout-scale', type=float, default=2,
                   help='Frozen default-production baseline multiplier, plus 30s; minimum 60s')
    a = p.parse_args()
    if a.jobs < 1 or a.timeout_scale < 1.2:
        p.error('Positive job count and at least 20% timeout headroom required')
    source, out, checker = a.source.resolve(), a.output.resolve(), a.checker.resolve()
    manifest = json.loads(a.manifest.read_text())
    metadata = json.loads((source / 'metadata.json').read_text())
    prior_summary = json.loads((source / 'summary.json').read_text())
    roots = sorted(r['root'] for r in manifest['positives'])
    assert len(roots) == len(set(roots)) and metadata['manifest_sha256'] == sha(a.manifest)
    assert prior_summary['passed'] and prior_summary['certified_roots'] == roots
    out.mkdir(parents=True, exist_ok=False)
    write(out / 'metadata.json', dict(scope=__doc__, checker_sha256=sha(checker),
          manifest_sha256=sha(a.manifest), source_metadata_sha256=sha(source / 'metadata.json'),
          timeout_scale=a.timeout_scale, runner_sha256=sha(pathlib.Path(__file__))))
    env = {k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')}
    def one(expected):
        prior = source / expected['id']; run = out / expected['id']; run.mkdir()
        row = json.loads((prior / 'result.json').read_text()); proof = prior / 'proof.cpf.xml'
        assert row['passed'] and row['correspondence']
        assert (row['root'], row['expected_answer'], row['input_sha256']) == (
            expected['root'], expected['answer'], expected['input_sha256'])
        assert sha(proof) == row['cpf_sha256']
        assert sha(source / 'inputs' / expected['root']) == row['input_sha256']
        deadline = time.monotonic() + 3600
        while memory_used() > 2 * 1024**4:
            if time.monotonic() > deadline:
                raise RuntimeError('Memory ceiling remained exceeded; checker not launched')
            time.sleep(5)
        timeout = max(60, a.timeout_scale * max(c['elapsed_seconds'] for c in row['checks']) + 30)
        check = execute([str(checker), str(proof)], run, env, run / 'check', timeout)
        check['certified'] = certified(check, run / 'check')
        result = dict(id=row['id'], root=row['root'], answer=row['expected_answer'],
                      input_sha256=row['input_sha256'], cpf_sha256=row['cpf_sha256'],
                      check=check, passed=check['certified'])
        write(run / 'result.json', result)
        return result
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        rows = list(pool.map(one, manifest['positives']))
    failures = [r['root'] for r in rows if not r['passed']]
    summary = dict(roots=len(rows), expected_roots=roots,
                   certified_roots=sorted(r['root'] for r in rows if r['passed']),
                   failures=failures, passed=not failures,
                   scope='Additional production entry-point check; no Ferrum regeneration or HPC coverage claim.')
    write(out / 'summary.json', summary)
    print(json.dumps(dict(roots=len(rows), failures=failures, passed=not failures)))
    raise SystemExit(bool(failures))


if __name__ == '__main__':
    main()
