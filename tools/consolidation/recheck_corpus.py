#!/usr/bin/env python3
"""Recheck every frozen root with a new checker, preserving replay provenance."""
import argparse, concurrent.futures, gzip, json, os, pathlib, shutil, time
from replay import execute, certified, sha, write
from root_audit import compare as audit_root
from suite import inside


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source', type=pathlib.Path, required=True)
    p.add_argument('--inputs', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    p.add_argument('--checker', type=pathlib.Path, required=True)
    p.add_argument('--hpc-checker', type=pathlib.Path)
    p.add_argument('--export-tix', type=pathlib.Path)
    p.add_argument('--source-revision', required=True)
    p.add_argument('--jobs', type=int, default=16)
    p.add_argument('--reaudit-inputs', action='store_true')
    a = p.parse_args()
    if a.jobs < 1 or bool(a.hpc_checker) != bool(a.export_tix):
        p.error('Positive jobs and paired HPC checker/exporter required')
    source, output = a.source.resolve(), a.output.resolve()
    prior = json.loads((source / 'metadata.json').read_text())
    rows = [json.loads(s) for s in (source / 'results.jsonl').read_text().splitlines()]
    if json.loads((source / 'summary.json').read_text())['losses']:
        raise ValueError('Source corpus has unresolved losses')
    identities = {(r['root'], r['expected_answer'], r['input_sha256']) for r in rows}
    expected = {(r['root'], r['answer'], r['input_sha256']) for r in prior['roots']}
    if identities != expected or len(rows) != len(expected) or not all(r['eligible'] for r in rows):
        raise ValueError('Source root set is incomplete, duplicated, or ineligible')
    checker = a.checker.resolve()
    output.mkdir(parents=True, exist_ok=False)
    meta = prior | dict(checker_sha256=sha(checker), hpc_sha256=sha(a.hpc_checker) if a.hpc_checker else None,
                        hpc_source_revision=a.source_revision, prior_stage=str(source),
                        verification_kind='Frozen corpus recheck; not a fresh Ferrum replay',
                        source_results_sha256=sha(source / 'results.jsonl'), runner_sha256=sha(pathlib.Path(__file__)))
    write(output / 'metadata.json', meta)
    env = {k: v for k, v in os.environ.items() if not k.startswith('HPCTIX')}
    def one(row):
        run = output / row['id']
        run.mkdir()
        r = row | dict(prior_checks=row['checks'], checks=[], eligible=False, passed=False)
        try:
            proof = source / row['id'] / 'proof.cpf.xml'
            inp = inside(a.inputs.resolve(), row['root'])
            if sha(proof) != row['cpf_sha256'] or sha(inp) != row['input_sha256']:
                raise ValueError('Frozen proof or original input changed')
            if not row.get('correspondence'):
                raise ValueError('Frozen input audit missing')
            if a.reaudit_inputs:
                r['correspondence'] = audit_root(inp.read_text(), proof, row['expected_answer'], row['category'])
            r['input_audit_reused_by_exact_hash'] = not a.reaudit_inputs
            for name in ['proof.cpf.xml', 'proof.cpf.xml.gz']:
                (run / name).symlink_to(source / row['id'] / name)
            timeout = max(60, 1.5 * max(c['elapsed_seconds'] for c in row['checks']) + 30)
            for i in [1, 2]:
                prefix = run / f'check-{i}'
                c = execute([str(checker), str(proof)], run, env, prefix, timeout)
                c['certified'] = certified(c, prefix)
                r['checks'].append(c)
            if not all(c['certified'] for c in r['checks']):
                raise ValueError('Production certification failed')
            if a.hpc_checker:
                prefix = run / 'hpc'
                c = execute([str(a.hpc_checker.resolve()), str(proof)], run,
                            env | {'HPCTIXFILE': str(run / 'coverage.tix')}, prefix,
                            max(120, 1.5 * row['hpc']['elapsed_seconds'] + 30))
                c['certified'] = certified(c, prefix)
                r['prior_hpc'], r['hpc'] = row['hpc'], c
                if not c['certified']:
                    raise ValueError('Production/HPC agreement failed')
                c = execute([str(a.export_tix.resolve()), str(run / 'coverage.tix')], run, env, run / 'coverage-export', 60)
                if c['returncode'] != 0:
                    raise ValueError('HPC export failed')
                with (run / 'coverage-export.stdout').open('rb') as src, (run / 'coverage.tsv.gz').open('wb') as dst, gzip.GzipFile(filename='', mode='wb', fileobj=dst, mtime=0) as z:
                    shutil.copyfileobj(src, z)
                (run / 'coverage-export.stdout').unlink()
                (run / 'coverage.tix').unlink()
                r['coverage_sha256'] = sha(run / 'coverage.tsv.gz')
                r['eligible'] = True
            r['passed'] = True
        except Exception as e:
            r['error'] = type(e).__name__ + ': ' + str(e)
        write(run / 'result.json', r)
        return r
    results = []
    start = time.monotonic()
    with (output / 'results.jsonl').open('w') as log, concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for r in pool.map(one, rows):
            results.append(r)
            log.write(json.dumps(r, sort_keys=True) + '\n')
            log.flush()
    summary = dict(roots=len(expected), checked=len(results), passed=sum(r['passed'] for r in results),
                   eligible=sum(r['eligible'] for r in results), elapsed_seconds=time.monotonic()-start,
                   losses=[dict(root=r['root'], answer=r['expected_answer'], error=r.get('error')) for r in results if not r['passed']],
                   exact_root_set_preserved=identities == {(r['root'],r['expected_answer'],r['input_sha256']) for r in results})
    write(output / 'summary.json', summary)
    print(json.dumps(summary))
    raise SystemExit(bool(summary['losses']) or not summary['exact_root_set_preserved'])


if __name__ == '__main__':
    main()
