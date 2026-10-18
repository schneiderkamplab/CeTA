#!/usr/bin/env python3
"""Twice recheck a packaged replay's exact frozen roots; never claim regeneration."""
import argparse, concurrent.futures, contextlib, gzip, json, os, pathlib, shutil, threading, time
from replay import execute, certified, sha, write


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['source', 'manifest', 'checker', 'hpc-checker', 'export-tix', 'output']:
        p.add_argument('--' + name, type=pathlib.Path, required=True)
    p.add_argument('--additional-checker', type=pathlib.Path, help='Also check every root with another production entry point')
    p.add_argument('--jobs', type=int, default=8)
    p.add_argument('--resume', action='store_true', help='Reuse hash-verified completed checks; preserve interrupted attempts')
    p.add_argument('--retry-failures', help='With --resume, archive failed attempts and record the investigation justifying retry')
    p.add_argument('--heavy-jobs', type=int, default=4, help='Limit simultaneous roots with prior production checks over 10s or HPC over 60s')
    p.add_argument('--reuse-default-checks-from', type=pathlib.Path,
                   help='Import completed default/HPC checks with identical binary and artifact hashes; excludes additional-checker results')
    a = p.parse_args()
    if a.jobs < 1 or a.heavy_jobs < 1:
        p.error('Positive job count required')
    if a.retry_failures and not a.resume:
        p.error('--retry-failures requires --resume')
    if a.reuse_default_checks_from and a.additional_checker:
        p.error('Imported default checks must be followed by a separate additional-checker campaign')
    source, out = a.source.resolve(), a.output.resolve()
    manifest = json.loads(a.manifest.read_text())
    metadata = json.loads((source / 'metadata.json').read_text())
    summary = json.loads((source / 'summary.json').read_text())
    roots = sorted(r['root'] for r in manifest['positives'])
    assert len(roots) == len(set(roots)), 'Duplicate roots'
    assert metadata['manifest_sha256'] == sha(a.manifest), 'Manifest changed'
    assert summary['passed'] and not summary['failures'], 'Source replay failed'
    assert summary['certified_roots'] == summary['expected_roots'] == roots
    out.mkdir(parents=True, exist_ok=a.resume)
    scope = 'Frozen packaged corpus recheck; no fresh Ferrum generation'
    current_metadata = metadata | dict(
        checker_sha256=sha(a.checker), hpc_sha256=sha(a.hpc_checker),
        checker_revision=None, prior_checker_revision=metadata.get('checker_revision'),
        checker_identity_note='New checker pinned by binary hashes; source/build receipts are recorded separately.',
        additional_checker_sha256=sha(a.additional_checker) if a.additional_checker else None,
        scope=scope, source_metadata_sha256=sha(source / 'metadata.json'),
        runner_sha256=sha(pathlib.Path(__file__)))
    if a.resume:
        previous = json.loads((out / 'metadata.json').read_text())
        for key in ['manifest_sha256', 'checker_sha256', 'hpc_sha256',
                    'additional_checker_sha256', 'source_metadata_sha256', 'scope']:
            assert previous[key] == current_metadata[key], f'Resume identity changed: {key}'
        write(out / f'resume-{time.time_ns()}.json', dict(
            previous_metadata=previous, current_metadata=current_metadata,
            retry_reason=a.retry_failures, jobs=a.jobs, heavy_jobs=a.heavy_jobs))
    else:
        write(out / 'metadata.json', current_metadata)
    if a.reuse_default_checks_from:
        reuse = a.reuse_default_checks_from.resolve()
        previous = json.loads((reuse / 'metadata.json').read_text())
        for key in ['manifest_sha256', 'checker_sha256', 'hpc_sha256', 'source_metadata_sha256', 'scope']:
            assert previous[key] == current_metadata[key], f'Imported check identity changed: {key}'
        write(out / 'imported-checks.json', dict(source=str(reuse), metadata_sha256=sha(reuse / 'metadata.json'),
              scope='Only complete, successful default/HPC checks are reused. Additional-checker failures remain in the original campaign.'))
    shutil.copy2(source / 'oracle-audit.json', out / 'oracle-audit.json')
    env = {k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')}
    def memory_gate():
        # Pause launching new checker processes above the task's memory ceiling.
        deadline = time.monotonic() + 3600
        while True:
            mem = {line.split(':')[0]:int(line.split()[1]) * 1024
                   for line in pathlib.Path('/proc/meminfo').read_text().splitlines()}
            if mem['MemTotal'] - mem['MemAvailable'] < 2 * 1024**4:
                return
            if time.monotonic() > deadline:
                raise RuntimeError('Memory ceiling remained exceeded; checker not launched')
            time.sleep(5)
    heavy_slots = threading.Semaphore(a.heavy_jobs)
    def one(expected):
        prior = json.loads((source / expected['id'] / 'result.json').read_text())
        heavy = max(c['elapsed_seconds'] for c in prior['checks']) > 10 or prior['hpc']['elapsed_seconds'] > 60
        with heavy_slots if heavy else contextlib.nullcontext():
            return check_one(expected)
    def check_one(expected):
        run = out / expected['id']
        prior = source / expected['id']
        row = json.loads((prior / 'result.json').read_text())
        assert (row['root'], row['expected_answer'], row['input_sha256']) == (
            expected['root'], expected['answer'], expected['input_sha256'])
        assert row['passed'] and row['correspondence']
        proof = prior / 'proof.cpf.xml'
        assert sha(proof) == row['cpf_sha256']
        inp = source / 'inputs' / expected['root']
        assert sha(inp) == row['input_sha256'], 'Original input changed'
        if a.reuse_default_checks_from and not run.exists():
            previous_run = reuse / expected['id']
            previous_result = previous_run / 'result.json'
            if previous_result.exists():
                saved = json.loads(previous_result.read_text())
                complete = (len(saved['checks']) == 2 and
                            all(c.get('certified') and certified(c, previous_run / f'check-{i}')
                                for i,c in enumerate(saved['checks'], 1)) and
                            saved.get('hpc', {}).get('certified') and
                            certified(saved['hpc'], previous_run / 'hpc') and
                            saved.get('coverage_sha256') and (previous_run / 'coverage.tsv.gz').exists())
                if complete:
                    for key in ['root', 'expected_answer', 'input_sha256', 'cpf_sha256']:
                        assert saved[key] == row[key], f'Imported result changed: {key}'
                    assert sha(previous_run / 'proof.cpf.xml') == row['cpf_sha256']
                    assert sha(previous_run / 'coverage.tsv.gz') == saved['coverage_sha256']
                    run.mkdir(); (run / 'proof.cpf.xml').symlink_to(proof)
                    for name in ['coverage.tsv.gz', 'check-1.stdout', 'check-1.stderr',
                                 'check-2.stdout', 'check-2.stderr', 'hpc.stdout', 'hpc.stderr']:
                        shutil.copy2(previous_run / name, run / name)
                    saved.pop('additional_checker', None); saved.pop('error', None)
                    saved.update(passed=True, imported_default_checks=dict(
                        result_sha256=sha(previous_result), metadata_sha256=sha(reuse / 'metadata.json')))
                    write(run / 'result.json', saved)
                    return saved
        if a.resume and (run / 'result.json').exists():
            saved = json.loads((run / 'result.json').read_text())
            if not saved['passed']:
                assert a.retry_failures, 'Failed completed checks require investigation, not automatic retry'
                failed = out / 'failed-attempts'; failed.mkdir(exist_ok=True)
                run.rename(failed / (expected['id'] + '-' + str(time.time_ns())))
                return check_one(expected)
            for key in ['root', 'expected_answer', 'input_sha256', 'cpf_sha256']:
                assert saved[key] == row[key], f'Resume result changed: {key}'
            assert sha(run / 'proof.cpf.xml') == row['cpf_sha256']
            assert sha(run / 'coverage.tsv.gz') == saved['coverage_sha256']
            assert len(saved['checks']) == 2
            for i, check in enumerate(saved['checks'], 1):
                assert check['certified'] and certified(check, run / f'check-{i}')
            assert saved['hpc']['certified'] and certified(saved['hpc'], run / 'hpc')
            if a.additional_checker:
                assert saved['additional_checker']['certified'] and certified(saved['additional_checker'], run / 'additional-checker')
            return saved
        if run.exists():
            assert a.resume
            interrupted = out / 'interrupted'; interrupted.mkdir(exist_ok=True)
            run.rename(interrupted / (expected['id'] + '-' + str(time.time_ns())))
        run.mkdir()
        result = row | dict(prior_checks=row['checks'], prior_hpc=row['hpc'],
                            checks=[], passed=False, input_audit_reused_by_exact_hash=True)
        (run / 'proof.cpf.xml').symlink_to(proof)
        try:
            for i in [1,2]:
                prefix = run / f'check-{i}'
                memory_gate()
                c = execute([str(a.checker.resolve()), str(proof)], run, env, prefix,
                            max(60, 1.5 * max(x['elapsed_seconds'] for x in row['checks']) + 30))
                c['certified'] = certified(c, prefix); result['checks'].append(c)
            if not all(c['certified'] for c in result['checks']):
                raise ValueError('Production rejection, crash or timeout')
            prefix = run / 'hpc'
            memory_gate()
            c = execute([str(a.hpc_checker.resolve()), str(proof)], run,
                        env | {'HPCTIXFILE':str(run / 'coverage.tix')}, prefix,
                        max(120, 1.5 * row['hpc']['elapsed_seconds'] + 30))
            c['certified'] = certified(c, prefix); result['hpc'] = c
            if not c['certified']:
                raise ValueError('HPC disagreement, crash or timeout')
            c = execute([str(a.export_tix.resolve()), str(run / 'coverage.tix')],
                        run, env, run / 'coverage', 60)
            if c['returncode'] != 0:
                raise ValueError('HPC export failed')
            with (run / 'coverage.stdout').open('rb') as src, gzip.open(run / 'coverage.tsv.gz','wb') as dst:
                shutil.copyfileobj(src, dst)
            result['coverage_sha256'] = sha(run / 'coverage.tsv.gz')
            (run / 'coverage.stdout').unlink(); (run / 'coverage.tix').unlink()
            if a.additional_checker:
                memory_gate(); prefix = run / 'additional-checker'
                c = execute([str(a.additional_checker.resolve()), str(proof)], run, env, prefix,
                            max(60, 1.5 * max(x['elapsed_seconds'] for x in row['checks']) + 30))
                c['certified'] = certified(c, prefix); result['additional_checker'] = c
                if not c['certified']:
                    raise ValueError('Additional production entry point rejected, crashed or timed out')
            result['passed'] = True
        except Exception as e:
            result['error'] = str(e)
        write(run / 'result.json', result)
        return result
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        rows = list(pool.map(one, manifest['positives']))
    failures = [dict(root=r['root'], error=r.get('error')) for r in rows if not r['passed']]
    result = dict(scope=scope, roots=len(rows), expected_roots=roots,
                  certified_roots=sorted(r['root'] for r in rows if r['passed']),
                  failures=failures, passed=not failures)
    write(out / 'summary.json', result)
    print(json.dumps(dict(roots=len(rows), failures=failures, passed=not failures)))
    raise SystemExit(bool(failures))


if __name__ == '__main__':
    main()
