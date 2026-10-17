#!/usr/bin/env python3
"""Investigate suite slowdown candidates with interleaved reference repeats."""
import argparse, gzip, json, os, pathlib, re, shutil, statistics
from replay import execute, certified, sha, write
from suite import inside


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--manifest', type=pathlib.Path, required=True)
    p.add_argument('--suite-result', type=pathlib.Path, required=True)
    p.add_argument('--reference', type=pathlib.Path, required=True)
    p.add_argument('--candidate', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    p.add_argument('--repeats', type=int, default=5)
    p.add_argument('--instrumented', action='store_true')
    p.add_argument('--cpu', type=int, help='Pin this investigation and its own children to one allowed CPU')
    a = p.parse_args()
    if a.repeats < 3:
        p.error('At least three interleaved repeats are required')
    if a.cpu is not None:
        if not hasattr(os,'sched_getaffinity') or a.cpu not in os.sched_getaffinity(0):p.error('CPU not available in this process affinity')
        os.sched_setaffinity(0,{a.cpu})
    manifest = json.loads(a.manifest.read_text())
    suite = json.loads(a.suite_result.read_text())
    binaries = {'reference': a.reference.resolve(), 'candidate': a.candidate.resolve()}
    if not suite['acceptance_passed']:
        p.error('Resolve acceptance failures before evaluating performance')
    if sha(binaries['candidate']) != suite['hpc_checker_sha256' if a.instrumented else 'checker_sha256']:
        p.error('Candidate binary differs from the measured suite')
    if sha(binaries['reference']) != manifest['provenance']['hpc_sha256' if a.instrumented else 'checker_sha256']:
        p.error('Reference binary differs from the frozen baseline')
    base = a.manifest.resolve().parent
    output = a.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    selected = set(suite['hpc_slowdown_candidates' if a.instrumented else 'slowdown_candidates'])
    rows = {r['id']: r|dict(kind='positive') for r in manifest['positives']}
    if not a.instrumented:rows.update({r['id']:r|dict(kind='negative') for r in manifest['negatives']})
    if selected - rows.keys():
        raise ValueError('Unknown slowdown candidates')
    results = []
    for rid in sorted(selected):
        row = rows[rid]
        run = output / rid
        run.mkdir()
        compressed = inside(base, row['certificate'])
        if sha(compressed) != row['compressed_sha256']:
            raise ValueError('Changed certificate')
        proof = run / 'proof.cpf.xml'
        with gzip.open(compressed, 'rb') as src, proof.open('wb') as dst:
            shutil.copyfileobj(src, dst)
        if sha(proof) != row['cpf_sha256' if row['kind']=='positive' else 'mutation_sha256']:
            raise ValueError('Changed uncompressed certificate')
        checks = {'reference': [], 'candidate': []}
        references = [row['reference_hpc']] if a.instrumented else row['reference_checks' if row['kind']=='positive' else 'checks']
        timeout = max(60, 1.5 * max(c['elapsed_seconds'] for c in references) + 30)
        for i in range(a.repeats + 1):
            # Warm both binaries once, then alternate the first checker to reduce
            # systematic cache/order bias. No unrelated processes are modified.
            for name in (['reference', 'candidate'] if i % 2 == 0 else ['candidate', 'reference']):
                prefix = run / f'{name}-{i}'
                env={k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')}
                if a.instrumented:env['HPCTIXFILE']=str(prefix.with_suffix('.tix'))
                result = execute([str(binaries[name]), str(proof)], run, env, prefix, timeout)
                if row['kind']=='positive':
                    result['certified']=certified(result,prefix)
                    result['outcome_passed']=result['certified']
                else:
                    text=prefix.with_suffix('.stdout').read_text()+prefix.with_suffix('.stderr').read_text()
                    result['semantic_rejection']=result['returncode']==1 and not result['timed_out'] and text.startswith('REJECTED') and bool(re.search(row['expected_diagnostic_regex'],text,re.S|re.I))
                    result['outcome_passed']=result['semantic_rejection']
                if a.instrumented and prefix.with_suffix('.tix').exists():prefix.with_suffix('.tix').unlink()
                result['warmup'] = i == 0
                checks[name].append(result)
        passed = all(c['outcome_passed'] for cs in checks.values() for c in cs)
        medians = {n: statistics.median(c['elapsed_seconds'] for c in cs if not c['warmup']) for n, cs in checks.items()}
        result = dict(id=rid, kind=row['kind'], checks=checks, acceptance_passed=passed, medians=medians,
                      slowdown_ratio=medians['candidate'] / medians['reference'])
        result['confirmed_slowdown'] = passed and result['slowdown_ratio'] > 1.2
        write(run / 'result.json', result)
        results.append(result)
    summary = dict(cpu_affinity=sorted(os.sched_getaffinity(0)) if hasattr(os,'sched_getaffinity') else None,mode='instrumented' if a.instrumented else 'production',source_suite_sha256=sha(a.suite_result),reference_sha256=sha(binaries['reference']), candidate_sha256=sha(binaries['candidate']),
                   method='One warmup and alternating-order sequential repeats; median comparison.',
                   results=results, acceptance_passed=all(r['acceptance_passed'] for r in results),
                   confirmed_slowdowns=[r['id'] for r in results if r['confirmed_slowdown']])
    write(output / 'summary.json', summary)
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}))
    raise SystemExit(not summary['acceptance_passed'] or bool(summary['confirmed_slowdowns']))


if __name__ == '__main__':
    main()
