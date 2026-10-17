#!/usr/bin/env python3
"""Rebuild Ferrum and regenerate packaged proofs from durable search-only assets."""
import argparse, concurrent.futures, gzip, json, math, os, pathlib, shutil, tarfile
from replay import execute, certified, sha, write, trs, csr
from oracle_audit import audit
from suite import inside
from root_audit import compare as audit_root


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--manifest', type=pathlib.Path, required=True)
    p.add_argument('--assets', type=pathlib.Path, required=True)
    p.add_argument('--checker', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--rust-toolchain', default='1.95.0')
    a = p.parse_args()
    if a.jobs < 1:
        p.error('jobs must be positive')
    base = a.manifest.resolve().parent
    manifest = json.loads(a.manifest.read_text())
    assets = a.assets.resolve()
    asset_manifest = json.loads((assets / 'manifest.json').read_text())
    if asset_manifest['ferrum_revision'] != manifest['provenance']['source_revision']:
        raise ValueError('Ferrum revision mismatch')
    if asset_manifest['oracle_uncompressed_sha256'] != manifest['provenance']['oracle_sha256']:
        raise ValueError('Oracle identity mismatch')
    for name, info in asset_manifest['files'].items():
        if sha(inside(assets, name)) != info['sha256']:
            raise ValueError('Replay asset hash mismatch: ' + name)
    output = a.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for archive, directory in [('ferrum-source.tar.gz', 'source'), ('lp-tools.tar.gz', 'lp-tools')]:
        with tarfile.open(assets / archive) as t:
            t.extractall(output / directory, filter='data')
    frozen_inputs=None
    if manifest.get('input_archive'):
        archive=inside(assets,manifest['input_archive'])
        if sha(archive)!=manifest['input_archive_sha256']:
            raise ValueError('Full replay input archive changed')
        frozen_inputs=output/'frozen-inputs'
        with tarfile.open(archive) as t:t.extractall(frozen_inputs,filter='data')
    oracle = output / 'oracle.jsonl'
    with gzip.open(assets / 'oracle.jsonl.gz', 'rb') as src, oracle.open('wb') as dst:
        shutil.copyfileobj(src, dst)
    audited = audit(oracle)
    write(output / 'oracle-audit.json', audited)
    if audited['sha256'] != asset_manifest['oracle_uncompressed_sha256'] or audited['forbidden'] or audited['unresolved_aliases']:
        raise ValueError('Search-only oracle audit failed')
    env = {k: v for k, v in os.environ.items() if not k.startswith(('FERRUM_', 'CETA_', 'HPCTIX'))}
    build = execute(['cargo', '+' + a.rust_toolchain, 'build', '--release', '--locked', '--offline',
                     '--target-dir', str(output / 'cargo')], output / 'source', env, output / 'build', 1800)
    write(output / 'build.json', build)
    if build['returncode'] != 0 or build['timed_out']:
        raise RuntimeError('Pinned Ferrum build failed; see build logs')
    ferrum = output / 'cargo/release/ferrum'
    checker = a.checker.resolve()
    profile = manifest['provenance']['profile'].copy()
    profile.update(FERRUM_LP_PYTHONPATH=str(output / 'lp-tools'), CETA_CSR_BIN=str(checker),
                   PYTHONDONTWRITEBYTECODE='1', FERRUM_DP_LLM_NO_FALLBACK='1')
    env.update(profile)
    write(output / 'metadata.json', dict(scope=manifest['scope'], source_revision=asset_manifest['ferrum_revision'],
          ferrum_sha256=sha(ferrum), checker_sha256=sha(checker), oracle_sha256=audited['sha256'],
          profile=profile, rust_toolchain=a.rust_toolchain, manifest_sha256=sha(a.manifest)))

    def one(row):
        run = output / row['id']
        run.mkdir()
        result = dict(id=row['id'], root=row['root'], expected_answer=row['answer'], passed=False)
        try:
            source = inside(frozen_inputs,row['root']) if frozen_inputs else inside(base, row['input'])
            if sha(source) != row['input_sha256']:
                raise ValueError('Input hash changed')
            inp = inside(output / 'inputs', row['root'])
            inp.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, inp)
            proof = run / 'proof.cpf.xml'
            ceiling = max(2880, math.ceil(1.2 * row['replay']['elapsed_seconds'] + 60))
            command = [str(ferrum), 'prove', str(inp), '--cpf', str(proof), '--cpf-mode', 'auto',
                       '--strategy', f'timeout({ceiling}s,fail)', '--utility-guidance-manifest', str(oracle),
                       '--no-top-level-llm', '--processor-events', str(run / 'processor-events.jsonl')]
            localenv=env|{'FERRUM_ORACLE_TIME_SCALE_PERCENT':str(row.get('oracle_time_scale_percent',profile['FERRUM_ORACLE_TIME_SCALE_PERCENT']))}
            result['oracle_time_scale_percent']=int(localenv['FERRUM_ORACLE_TIME_SCALE_PERCENT'])
            result['replay'] = execute(command, run, localenv, run / 'ferrum', ceiling + 30)
            if result['replay']['returncode'] != 0 or result['replay']['timed_out'] or not proof.is_file():
                raise ValueError('Fresh replay failed')
            result['cpf_sha256'] = sha(proof)
            result['correspondence'] = audit_root(inp.read_text(), proof, row['answer'], row['category'])
            result['checks'] = []
            timeout = max(600, 1.5 * max(c['elapsed_seconds'] for c in row['reference_checks']) + 30)
            for i in [1, 2]:
                prefix = run / f'check-{i}'
                c = execute([str(checker), str(proof)], run, env, prefix, timeout)
                c['certified'] = certified(c, prefix)
                result['checks'].append(c)
            result['passed'] = all(c['certified'] for c in result['checks'])
            if not result['passed']:
                raise ValueError('Twice-certification gate failed')
        except Exception as e:
            result['error'] = type(e).__name__ + ': ' + str(e)
        write(run / 'result.json', result)
        return result

    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        results = list(pool.map(one, manifest['positives']))
    summary = dict(scope=manifest['scope'], roots=len(results), passed=sum(r['passed'] for r in results),
                   expected_roots=sorted(r['root'] for r in manifest['positives']),
                   certified_roots=sorted(r['root'] for r in results if r['passed']),
                   failures=[r for r in results if not r['passed']])
    write(output / 'summary.json', summary)
    print(json.dumps(summary))
    raise SystemExit(bool(summary['failures']))


if __name__ == '__main__':
    main()
