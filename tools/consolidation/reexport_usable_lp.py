#!/usr/bin/env python3
"""Replay the pinned baseline/indexed LP exports in an isolated Isabelle home.

Requires a compatible private Proof_Checker heap and AFP via the environment.
The saved source snapshot and audited export wrappers are the actual inputs of
this milestone, not mutable source files from the development worktree.
"""
import argparse, concurrent.futures, hashlib, json, subprocess, tarfile, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/usable-membership-20261026'
OLD_ROOT = '/work/dfm/festschrift/CeTA-consolidated'
OLD_OUTPUT = OLD_ROOT + '/target/usable-membership-20261026'

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--isabelle', type=Path, required=True)
    p.add_argument('--base-theories', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--workers', type=int, default=4)
    a = p.parse_args()
    out = a.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = out / 'lp-source-committed'
    source.mkdir()
    with tarfile.open(DOC / 'lp-source.tar.gz', 'r:gz') as bundle:
        for member in bundle.getmembers():
            target = source / member.name
            if not member.isfile() or not target.resolve().is_relative_to(source):
                raise ValueError(member.name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(bundle.extractfile(member).read())
    wrappers = out / 'lp-wrappers'
    wrappers.mkdir()
    expected = json.loads((DOC / 'lp-reproduction.json').read_text())
    for path in (DOC / 'export-wrappers').glob('*LP*.thy'):
        text = path.read_text().replace(OLD_OUTPUT, str(out)).replace(OLD_ROOT, str(ROOT))
        (wrappers / path.name).write_text(text)
    cmd = [str(a.isabelle.resolve()), 'console', '-n', '-l', 'Proof_Checker',
           '-d', str(a.base_theories.resolve()), '-o', 'threads=4',
           '-o', 'parallel_proofs=0', '-o', 'quick_and_dirty=false']
    def run(row):
        module = row['module']
        for variant in ['baseline', 'indexed']:
            (out / ('lp-' + variant) / module).mkdir(parents=True)
        code = '; '.join('Thy_Info.use_thy_legacy ' + json.dumps(str(wrappers / (v + '_' + module)))
                         for v in ['Baseline', 'Indexed'])
        marker = 'PAIR_VERIFIED_' + module
        code = '((' + code + '; writeln "' + marker + '"; OS.Process.exit OS.Process.success) handle exn => (Runtime.exn_message exn |> writeln; OS.Process.exit OS.Process.failure));\n'
        start = time.monotonic()
        log = out / (module + '.log')
        with log.open('w') as f:
            result = subprocess.run(cmd, input=code, text=True, stdout=f, stderr=subprocess.STDOUT)
        if result.returncode or marker not in log.read_text():
            raise RuntimeError(f'Export failed: {log}')
        for variant in ['baseline', 'indexed']:
            data = (out / ('lp-' + variant) / module / (module + '.hs')).read_bytes()
            if hashlib.sha256(data).hexdigest() != row[variant + '_sha256']:
                raise RuntimeError(f'Export mismatch: {variant} {module}')
        record = dict(module=module, verified=True, seconds=time.monotonic()-start, command=cmd)
        (out / (module + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        print(module, 'verified', flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
        list(pool.map(run, expected))

if __name__ == '__main__':
    main()
