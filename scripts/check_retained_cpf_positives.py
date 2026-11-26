#!/usr/bin/env python3
"""Recheck a hash-pinned positive CPF fixture list with one immutable checker."""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import time


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=8)
    args = parser.parse_args()
    assert 1 <= args.workers <= 32
    assert not args.output.exists(), 'Preserve prior evidence; choose a new output file'
    checker = args.checker.resolve()
    identity = sha(checker)
    manifest_identity = sha(args.manifest)
    cases = json.loads(args.manifest.read_text())['cases']
    assert cases and len({case['id'] for case in cases}) == len(cases)

    def run(case):
        row = dict(case, checks=[], passed=False)
        try:
            assert sha(case['certificate']) == case['sha256']
            for repeat in (1, 2):
                start = time.monotonic()
                result = subprocess.run(
                    [str(checker), case['certificate']], capture_output=True,
                    text=True, timeout=600,
                )
                row['checks'].append(dict(
                    repeat=repeat, exit=result.returncode, stdout=result.stdout,
                    stderr=result.stderr, seconds=time.monotonic() - start,
                    accepted=result.returncode == 0 and result.stdout.strip() == 'CERTIFIED',
                ))
            assert sha(case['certificate']) == case['sha256']
            row['passed'] = all(check['accepted'] for check in row['checks'])
        except Exception as error:
            row['error'] = repr(error)
        return row

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(run, cases))
    stable = sha(checker) == identity and sha(args.manifest) == manifest_identity
    report = dict(
        checker=str(checker), checker_sha256=identity,
        manifest_sha256=manifest_identity, workers=args.workers,
        timeout_seconds=600, passes=2, identities_stable=stable,
        total=len(rows), passed=sum(row['passed'] for row in rows), cases=rows,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(report['passed'], '/', report['total'], flush=True)
    assert stable and all(row['passed'] for row in rows)


if __name__ == '__main__':
    main()
