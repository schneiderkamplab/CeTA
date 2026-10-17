#!/usr/bin/env python3
"""Export a draft proof-only series without checking out or changing any branch.

Uses a private index, creates unreferenced commit objects, and verifies the exact
result by applying the emitted patches to the pinned prerequisite tree. This is
an apply check, not a build of the series against upstream CeTA 3.9.
"""
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / 'docs/consolidation/upstream-proof-series'
BASE = '85b6876'
RETIREMENT = '7e9ac72'
PREFIX = 'thys/CSR_Checker/'
GROUPS = [
    ('Specialize finite conservative coverage', RETIREMENT,
     [PREFIX + 'Extensions/CSR_Improved_CSDP_Proofs.thy']),
    ('Share guarded rank and endpoint corollaries', RETIREMENT,
     [PREFIX + 'Guarded_List_Measure_Check/CSR_Guarded_List_Measure.thy']),
    ('Share the non-strict endpoint tail argument', None,
     [PREFIX + 'Guarded_List_Measure_Check/CSR_Guarded_List_Measure.thy']),
    ('Factor usable-rule pair-set restriction', None,
     [PREFIX + 'Muterm_Ext/CSR_Muterm_Innermost_Usable_Exec.thy']),
    ('Share root and residual DP representation proofs', None,
     [PREFIX + 'Extensions/CSR_Conservative_Checker.thy',
      PREFIX + 'Guarded_List_Measure_Check/CSR_Guarded_List_Checker.thy',
      'thys/Proof_Checker/CSR_Standalone_DP_Checker.thy',
      'thys/Proof_Checker/CSR_GM_Transformation.thy']),
]


def git(*args, env=None, data=None):
    return subprocess.check_output(['git', *args], cwd=ROOT, env=env, input=data)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    base = git('rev-parse', BASE).decode().strip()
    parent = base
    records = []
    expected = {}
    with tempfile.TemporaryDirectory(prefix='proof-series-', dir=ROOT / 'target') as tmp:
        env = dict(os.environ, GIT_INDEX_FILE=tmp + '/index',
                   GIT_AUTHOR_NAME='CeTA consolidation', GIT_AUTHOR_EMAIL='consolidation@example.invalid',
                   GIT_COMMITTER_NAME='CeTA consolidation', GIT_COMMITTER_EMAIL='consolidation@example.invalid',
                   GIT_AUTHOR_DATE='2026-10-17T12:00:00+00:00',
                   GIT_COMMITTER_DATE='2026-10-17T12:00:00+00:00')
        git('read-tree', base, env=env)
        for index, (title, revision, paths) in enumerate(GROUPS, 1):
            for path in paths:
                assert 'Relative_ADP' not in path and 'Outermost' not in path
                content = git('show', revision + ':' + path) if revision else (ROOT / path).read_bytes()
                blob = git('hash-object', '-w', '--stdin', data=content).decode().strip()
                git('update-index', '--add', '--cacheinfo', '100644', blob, path, env=env)
                expected[path] = hashlib.sha256(content).hexdigest()
            tree = git('write-tree', env=env).decode().strip()
            message = title + '\n\nPreserve existing contracts and executable definitions.\n'
            commit = git('commit-tree', tree, '-p', parent, env=env, data=message.encode()).decode().strip()
            patch = git('format-patch', '--stdout', '--no-signature', '--full-index', '-1', commit)
            name = f'{index:04d}-' + title.lower().replace(' ', '-') + '.patch'
            (OUT / name).write_bytes(patch)
            records.append(dict(file=name, sha256=hashlib.sha256(patch).hexdigest(),
                                commit=commit, parent=parent, tree=tree, paths=paths))
            parent = commit
        git('read-tree', base, env=env)
        for record in records:
            patch = (OUT / record['file']).read_bytes()
            git('apply', '--cached', '--check', env=env, data=patch)
            git('apply', '--cached', env=env, data=patch)
            assert git('write-tree', env=env).decode().strip() == record['tree']
        for path, digest in expected.items():
            assert hashlib.sha256(git('show', parent + ':' + path)).hexdigest() == digest
    manifest = dict(base=base, series=records, final_tree=records[-1]['tree'],
                    final_sources=expected, exact_apply_verified=True,
                    status='Draft proof-only series against a consolidated prerequisite, not upstream-ready CeTA 3.9 patches.',
                    verification_limit='These sources are checked in the consolidated integration context; this prerequisite series has not been built independently.',
                    deferred=['relative ADP', 'outermost-RZ', 'reconstruct feature prerequisites from CeTA 3.9'])
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print('Exported and exactly apply-checked', len(records), 'draft patches against', base)


if __name__ == '__main__':
    main()
