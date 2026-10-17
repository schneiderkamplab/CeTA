#!/usr/bin/env python3
"""Account for every failed root using separately verified recovery evidence."""
import argparse, json, pathlib
from replay import CORPUS, sha, write


def read_stage(name):
    if pathlib.Path(name).name != name or name in {'.', '..'}:
        raise ValueError('Stage must be a single directory name')
    path = CORPUS / name
    metadata = json.loads((path / 'metadata.json').read_text())
    summary = json.loads((path / 'summary.json').read_text())
    records = [json.loads(s) for s in (path / 'results.jsonl').read_text().splitlines()]
    expected = {(r['root'], r['answer']) for r in metadata['roots']}
    if len(records) != len(expected) or {(r['root'], r['expected_answer']) for r in records} != expected:
        raise ValueError('Incomplete root accounting in ' + name)
    return path, metadata, summary, records


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source', required=True)
    p.add_argument('--recoveries', nargs='+', required=True)
    p.add_argument('--stage', required=True)
    a = p.parse_args()
    if pathlib.Path(a.stage).name != a.stage or a.stage in {'.', '..'}:
        p.error('Stage must be a single directory name')
    source, metadata, summary, records = read_stage(a.source)
    failed = {r['root']: r for r in records if not r['eligible']}
    if not failed:
        raise ValueError('No failed roots to reconcile')
    chosen = {r['root']: (source, r, metadata) for r in records if r['eligible']}
    receipts = [dict(stage=a.source, metadata_sha256=sha(source / 'metadata.json'), summary_sha256=sha(source / 'summary.json'))]
    recovered = set()
    for name in a.recoveries:
        path, meta, report, rows = read_stage(name)
        if report['losses'] or not all(r['eligible'] for r in rows):
            raise ValueError('Recovery still has failed gates: ' + name)
        for key in ['ferrum_sha256', 'checker_sha256', 'hpc_sha256', 'oracle_sha256', 'source_revision', 'hpc_source_revision']:
            if metadata[key] != meta[key]:
                raise ValueError('Recovery changed pinned identity: ' + key)
        left, right = metadata['profile'].copy(), meta['profile'].copy()
        left.pop('FERRUM_ORACLE_TIME_SCALE_PERCENT', None)
        right.pop('FERRUM_ORACLE_TIME_SCALE_PERCENT', None)
        if left != right:
            raise ValueError('Recovery changed non-budget replay settings')
        for row in rows:
            root = row['root']
            if root not in failed or root in recovered:
                raise ValueError('Unexpected or duplicate recovery root: ' + root)
            if row['expected_answer'] != failed[root]['expected_answer']:
                raise ValueError('Recovery changed expected outcome')
            if row['id'] != failed[root]['id']:
                raise ValueError('Recovery changed root identity')
            recovered.add(root)
            chosen[root] = (path, row, meta)
        receipts.append(dict(stage=name, metadata_sha256=sha(path / 'metadata.json'), summary_sha256=sha(path / 'summary.json')))
    if recovered != failed.keys():
        raise ValueError('Unresolved failed roots: ' + str(sorted(failed.keys() - recovered)))
    dest = CORPUS / a.stage
    dest.mkdir(exist_ok=False)
    final_records, final_roots = [], []
    original = {r['root']: r for r in metadata['roots']}
    for root, (path, row, meta) in sorted(chosen.items()):
        # Input hashes are checked even when an earlier replay failed before
        # reaching its independent original-input audit.
        if row['input_sha256'] != original[root]['input_sha256']:
            raise ValueError('Recovery changed frozen input')
        scale = int(row.get('oracle_time_scale_percent', meta['profile']['FERRUM_ORACLE_TIME_SCALE_PERCENT']))
        final_records.append(row | dict(oracle_time_scale_percent=scale, evidence_stage=path.name))
        final_roots.append(original[root] | dict(oracle_time_scale_percent=scale))
        (dest / row['id']).symlink_to(path / row['id'], target_is_directory=True)
    write(dest / 'metadata.json', metadata | dict(roots=final_roots, source_stages=receipts,
          scope='Every original root retained; original failed attempts remain in source stages. Per-root calibrated search budgets are explicit.'))
    (dest / 'results.jsonl').write_text(''.join(json.dumps(r, sort_keys=True) + '\n' for r in final_records))
    result = dict(roots=len(final_records), eligible=len(final_records), losses=[], recovered_roots=sorted(recovered),
                  prior_failures_preserved=True, source_stages=receipts)
    write(dest / 'summary.json', result)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
