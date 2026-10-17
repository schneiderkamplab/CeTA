#!/usr/bin/env python3
"""Join complete compatible replay stages without changing their evidence."""
import argparse, json, pathlib
from replay import CORPUS, write, sha


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--stage', required=True)
    p.add_argument('--sources', nargs='+', required=True)
    a = p.parse_args()
    for name in [a.stage] + a.sources:
        if pathlib.Path(name).name != name or name in {'.', '..'}:
            p.error('Stages must be single directory names')
    records, roots, receipts, seen = [], [], [], set()
    first = None
    directories = []
    for name in a.sources:
        src = CORPUS / name
        summary = json.loads((src / 'summary.json').read_text())
        metadata = json.loads((src / 'metadata.json').read_text())
        rows = [json.loads(s) for s in (src / 'results.jsonl').read_text().splitlines()]
        if summary['losses'] or len(rows) != len(metadata['roots']) or not all(r['eligible'] for r in rows):
            raise ValueError('Incomplete or failing source stage: ' + name)
        if {(r['root'], r['expected_answer']) for r in rows} != {(r['root'], r['answer']) for r in metadata['roots']}:
            raise ValueError('Exact root/outcome mismatch: ' + name)
        if first is None:
            first = metadata
        else:
            for key in ['ferrum_sha256', 'checker_sha256', 'hpc_sha256', 'oracle_sha256', 'source_revision', 'hpc_source_revision', 'profile']:
                if first[key] != metadata[key]:
                    raise ValueError('Incompatible evidence: ' + key)
        for row in rows:
            if row['root'] in seen:
                raise ValueError('Overlapping root sets: ' + row['root'])
            seen.add(row['root'])
            directories.append((row['id'], src / row['id']))
        records.extend(rows)
        roots.extend(metadata['roots'])
        receipts.append(dict(stage=name, metadata_sha256=sha(src / 'metadata.json'), summary_sha256=sha(src / 'summary.json')))
    dest = CORPUS / a.stage
    dest.mkdir(exist_ok=False)
    for rid, src in directories:
        (dest / rid).symlink_to(src, target_is_directory=True)
    metadata = first | dict(roots=sorted(roots, key=lambda r: r['root']), source_stages=receipts,
                            scope='Union of complete compatible frozen stages; source evidence remains unchanged.')
    # Stage-specific timing ceilings remain in the source receipts, not implied
    # to be identical merely because their checker/oracle identities match.
    for key in ['checker_ceiling_seconds', 'hpc_ceiling_seconds', 'prior_stage', 'prior_hpc_sha256', 'runner_sha256']:
        metadata.pop(key, None)
    write(dest / 'metadata.json', metadata)
    (dest / 'results.jsonl').write_text(''.join(json.dumps(r, sort_keys=True) + '\n' for r in sorted(records, key=lambda r: r['root'])))
    summary = dict(roots=len(records), eligible=len(records), losses=[], source_stages=receipts)
    write(dest / 'summary.json', summary)
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
