#!/usr/bin/env python3
"""Inventory retained observer obligations; never authenticate source evidence.

This development audit reads the retained native extraction, verifies its pinned
table hashes, and identifies the coordinates needing actual-return proofs.
It is deliberately not a production proof search or certificate checker.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET


def audit(ferrum):
    manifest = json.loads((ferrum / 'target/observer-family-assembly/manifest.json').read_text())
    bindings = json.loads((ferrum / 'target/checkpoint-coverage-20261118/bound-return-contracts-manifest.json').read_text())
    hashes = {}
    stale_sources = []
    for entries in (manifest['sha256'], bindings['sha256']):
        for name, expected in entries.items():
            actual = hashlib.sha256((ferrum / name).read_bytes()).hexdigest()
            if actual != expected and name.startswith('src/'):
                stale_sources.append(dict(path=name, recorded=expected, current=actual))
            elif actual != expected:
                raise ValueError('stale retained evidence: ' + name)
            hashes[name] = actual
    families = {}
    for variant in ('original', 'renamed'):
        rows = {}
        directory = ferrum / 'target/observer-family-assembly' / variant
        for path in sorted(directory.glob('observer-*.xml')):
            module = int(path.stem.split('-')[1])
            root = ET.parse(path).getroot()
            if root.findtext('version') != '1':
                raise ValueError('unsupported observer plan version')
            seen = set()
            for row in root.findall('rows/row'):
                index = int(row.findtext('index'))
                roles = [child.tag for child in row if child.tag != 'index']
                if index in seen or len(roles) != 1:
                    raise ValueError('duplicate or malformed row')
                seen.add(index)
                rows.setdefault(roles[0], []).append(f'{module}:{index}')
            frontier = [int(x.text) for x in root.findall('frontier/index')]
            # Internal acquired-block rows need not belong to the frontier.
            # Semantic coverage is checked by the generated continuing checker.
            if len(frontier) != len(set(frontier)) or not set(frontier) <= seen:
                raise ValueError('malformed frontier')
        if {key: len(value) for key, value in rows.items()} != manifest['rows'][variant]:
            raise ValueError('row inventory differs from retained extraction')
        families[variant] = rows
    log = (ferrum / 'target/checkpoint-coverage-20261118/bound-return-contracts-original.log').read_text()
    pattern = (r'MODULE_FOREST_RETURN_PREMISES start=(\d+) head=(\w+) tail_before=(\w+) '
               r'tail_after=(\w+) prefix=(\d+) continuation=(\d+) obligations=([^\n]+)')
    splits = []
    for split, head, tail, output, prefix, continuation, premises in re.findall(pattern, log):
        splits.append(dict(split=int(split), head=head, tail_before=tail, tail_after=output,
                           prefix_module=int(prefix), continuation_module=int(continuation),
                           conditional_premises=premises.split(','),
                           actual_return_authenticated=False))
    if sorted(x['split'] for x in splits) != sorted(bindings['original_splits']):
        raise ValueError('missing or duplicate Split return')
    return dict(version=1, gate='OPEN', source_certified=False,
                evidence_kind='hash-validated retained extraction; not fresh source discovery',
                families=families, splits=splits, stale_sources=stale_sources,
                unresolved=[
                    'Authenticate initial/current parameter identity and copied-or-scalar returns by family induction.',
                    'Transport context groundness into Split 44, whose raw prefix ground set is empty.',
                    'Preserve restricted leaf effects on V3, including sharing, free outputs and saved alternatives.',
                    'Prove both returned continuations and every listed module boundary.',
                    'Replace the planned family all-ground invariant with the authenticated restricted invariant.'
                ], hashes=hashes)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ferrum', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.ferrum)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print('GATE OPEN: retained evidence validated; neither actual return authenticated')
