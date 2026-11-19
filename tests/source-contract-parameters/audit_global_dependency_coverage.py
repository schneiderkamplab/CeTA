"""Audit complete dependency triples, preserving order inside every prefix."""
from pathlib import Path
import contextlib
import copy
import hashlib
import io
import json
import runpy
import xml.etree.ElementTree as ET


def key(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def extracted(subject):
    return [dict(head=c['head'], prefix=c['body'][:i], call=b)
            for c in subject['success_program'] for i, b in enumerate(c['body'])]


def complete(subject):
    return set(map(key, extracted(subject))) == set(map(key, subject['triples']))


def main():
    with contextlib.redirect_stdout(io.StringIO()):
        base = runpy.run_path(str(Path(__file__).with_name('audit_global_boundary_projection.py')))
    records = []
    for variant, certificate, digest in base['cases']:
        assert hashlib.sha256(certificate.read_bytes()).hexdigest() == digest
        path = certificate.with_name('child-subject.json')
        subject = json.loads(path.read_text())
        assert complete(subject)
        triples = extracted(subject)
        assert len(triples) == len(subject['triples']) == 104
        assert len(set(map(key, triples))) == 104
        tree = ET.parse(certificate).getroot()
        assert int(tree.findtext('query/arity')) == 6
        positions = [int(e.text) for e in tree.findall('query/ground/index')]
        assert positions == [3, 4, 5]
        # Order of triples is irrelevant; order inside a successful prefix is not.
        reordered = copy.deepcopy(subject)
        reordered['triples'].reverse()
        assert complete(reordered)
        duplicated = copy.deepcopy(subject)
        duplicated['triples'].append(copy.deepcopy(duplicated['triples'][0]))
        assert complete(duplicated)
        duplicated['triples'].pop()
        assert complete(duplicated)
        mutations = {}
        for kind in ['missing_call', 'missing_prefix', 'reordered_prefix', 'wrong_head']:
            bad = copy.deepcopy(subject)
            if kind == 'missing_call':
                bad['triples'].pop()
            elif kind == 'missing_prefix':
                next(t for t in bad['triples'] if t['prefix'])['prefix'].pop()
            elif kind == 'reordered_prefix':
                next(t for t in bad['triples'] if len(t['prefix']) > 1)['prefix'].reverse()
            else:
                bad['triples'][0]['head']['symbol'] += '_forged'
            assert not complete(bad), kind
            mutations[kind] = True
        records.append(dict(variant=variant, clauses=len(subject['success_program']),
            required_calls=len(triples), exact_dependency_triple_sets=True,
            exact_triple_list_order=(triples == subject['triples']),
            query_arity=6, ground_coordinates=positions,
            reordered_triples_positive=True, unused_duplicate_removal_positive=True,
            rejected_mutations=mutations, certificate_sha256=digest,
            subject_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    print(json.dumps(dict(scope='Executable extraction coverage audit, not kernel certificate instantiation or fresh production replay', records=records), indent=2))


if __name__ == '__main__':
    main()
