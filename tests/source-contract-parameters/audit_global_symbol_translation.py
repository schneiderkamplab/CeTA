"""Exact retained JSON/XML correspondence; not source simulation or proof search."""
from pathlib import Path
import contextlib
import copy
import hashlib
import io
import json
import runpy
import xml.etree.ElementTree as ET


def symbol(role, name, arity):
    return f'lp_{role}_{name.encode("utf-8").hex()}_{arity}'


def translated(term, role='c'):
    if term['kind'] == 'variable':
        return ('variable', term['name'])
    assert term['kind'] == 'application'
    return ('application', symbol(role, term['symbol'], len(term['args'])),
            tuple(translated(t) for t in term['args']))


def parsed(term):
    if term.tag == 'var':
        assert not list(term)
        return ('variable', term.text)
    assert term.tag == 'funapp'
    children = list(term)
    assert children and children[0].tag == 'name'
    return ('application', children[0].text, tuple(map(parsed, children[1:])))


def atoms(container):
    assert container is not None
    return tuple(parsed(t) for t in container)


def verify(subject, certificate):
    program, triples = certificate.find('program'), certificate.find('triples')
    assert program is not None and triples is not None
    assert len(program) == len(subject['success_program'])
    assert len(triples) == len(subject['triples'])
    for source, clause in zip(subject['success_program'], program):
        assert clause.tag == 'clause'
        assert atoms(clause.find('head')) == (translated(source['head'], 'in'),)
        assert atoms(clause.find('body')) == tuple(translated(t, 'in') for t in source['body'])
    for source, triple in zip(subject['triples'], triples):
        assert triple.tag == 'triple'
        assert atoms(triple.find('head')) == (translated(source['head'], 'in'),)
        assert atoms(triple.find('prefix')) == tuple(translated(t, 'in') for t in source['prefix'])
        assert atoms(triple.find('call')) == (translated(source['call'], 'in'),)


def rejected(subject, tree):
    try:
        verify(subject, tree)
    except AssertionError:
        return True
    return False


def main():
    with contextlib.redirect_stdout(io.StringIO()):
        base = runpy.run_path(str(Path(__file__).with_name('audit_global_boundary_projection.py')))
    records = []
    for variant, path, expected_hash in base['cases']:
        subject_path = path.with_name('child-subject.json')
        subject = json.loads(subject_path.read_text())
        tree = ET.parse(path).getroot()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected_hash
        verify(subject, tree)
        assert (len(subject['success_program']), len(subject['triples'])) == (117, 104)
        mutations = {}
        def damage(label, edit):
            changed = copy.deepcopy(tree)
            edit(changed)
            assert rejected(subject, changed), label
            mutations[label] = True
        damage('predicate_role', lambda t: setattr(t.find('program/clause/head/funapp/name'), 'text', 'lp_c_wrong_6'))
        damage('data_symbol', lambda t: setattr(t.find('program/clause/head/funapp/funapp/name'), 'text', 'forged_data'))
        damage('variable_sharing', lambda t: setattr(t.find('program/clause/head/funapp/var'), 'text', 'forged_variable'))
        damage('missing_clause', lambda t: t.find('program').remove(t.find('program')[0]))
        damage('missing_triple', lambda t: t.find('triples').remove(t.find('triples')[0]))
        def reorder_clauses(t):
            program = t.find('program')
            program[:2] = list(reversed(list(program)[:2]))
        damage('clause_order', reorder_clauses)
        def wrong_arity(t):
            name = t.find('program/clause/head/funapp/name')
            name.text = name.text.rsplit('_', 1)[0] + '_999'
        damage('encoded_arity', wrong_arity)
        def prefix_edit(t, reverse=False):
            prefix = next(p for p in t.findall('triples/triple/prefix') if len(p) >= (2 if reverse else 1))
            if reverse:
                prefix[:] = list(reversed(list(prefix)))
            else:
                prefix.remove(prefix[0])
        damage('missing_successful_prefix', prefix_edit)
        damage('reordered_successful_prefix', lambda t: prefix_edit(t, True))
        # Whitespace serialization changes are irrelevant to exact term identity.
        ET.indent(tree)
        verify(subject, ET.fromstring(ET.tostring(tree)))
        records.append(dict(variant=variant, clauses=117, triples=104,
            nonempty_prefixes=sum(bool(t['prefix']) for t in subject['triples']),
            rejected_mutations=mutations, whitespace_positive=True,
            certificate=str(path), certificate_sha256=expected_hash,
            subject=str(subject_path), subject_sha256=hashlib.sha256(subject_path.read_bytes()).hexdigest()))
    print(json.dumps(dict(scope='Ordered full JSON-to-XML role/arity/data translation only; native source encoding and semantic simulation remain open', records=records), indent=2))


if __name__ == '__main__':
    main()
