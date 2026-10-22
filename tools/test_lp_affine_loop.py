#!/usr/bin/env python3
"""Compiled checker tests for independently indexed LP source recurrences."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import xml.etree.ElementTree as ET


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ceta', type=Path, required=True)
    args = parser.parse_args()
    checker = args.ceta.resolve()
    fixture = Path(__file__).parent / 'fixtures/lp-affine-loop.xml'
    original = ET.parse(fixture).getroot()
    cases = [('positive-first', copy.deepcopy(original), True),
             ('positive-second', copy.deepcopy(original), True)]
    renamed = copy.deepcopy(original)
    names = {}
    for node in renamed.iter('name'):
        names.setdefault(node.text, 'renamed_' + str(len(names)))
        node.text = names[node.text]
    cases.append(('symbol-independent', renamed, True))
    for name, path, value in [
        ('query', 'query/name', 'wrong-query'),
        ('arity', 'query/arity', '3'),
        ('mode', 'query/ground/index', '2'),
        ('constructor', 'constructor/name', 'wrong-constructor'),
        ('zero', 'zero/name', 'wrong-zero'),
        ('first-source-clause', 'steps/step/clauseIndex', '99'),
        ('base-source-clause', 'prefixes/affineSuccess/steps/step/clauseIndex', '99'),
        ('summary-predicate', 'prefixes/affineSuccess/atomContext/funapp/name', 'wrong-helper'),
        ('initial-gap', 'environment/binding/affine/constant', '0'),
        ('helper-index', 'prefixes/affineSuccess/affine/constant', '1'),
    ]:
        tree = copy.deepcopy(original)
        tree.find(path).text = value
        cases.append((name, tree, False))
    for path in ['steps', 'prefixes', 'environment',
                 'prefixes/affineSuccess/steps']:
        tree = copy.deepcopy(original)
        tree.find(path).clear()
        cases.append(('missing-' + path, tree, False))
    for i in range(4):
        tree = copy.deepcopy(original)
        tree.find('prefixes/affineSuccess').findall('substitution')[i].clear()
        # The last two maps explicitly contain identity bindings. Their empty
        # representation is semantically identical and must remain accepted.
        cases.append(('empty-helper-substitution-' + str(i), tree, i >= 2))
        tree = copy.deepcopy(original)
        binding = tree.find('prefixes/affineSuccess').findall('substitution')[i].find('binding')
        binding.remove(list(binding)[1])
        term = ET.SubElement(binding, 'funapp')
        ET.SubElement(term, 'name').text = 'wrong_helper_transport'
        cases.append(('wrong-helper-substitution-' + str(i), tree, False))
    tree = copy.deepcopy(original)
    tree.find('prefixes/affineSuccess').findall('steps')[1].clear()
    cases.append(('missing-helper-induction', tree, False))
    for i in range(2):
        tree = copy.deepcopy(original)
        for field in tree.findall('affine')[i]:
            field.text = '0'
        cases.append(('invalid-parameter-update-' + str(i), tree, False))
    tree = copy.deepcopy(original)
    guard = ET.Element('funapp')
    ET.SubElement(guard, 'name').text = 'unproved_guard'
    tree.find('program/clause/body').insert(0, guard)
    cases.append(('cannot-skip-new-prefix', tree, False))
    results = []
    with tempfile.TemporaryDirectory(prefix='lp-affine-check-') as directory:
        for name, tree, accepted in cases:
            path = Path(directory) / (str(len(results)) + '.xml')
            ET.ElementTree(tree).write(path, encoding='unicode')
            run = subprocess.run([str(checker), str(path)], text=True,
                                 capture_output=True, timeout=30)
            actual = run.returncode == 0 and 'CERTIFIED TOCL09 LP NO' in run.stdout
            if actual != accepted or (not accepted and 'REJECTED' not in run.stdout):
                raise RuntimeError(f'{name}: {run.returncode}: {run.stdout} {run.stderr}')
            results.append({'case': name, 'accepted': actual})
    print(json.dumps({'checker': str(checker),
                      'sha256': hashlib.sha256(checker.read_bytes()).hexdigest(),
                      'fixture_sha256': hashlib.sha256(fixture.read_bytes()).hexdigest(),
                      'results': results}, indent=2))


if __name__ == '__main__':
    main()
