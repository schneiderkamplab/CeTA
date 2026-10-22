#!/usr/bin/env python3
"""Test generated LP pattern-loop checking, including source/prefix mutations."""
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
    fixture = Path(__file__).parent / 'fixtures/lp-pattern-loop.xml'
    original = ET.parse(fixture).getroot()
    cases = [('positive-first', copy.deepcopy(original), True),
             ('positive-second', copy.deepcopy(original), True)]
    for name, path, value in [
        ('wrong-query', 'query/name', 'other'),
        ('wrong-arity', 'query/arity', '3'),
        ('invalid-mode', 'query/ground/index', '2'),
        ('wrong-initial-clause', 'steps/step/clauseIndex', '99'),
        ('wrong-base-clause', 'prefixes/successPattern/steps/step/clauseIndex', '0'),
    ]:
        tree = copy.deepcopy(original)
        tree.find(path).text = value
        cases.append((name, tree, False))
    for name, path in [
        ('empty-initial-steps', 'steps'),
        ('skip-all-prefixes', 'prefixes'),
        ('empty-base-proof', 'prefixes/successPattern/steps'),
        ('empty-pumping', 'substitution'),
    ]:
        tree = copy.deepcopy(original)
        tree.find(path).clear()
        cases.append((name, tree, False))
    tree = copy.deepcopy(original)
    tree.findall('substitution')[1].clear()
    cases.append(('nonground-closing', tree, False))
    tree = copy.deepcopy(original)
    tree.find('prefixes').remove(tree.find('prefixes/successPattern'))
    cases.append(('skip-one-prefix', tree, False))
    tree = copy.deepcopy(original)
    tree.find('prefixes/successPattern').findall('steps')[1].clear()
    cases.append(('empty-induction-step', tree, False))
    tree = copy.deepcopy(original)
    guard = ET.Element('funapp')
    ET.SubElement(guard, 'name').text = 'unproved_guard'
    tree.find('program/clause/body').insert(0, guard)
    cases.append(('cannot-skip-new-prefix', tree, False))
    instance = ET.parse(Path(__file__).parent / 'fixtures/lp-success-instance.xml').getroot()
    cases.extend([('instance-first', copy.deepcopy(instance), True),
                  ('instance-second', copy.deepcopy(instance), True)])
    for i, name in enumerate(('local-pumping', 'local-closing', 'embedding',
                              'closing-transport', 'induction-target', 'base-transport')):
        tree = copy.deepcopy(instance)
        tree.find('prefixes/successInstance').findall('substitution')[i].clear()
        cases.append(('instance-missing-' + name, tree, False))
    for i in range(2):
        tree = copy.deepcopy(instance)
        tree.find('prefixes/successInstance').findall('steps')[i].clear()
        cases.append(('instance-missing-trace-' + str(i), tree, False))
    tree = copy.deepcopy(instance)
    tree.find('prefixes/successInstance/atomContext/funapp/name').text = 'wrong-helper'
    cases.append(('instance-wrong-helper', tree, False))
    results = []
    with tempfile.TemporaryDirectory(prefix='lp-pattern-check-') as directory:
        for name, tree, accepted in cases:
            path = Path(directory) / (name + '.xml')
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
