#!/usr/bin/env python3
"""Check source-bound constructor-QDP envelopes and adversarial mutations."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import xml.etree.ElementTree as ET


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ceta', type=Path, required=True)
    parser.add_argument('--proof', type=Path, required=True)
    args = parser.parse_args()
    original = ET.parse(args.proof).getroot()
    assert original.tag == 'lpConstructorQDpTerminationProof'
    assert original.findtext('normalSubstitutions') == 'true'
    cases = [('positive-first', copy.deepcopy(original), True),
             ('positive-second', copy.deepcopy(original), True)]
    renamed = copy.deepcopy(original)
    names = {}
    for node in renamed.iter('name'):
        names.setdefault(node.text, 'renamed_' + str(len(names)))
        node.text = names[node.text]
    cases.append(('consistent-renaming', renamed, True))
    for label, path, value in [
        ('invalid-context', 'normalSubstitutions', 'invalid'),
        ('wrong-arity', 'query/arity', '999'),
        ('defined-seed', 'seed/name', original.findtext('program/clause/head/funapp/name')),
    ]:
        tree = copy.deepcopy(original)
        node = tree.find(path)
        assert node is not None and value is not None, path
        node.text = value
        cases.append((label, tree, False))
    # An undefined predicate genuinely terminates by immediate failure. The
    # independent original-query audit, not this theorem, binds a benchmark.
    tree = copy.deepcopy(original)
    tree.find('query/name').text = 'not_a_source_predicate'
    cases.append(('undefined-query-terminates', tree, True))
    tree = copy.deepcopy(original)
    tree.find('query/ground').clear()
    cases.append(('missing-ground-assumption', tree, False))
    tree = copy.deepcopy(original)
    tree.find('dpProof').clear()
    cases.append(('missing-child-proof', tree, False))
    with tempfile.TemporaryDirectory(prefix='lp-constructor-context-') as directory:
        for label, tree, expected in cases:
            path = Path(directory) / (label + '.xml')
            ET.ElementTree(tree).write(path, encoding='unicode')
            result = subprocess.run([str(args.ceta.resolve()), str(path)],
                                    capture_output=True, text=True, timeout=60)
            accepted = result.returncode == 0 and 'CERTIFIED' in result.stdout
            print(json.dumps({'case': label, 'accepted': accepted, 'expected': expected}), flush=True)
            assert accepted == expected, (label, result.stdout, result.stderr)


if __name__ == '__main__':
    main()
