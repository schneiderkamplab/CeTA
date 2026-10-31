#!/usr/bin/env python3
"""Check native sparse-tiling CPF artifacts and semantic mutations with one CeTA.

Preparation alone produces fixtures, never certification evidence. The checker
must support the unified category dispatch; no standalone checker fallback.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import time
import xml.etree.ElementTree as ET


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signature(node):
    return (node.tag, (node.text or '').strip(), tuple(signature(c) for c in node))


def fixtures(empty_path, residual_path):
    empty = ET.parse(empty_path).getroot()
    residual = ET.parse(residual_path).getroot()
    assert empty.find('.//sparseTiling') is not None
    assert residual.find('.//sparseTiling/tiledRules/tiledRule') is not None
    cases = [('empty-positive', True, empty), ('residual-positive', True, residual)]

    def mutate(name, base, change):
        tree = copy.deepcopy(base)
        change(tree)
        cases.append((name, False, tree))

    def remove_tiles(tree):
        tree.find('.//sparseTiling/tiles').clear()
    mutate('missing-closure-tiles', empty, remove_tiles)

    def mismatch_variable(tree):
        rule = tree.find('./input/trsInput/trs/rules/rule')
        rhs = list(rule)[1]
        variable = rhs.find('.//var') if rhs.tag != 'var' else rhs
        assert variable is not None
        variable.text = (variable.text or '') + '_different_tail'
    mutate('mismatched-source-tail', empty, mismatch_variable)

    def empty_lhs(tree):
        rule = tree.find('./input/trsInput/trs/rules/rule')
        rule.remove(list(rule)[0])
        lhs = ET.Element('var'); lhs.text = 'x'
        rule.insert(0, lhs)
    mutate('empty-source-left-side', empty, empty_lhs)

    def remove_required_rule(tree):
        rules = tree.find('.//sparseTiling/tiledRules')
        rules.remove(list(rules)[0])
    mutate('missing-tiled-rule', residual, remove_required_rule)

    def remove_used_mapping(tree):
        sparse = tree.find('.//sparseTiling')
        used = signature(sparse.find('./tiledRules/tiledRule/lhs/tile'))
        table = sparse.find('./tileEncoding')
        entry = next(e for e in table if signature(e.find('./tile')) == used)
        table.remove(entry)
    mutate('missing-used-encoding', residual, remove_used_mapping)

    def empty_child(tree):
        child = tree.find('.//sparseTiling/trsTerminationProof')
        child.clear(); ET.SubElement(child, 'rIsEmpty')
    mutate('false-empty-child', residual, empty_child)

    def erase_residual(tree):
        tree.find('.//sparseTiling/trs/rules').clear()
        empty_child(tree)
    mutate('missing-encoded-residual', residual, erase_residual)
    return cases


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--empty-certificate', type=Path, required=True)
    p.add_argument('--residual-certificate', type=Path, required=True)
    p.add_argument('--checker', type=Path)
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    if a.prepare_only == (a.checker is not None):
        p.error('select exactly one of --checker and --prepare-only')
    a.out.mkdir(parents=True, exist_ok=False)
    ET.register_namespace('xsi', 'http://www.w3.org/2001/XMLSchema-instance')
    cases = []
    for name, expected, tree in fixtures(a.empty_certificate, a.residual_certificate):
        path = a.out / (name + '.xml')
        ET.indent(tree)
        ET.ElementTree(tree).write(path, encoding='utf-8', xml_declaration=True)
        cases.append(dict(name=name, expected_acceptance=expected, path=str(path.resolve()), sha256=digest(path)))
    manifest = dict(inputs={str(path.resolve()): digest(path) for path in
                            [a.empty_certificate, a.residual_certificate]},
                    cases=cases, checked=False)
    def save():
        (a.out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    save()
    if a.prepare_only:
        print(f'Prepared {len(cases)} cases; no checker run')
        return
    checker = a.checker.resolve(); checker_hash = digest(checker)
    categories = subprocess.run([str(checker), '--list-categories'], capture_output=True,
                                text=True, timeout=30, check=True)
    required = {'cpf','cycle','conditional','conditional-erasure','lp',
                'higher-order','higher-order-delegation','its'}
    if set(categories.stdout.splitlines()) != required:
        raise RuntimeError('expected the unified checker, including ITS')
    manifest['checker_sha256'] = checker_hash
    manifest['results'] = []
    for case in cases:
        for repetition in range(2):
            assert digest(case['path']) == case['sha256']
            start = time.monotonic()
            run = subprocess.run([str(checker), '--category', 'cpf', case['path']],
                                 capture_output=True, text=True, timeout=60)
            accepted = run.returncode == 0 and any(line.strip() in {'CERTIFIED','CERTIFIED YES'}
                                                  for line in run.stdout.splitlines())
            passed = accepted if case['expected_acceptance'] else run.returncode != 0
            manifest['results'].append(dict(name=case['name'], repetition=repetition,
                returncode=run.returncode, accepted=accepted, passed=passed,
                seconds=time.monotonic()-start, stdout=run.stdout, stderr=run.stderr))
            save()
            if not passed:
                raise RuntimeError(f"unexpected checker result for {case['name']}")
    assert digest(checker) == checker_hash
    manifest['checked'] = True; save()
    print(f'Passed {2*len(cases)} checks with {checker_hash}')


if __name__ == '__main__':
    main()
