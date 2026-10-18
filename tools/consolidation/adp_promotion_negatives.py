#!/usr/bin/env python3
"""Reject well-formed promotion mutations for independently checked side conditions."""
import argparse, copy, gzip, json, os, pathlib, xml.etree.ElementTree as ET
from replay import execute, certified, sha, write


def key(node):
    return node.tag, (node.text or '').strip(), tuple(sorted(node.attrib.items())), tuple(key(c) for c in node)


def mutate(tree, name):
    selected = tree.find('./proof/trsTerminationProof/split/trs/rules')
    strict = tree.find('./input/trsInput/trs/rules')
    if selected is None or strict is None or not len(strict):
        raise ValueError('Expected a promotion certificate with nonempty strict rules')
    original = {key(rule) for rule in tree.find('input').iter('rule')}
    if name == 'missing-strict':
        removed = key(strict[0])
        assert removed in {key(rule) for rule in selected}
        for rule in list(selected):
            if key(rule) == removed:
                selected.remove(rule)
        assert not {key(rule) for rule in strict}.issubset({key(rule) for rule in selected})
    elif name == 'foreign-rule':
        foreign = copy.deepcopy(selected[0])
        symbol = foreign.find('.//name')
        assert symbol is not None
        names = {n.text for n in tree.iter('name')}
        fresh = 'fresh_foreign_promotion_symbol'
        while fresh in names:
            fresh += '_fresh'
        symbol.text = fresh
        assert key(foreign) not in original
        selected.append(foreign)
        assert not {key(rule) for rule in selected}.issubset(original)
    else:
        raise ValueError(name)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for k in ['manifest', 'checker', 'output']:
        p.add_argument('--' + k, type=pathlib.Path, required=True)
    p.add_argument('--hpc-checker', type=pathlib.Path)
    a = p.parse_args(); manifest = a.manifest.resolve(); base = manifest.parent
    out = a.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    binaries = [a.checker.resolve()] + ([a.hpc_checker.resolve()] if a.hpc_checker else [])
    env = {k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')}
    results = []
    diagnostic = 'invalid relative promotion split'
    for row in json.loads(manifest.read_text())['roots']:
        run = out / row['id']; run.mkdir(); proof = run / 'source.xml'
        proof.write_bytes(gzip.decompress((base / row['id'] / 'proof.cpf.xml.gz').read_bytes()))
        if sha(proof) != row['proof_sha256']:
            raise ValueError('Frozen certificate changed')
        source_checks = []
        for i, binary in enumerate(binaries):
            prefix = run / ('source-' + str(i))
            result = execute([str(binary), str(proof)], run, env | {'HPCTIXFILE':str(run / 'source.tix')}, prefix, 1200)
            result['certified'] = certified(result, prefix); source_checks.append(result)
        if not all(c['certified'] for c in source_checks):
            raise ValueError('Mutation source does not certify')
        for name in ['missing-strict', 'foreign-rule']:
            tree = ET.parse(proof); mutate(tree, name)
            path = run / (name + '.xml'); tree.write(path, encoding='utf-8', xml_declaration=True)
            ET.parse(path)  # XML well-formedness is distinct from semantic rejection.
            checks = []
            for i, binary in enumerate(binaries):
                prefix = run / (name + '-' + str(i))
                result = execute([str(binary), str(path)], run, env | {'HPCTIXFILE':str(run / (name + '.tix'))}, prefix, 1200)
                output = prefix.with_suffix('.stdout').read_text() + prefix.with_suffix('.stderr').read_text()
                result['semantic_rejection'] = result['returncode'] == 1 and not result['timed_out'] and output.startswith('REJECTED') and diagnostic in output
                checks.append(result)
            results.append(dict(id=row['id'], root=row['root'], source_sha256=row['proof_sha256'], mutation_sha256=sha(path), mutation=name, side_condition_violated=True, diagnostic=diagnostic, source_checks=source_checks, checks=checks, passed=all(c['semantic_rejection'] for c in checks)))
    report = dict(manifest_sha256=sha(manifest), checker_sha256=sha(a.checker), results=results, passed=bool(results) and all(r['passed'] for r in results))
    write(out / 'summary.json', report)
    print(json.dumps(dict(cases=len(results), passed=report['passed'])))
    raise SystemExit(not report['passed'])


if __name__ == '__main__':
    main()
