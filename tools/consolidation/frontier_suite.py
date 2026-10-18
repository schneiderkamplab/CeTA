#!/usr/bin/env python3
"""Supplemental frontier checks, deliberately separate from genuine replay coverage."""
import argparse, concurrent.futures, gzip, json, os, pathlib, xml.etree.ElementTree as ET
from replay import execute, certified, sha, write
from root_audit import compare


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['manifest', 'checker', 'output']:
        p.add_argument('--' + name, type=pathlib.Path, required=True)
    p.add_argument('--hpc-checker', type=pathlib.Path)
    p.add_argument('--jobs', type=int, default=4)
    a = p.parse_args(); base = a.manifest.resolve().parent
    out = a.output.resolve(); out.mkdir(parents=True, exist_ok=False)
    manifest = json.loads(a.manifest.read_text())
    def one(row):
        run = out / row['id']; run.mkdir()
        proof = run / 'proof.cpf.xml'
        proof.write_bytes(gzip.decompress((base / row['id'] / 'proof.cpf.xml.gz').read_bytes()))
        assert sha(proof) == row['proof_sha256']
        inp = base / row['id'] / 'input.ari'
        assert sha(inp) == row['input_sha256']
        result = dict(id=row['id'], root=row['root'], checks=[], mutations=[])
        result['audit'] = compare(inp.read_text(), proof, 'yes', row['category'])
        env = {k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')}
        for i, checker in enumerate([a.checker, a.checker] + ([a.hpc_checker] if a.hpc_checker else [])):
            prefix = run / f'check-{i}'
            c = execute([str(checker.resolve()), str(proof)], run,
                        env | {'HPCTIXFILE':str(run / 'coverage.tix')}, prefix, 600)
            c['certified'] = certified(c, prefix); result['checks'].append(c)
        tree = ET.parse(proof); root = tree.getroot()
        input_node = root.find('input')
        input_file = run / 'input.xml'; ET.ElementTree(input_node).write(input_file)
        for tag in ['input', 'property', 'answer']:
            node = root.find(tag)
            if node is not None: root.remove(node)
        split_file = run / 'separate.cpf.xml'; tree.write(split_file)
        prefix = run / 'separate'
        c = execute([str(a.checker.resolve()), '--inputf', str(input_file),
                     '--property', 'SN', '--answer', 'YES', str(split_file)], run, env, prefix, 600)
        c['certified'] = certified(c, prefix); result['separate_input'] = c
        tree = ET.parse(proof); tree.getroot().find('proof')[0].tag = 'unknownFrontierProof'
        unknown = run / 'unknown.xml'; tree.write(unknown); prefix = run / 'unknown'
        c = execute([str(a.checker.resolve()), str(unknown)], run, env, prefix, 600)
        text = prefix.with_suffix('.stdout').read_text()
        c['rejected'] = not c['timed_out'] and c['returncode'] in [1,2] and text.startswith(('UNSUPPORTED', 'REJECTED'))
        result['unknown_node'] = c
        def mutation_check(tree, name, reason, diagnostic):
            mutation = run / (name + '.xml'); tree.write(mutation)
            checks = []
            for i, checker in enumerate([a.checker] + ([a.hpc_checker] if a.hpc_checker else [])):
                prefix = run / (name + '-' + str(i))
                c = execute([str(checker.resolve()), str(mutation)], run,
                            env | {'HPCTIXFILE':str(run / 'negative.tix')}, prefix, 600)
                text = prefix.with_suffix('.stdout').read_text() + prefix.with_suffix('.stderr').read_text()
                c['semantic_rejection'] = (c['returncode'] == 1 and not c['timed_out']
                    and text.startswith('REJECTED') and diagnostic in text)
                checks.append(c)
            result['mutations'].append(dict(source_sha256=sha(proof), mutation_sha256=sha(mutation),
                condition=reason, expected_diagnostic=diagnostic, checks=checks))
        # Retain well-formed CPF while removing a required compound argument.
        for kept in ['1', '2']:
            tree = ET.parse(proof)
            node = next((n for interpretation in tree.findall('.//relativeAdpComReductionPair/interpretation')
                         if interpretation.find('type/polynomial') is not None
                         for n in interpretation.findall('interpret')
                         if n.find('adpCom2') is not None), None)
            if node is None:
                break
            for child in list(node)[2:]: node.remove(child)
            ET.SubElement(node, 'variable').text = kept
            mutation_check(tree, 'missing-compound-' + kept,
                'Strict monotonicity in compound argument ' + ('2' if kept == '1' else '1'),
                'not strict in both compound arguments')
        tree = ET.parse(proof)
        rz = tree.find('.//outermostRaffelsieperZantemaTransformation')
        if rz is not None:
            import copy
            marker = rz.find('blockSymbol'); marker.clear()
            for child in rz.find('groundConstant'): marker.append(copy.deepcopy(child))
            mutation_check(tree, 'rz-marker-collision', 'Freshness of the tree-automata marker',
                           'tree-automata marker is not fresh')
        tree = ET.parse(proof)
        split = tree.find('./proof/trsTerminationProof/split')
        if split is not None and tree.find('.//rfcMatchboxRelativeBounds') is not None:
            first = split.find('trsTerminationProof'); first.clear()
            ET.SubElement(first, 'rIsEmpty')
            mutation_check(tree, 'split-unproved-selected-rules',
                           'The nonempty selected rule component must be proved terminating',
                           'R is not empty')
        result['passed'] = result['separate_input']['certified'] and result['unknown_node']['rejected'] and all(c['certified'] for c in result['checks']) and all(
            c['semantic_rejection'] for m in result['mutations'] for c in m['checks'])
        for name in ['negative.tix']:
            (run / name).unlink(missing_ok=True)
        write(run / 'result.json', result)
        return result
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        rows = list(pool.map(one, manifest['roots']))
    report = dict(scope=manifest['scope'], checker_sha256=sha(a.checker),
                  hpc_checker_sha256=sha(a.hpc_checker) if a.hpc_checker else None,
                  manifest_sha256=sha(a.manifest), results=rows,
                  passed=all(r['passed'] for r in rows))
    write(out / 'summary.json', report)
    print(json.dumps(dict(passed=report['passed'], roots=len(rows),
                         failures=[r['root'] for r in rows if not r['passed']])))
    raise SystemExit(not report['passed'])


if __name__ == '__main__':
    main()
