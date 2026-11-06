#!/usr/bin/env python3
"""Check a native mixed certificate and mutations of its return obligations."""
import argparse
import copy
import hashlib
import json
import subprocess
import xml.etree.ElementTree as E
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
for key in ('source', 'checker', 'output'):
    p.add_argument('--' + key, type=Path, required=True)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
root = E.parse(a.source).getroot()
assert root.tag == 'prologEstablishedStableSEGMixedProof'
assert root.find('components/relationalGroundSplit') is not None
cases = {'positive': root}
paths = {
    'missing-return-model': 'components/relationalGroundSplit/sourceGroundReturn/sourceFiniteReturnModel/predicates',
    'missing-ground-modes': 'components/relationalGroundSplit/sourceGroundReturn/groundModes',
    'missing-ground-return': 'components/relationalGroundSplit/sourceGroundReturn/ground',
    'missing-returned-call': 'components/relationalGroundSplit/returnedCall',
    'missing-second-interface': 'components/relationalGroundSplit/tripleSplit/secondInput',
    'missing-first-descent': 'components/relationalGroundSplit/firstCall',
    'missing-second-descent': 'components/relationalGroundSplit/secondCall',
    'missing-routing': 'routing',
    'missing-backends': 'backends',
}
for name, path in paths.items():
    changed = copy.deepcopy(root)
    node = changed.find(path)
    assert node is not None and len(node), (name, path)
    node.clear()
    cases[name] = changed
changed = copy.deepcopy(root)
removed = 0
for program in changed.iter('successProgram'):
    for clause in list(program):
        if clause.findtext('head/atom/predicate') == '1:\\+':
            program.remove(clause)
            removed += 1
assert removed, 'This control requires an explicit negation success clause'
cases['missing-probe-success-coverage'] = changed
checker = a.checker.resolve()
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
checker_hash = sha(checker)
results = []
for name, tree in cases.items():
    artifact = a.output / (name + '.xml')
    E.ElementTree(tree).write(artifact, encoding='unicode')
    for repeat in range(2):
        run = subprocess.run([str(checker), '--category', 'prolog', str(artifact.resolve())],
                             capture_output=True, text=True, timeout=60)
        (a.output / f'{name}-{repeat}.log').write_text(run.stdout + run.stderr)
        accepted = run.returncode == 0 and 'CERTIFIED SOURCE-BOUND PROLOG' in run.stdout
        results.append(dict(case=name, repeat=repeat, expected=name == 'positive',
                            accepted=accepted, exit_code=run.returncode,
                            artifact_sha256=sha(artifact)))
manifest = dict(checker=str(checker), checker_sha256=checker_hash,
                source=str(a.source.resolve()), source_sha256=sha(a.source), results=results)
(a.output / 'results.json').write_text(json.dumps(manifest, indent=2) + '\n')
assert sha(checker) == checker_hash
assert all(r['accepted'] == r['expected'] for r in results), results
print(f'{len(results)} mixed return checks passed')
