#!/usr/bin/env python3
"""Check nested absolute RFC residuals and reject semantic mutations."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import time
import xml.etree.ElementTree as ET


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    checker = args.checker.resolve()
    original = Path(__file__).resolve().parent / 'rfc-recursive/positive.cpf.xml'
    tree = ET.parse(original)
    assert len(tree.findall('.//rfcMatchboxAbsoluteBounds')) == 2
    mutations = {}
    changed = copy.deepcopy(tree)
    changed.find('.//rfcMatchboxAbsoluteBounds/initialTerms').clear()
    mutations['missing-initial-language'] = changed
    changed = copy.deepcopy(tree)
    changed.find('.//rfcMatchboxAbsoluteBounds/trs/rules').clear()
    mutations['missing-removal'] = changed
    changed = copy.deepcopy(tree)
    changed.find('.//rfcMatchboxAbsoluteBounds/bounds/bound').text = '0'
    mutations['invalid-bound'] = changed
    changed = copy.deepcopy(tree)
    rule = changed.find('./input/trsInput/trs/rules/rule')
    rule[1].find('name').text = rule[0].findtext('name')
    mutations['changed-input-self-loop'] = changed
    jobs = [('positive', original, True), ('positive-repeat', original, True)]
    for name, mutation in mutations.items():
        path = output / (name + '.xml')
        mutation.write(path, encoding='utf-8', xml_declaration=True)
        jobs.append((name, path, False))
    rows = []
    for name, path, positive in jobs:
        start = time.monotonic()
        result = subprocess.run(
            [str(checker), '--category', 'cpf', str(path)],
            capture_output=True, text=True, timeout=300,
        )
        accepted = result.returncode == 0 and result.stdout.strip() == 'CERTIFIED'
        rows.append(dict(
            name=name, expected_acceptance=positive, accepted=accepted,
            code=result.returncode, stdout=result.stdout, stderr=result.stderr,
            seconds=time.monotonic() - start,
            artifact_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        ))
        print(name, accepted, flush=True)
    report = dict(
        checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),
        checks=rows,
        passed=all(row['expected_acceptance'] == row['accepted'] for row in rows),
    )
    (output / 'checks.json').write_text(json.dumps(report, indent=2) + '\n')
    assert report['passed']


if __name__ == '__main__':
    main()
