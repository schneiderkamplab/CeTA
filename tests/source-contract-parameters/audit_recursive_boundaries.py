#!/usr/bin/env python3
"""Extract retained boundary maps for local tests, not production proof search."""
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET

ceta = Path(__file__).resolve().parents[2]
ferrum = ceta.parent / 'ferrum-prolog-release'
out = ceta / 'target/source-recursive-entry-link'
out.mkdir(parents=True, exist_ok=True)
manifest = json.loads((ferrum / 'target/checkpoint-coverage-20261118/bound-return-contracts-manifest.json').read_text())
entry = json.loads((ceta / 'docs/data/source-recursive-entry-20261119.json').read_text())
for variant in ('original', 'renamed'):
    log_path = f'target/checkpoint-coverage-20261118/bound-return-contracts-{variant}.log'
    data = (ferrum / log_path).read_bytes()
    assert hashlib.sha256(data).hexdigest() == manifest['sha256'][log_path]
    for item in entry['variants'][variant]['tables']:
        assert hashlib.sha256(Path(item['path']).read_bytes()).hexdigest() == item['sha256']
    directory = ferrum / 'target/source-contract-development' / variant
    fixtures = []
    audit = []
    for module, row, target in ((0, 27, 30), (35, 7, 44)):
        matches = re.findall(rf'^BOUNDARY from={module} local={row} target=(\d+) bindings=\{{(.*?)\}} state_ground=(.*?) ground_context=(.*?)$', data.decode(), re.M)
        assert len(matches) == 1
        actual_target, raw, ground, context = matches[0]
        assert int(actual_target) == target
        pairs = re.findall(r'Variable\("([^"]+)"\): Var\(Variable\("([^"]+)"\)\)', raw)
        assert ', '.join(f'Variable("{a}"): Var(Variable("{b}"))' for a, b in pairs) == raw
        assert len(pairs) == 5 and len({a for a, _ in pairs}) == 5
        states = ET.parse(directory / f'states-{module}.xml').getroot()
        goals = states.find('nodes')[row].findall('state/goals/atom/funapp')
        assert len(goals) == 2
        args = [[v.text for v in goal.findall('var')] for goal in goals]
        assert all(len(xs) == 3 for xs in args) and args[0][2] == args[1][1]
        roles = args[0] + [args[1][0], args[1][2]]
        assert len(set(roles)) == 5 and {a for a, _ in pairs} == set(roles)
        assert ET.parse(directory / f'actions-{module}.xml').getroot()[row].tag == 'absent'
        plan = ET.parse(directory / f'observer-{module}.xml').getroot()
        rows = [r for r in plan.find('rows') if r.findtext('index') == str(row)]
        assert len(rows) == 1 and rows[0].find('boundary') is not None
        label = f'{module}:{row}->{target}'
        fixtures.append('|'.join([label, ','.join(roles), ','.join(roles), ','.join(f'{a}:{b}' for a, b in pairs)]))
        audit.append(dict(edge=label, source_roles=roles, target_roles=roles,
                          bindings=pairs, raw_ground=ground, context_ground=context,
                          coordinate_only=True, checked_boundary_link=False))
    (out / f'{variant}.fixtures').write_text('\n'.join(fixtures) + '\n')
    (out / f'{variant}.audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    print(f'{variant}: two retained boundary maps audited; link and return premises remain open')
