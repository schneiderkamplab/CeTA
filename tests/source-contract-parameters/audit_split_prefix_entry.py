#!/usr/bin/env python3
"""Retained interface audit for development tests, never production discovery."""
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET

ceta = Path(__file__).resolve().parents[2]
ferrum = ceta.parent / 'ferrum-prolog-release'
out = ceta / 'target/source-split-prefix-entry'
out.mkdir(parents=True, exist_ok=True)
manifest = json.loads((ferrum / 'target/checkpoint-coverage-20261118/bound-return-contracts-manifest.json').read_text())
entry = json.loads((ceta / 'docs/data/source-recursive-caller-20261119.json').read_text())
for variant in ('original', 'renamed'):
    relative = f'target/checkpoint-coverage-20261118/bound-return-contracts-{variant}.log'
    raw = (ferrum / relative).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == manifest['sha256'][relative]
    for item in entry['variants'][variant]['tables']:
        assert hashlib.sha256(Path(item['path']).read_bytes()).hexdigest() == item['sha256']
    directory = ferrum / 'target/source-contract-development' / variant
    fixtures, audit = [], []
    for split, module, row in ((30, 0, 27), (44, 35, 7)):
        lines = [line for line in raw.decode().splitlines() if line.startswith(f'MODULE_SPLIT_RETURN start={split} ')]
        assert len(lines) == 1
        prefix, remaining = lines[0].split(' }, continuation: ReturnState ', 1)
        payload_text = re.search(r'answers: \[\[(.*?)\]\]', prefix).group(1)
        payload = re.findall(r'Var\(Variable\("([^"]+)"\)\)', payload_text)
        assert ', '.join(f'Var(Variable("{v}"))' for v in payload) == payload_text
        assert int(re.search(r'arity: (\d+)', prefix).group(1)) == len(payload)
        routing_text = re.search(r'routing: \{(.*?)\}, projection:', remaining).group(1)
        routes = re.findall(r'Variable\("([^"]+)"\): (\d+)', routing_text)
        assert ', '.join(f'Variable("{v}"): {i}' for v, i in routes) == routing_text
        routing = {v: int(i) for v, i in routes}
        assert len(routing) == len(routes) == len(payload)
        assert all(payload[i] == v for v, i in routing.items())
        states = ET.parse(directory / f'states-{module}.xml').getroot()
        goals = states.find('nodes')[row].findall('state/goals/atom/funapp')
        assert len(goals) == 2
        args = [[v.text for v in goal.findall('var')] for goal in goals]
        assert all(len(xs) == 3 for xs in args) and args[0][2] == args[1][1]
        roles = [args[0][2], args[1][0], args[1][2]]
        indices = [routing[v] for v in roles]
        continuation = remaining.split(' }, rest:', 1)[0]
        routed_args = re.search(r'args: \[(.*?)\]', continuation).group(1)
        assert re.findall(r'Variable\("return_(\d+)"\)', routed_args) == [str(indices[1]), str(indices[0]), str(indices[2])]
        fixtures.append('|'.join([str(split), ','.join(payload), ','.join(roles), ','.join(map(str, indices))]))
        audit.append(dict(split=split, source_boundary=f'{module}:{row}', payload=payload,
                          roles=roles, indices=indices, parameter_retained=args[0][1] in payload,
                          caller_interface_checked_only=True, helper_return_authenticated=False))
    (out / f'{variant}.fixtures').write_text('\n'.join(fixtures) + '\n')
    (out / f'{variant}.audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    print(f'{variant}: both prefix payloads and continuation routes audited')
