"""Independently compare benchmark CSR rules/maps with retained CPF root inputs.

This parser does not invoke Ferrum's parser or canonicalizer. Rule variables
are alpha-normalized separately per rule; function names are not renamed.
Checker acceptance is recorded separately from input correspondence.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET


def forms(source):
    tokens = re.findall(r';[^\n]*|\|[^|]*\||[()]|[^\s();]+', source)
    tokens = [t for t in tokens if not t.startswith(';')]
    stack, result = [], []
    for token in tokens:
        if token == '(':
            stack.append([])
        elif token == ')':
            if not stack:
                raise ValueError('unbalanced ARI closing parenthesis')
            item = stack.pop()
            (stack[-1] if stack else result).append(item)
        elif not stack:
            raise ValueError('ARI token outside a command')
        else:
            stack[-1].append(token)
    if stack:
        raise ValueError('unclosed ARI command')
    return result


def ari_name(name):
    return name[1:-1] if name.startswith('|') and name.endswith('|') else name


def canonical_rule(pair):
    variables = {}
    def term(t):
        if t[0] == 'v':
            return ('v', variables.setdefault(t[1], len(variables)))
        return ('f', t[1], tuple(term(a) for a in t[2]))
    return tuple(term(t) for t in pair)


def read_ari(source):
    commands = forms(source)
    signature, rules, replacement = {}, [], {}
    if ['format', 'CSTRS'] not in commands:
        raise ValueError('expected an explicit CSTRS benchmark')
    for command in commands:
        if command[0] == 'fun':
            if len(command) not in (3, 5) or (len(command) == 5 and command[3] != ':replacement-map'):
                raise ValueError(f'unsupported function declaration: {command}')
            name, arity = ari_name(command[1]), int(command[2])
            if name in signature:
                raise ValueError('duplicate function declaration')
            # ARI's specification defaults to all positions when omitted:
            # https://project-coco.uibk.ac.at/ARI/cstrs.php
            positions = tuple(int(p) for p in command[4]) if len(command) == 5 else tuple(range(1, arity + 1))
            if positions != tuple(sorted(positions)):
                raise ValueError('unsorted benchmark replacement map')
            if len(set(positions)) != len(positions) or any(p < 1 or p > arity for p in positions):
                raise ValueError('invalid benchmark replacement map')
            signature[name], replacement[name] = arity, positions
        elif command[0] not in ('format', 'rule'):
            raise ValueError(f'unsupported ARI command: {command[0]}')
    used = set()
    def term(t):
        name, args = (ari_name(t[0]), t[1:]) if isinstance(t, list) else (ari_name(t), [])
        if name not in signature:
            if isinstance(t, list):
                raise ValueError('undeclared function')
            return ('v', name)
        if len(args) != signature[name]:
            raise ValueError('benchmark arity mismatch')
        used.add(name)
        return ('f', name, tuple(term(a) for a in args))
    for command in commands:
        if command[0] == 'rule':
            if len(command) != 3:
                raise ValueError('unsupported rule shape')
            rules.append(canonical_rule((term(command[1]), term(command[2]))))
    return signature, replacement, rules, used


def compare(source, certificate, expected_status):
    signature, replacement, benchmark_rules, used = read_ari(source)
    root = ET.fromstring(certificate)
    inputs = root.findall('./input/*')
    if len(inputs) != 1 or inputs[0].tag != 'trsInput':
        raise ValueError('root CPF does not describe a TRS input')
    inp = inputs[0]
    if {n.tag for n in inp} != {'trs', 'strategy'}:
        raise ValueError('unexpected CPF input context')
    if [n.tag for n in inp.find('strategy')] != ['contextSensitive']:
        raise ValueError('replacement-map strategy absent or altered')
    if [n.tag for n in inp.find('trs')] != ['rules']:
        raise ValueError('unexpected relative/extra rule context')
    aliases, cpf_spellings = {}, {}
    def symbol(node, auxiliary=False, marked=False):
        if auxiliary and node.tag == 'sharp' and len(node) == 1:
            return ('sharp', symbol(node[0], auxiliary=True, marked=True))
        if node.tag != 'name' or node.text is None:
            raise ValueError('non-plain symbol in benchmark root input')
        raw_name = name = node.text
        # Quoted identifiers are spelling aliases, never arbitrary renaming.
        if name not in signature and ari_name(name) in signature:
            aliases[name] = ari_name(name)
            name = ari_name(name)
        # The rule symbols and their map entries must use one consistent CPF
        # spelling. Unused marked map symbols are separate typed symbols.
        if not marked and name in used and cpf_spellings.setdefault(name, raw_name) != raw_name:
            raise ValueError('distinct CPF symbols/map entries collapse under spelling normalization')
        return name
    def term(node):
        if node.tag == 'var':
            return ('v', node.text)
        if node.tag != 'funapp' or not len(node):
            raise ValueError('unsupported CPF root term')
        name = symbol(node[0])
        args = [n[0] if n.tag == 'arg' and len(n) == 1 else n for n in list(node)[1:]]
        if name not in signature or len(args) != signature[name]:
            raise ValueError('CPF root symbol or arity differs from benchmark')
        return ('f', name, tuple(term(a) for a in args))
    cpf_rules = []
    for rule in inp.findall('./trs/rules/*'):
        if rule.tag != 'rule' or len(rule) != 2:
            raise ValueError('unsupported CPF root rule')
        cpf_rules.append(canonical_rule(tuple(term(t) for t in rule)))
    if collections.Counter(benchmark_rules) != collections.Counter(cpf_rules):
        raise ValueError('root rule multisets differ (modulo per-rule alpha renaming)')
    cpf_map, extras = {}, {}
    for entry in inp.findall('./strategy/contextSensitive/*'):
        if entry.tag != 'replacementMapEntry' or not len(entry):
            raise ValueError('unsupported replacement-map entry')
        name = symbol(entry[0], auxiliary=True)
        arity = int(entry.findtext('arity'))
        positions = tuple(sorted(int(n.text) for n in entry.findall('position')))
        if name in cpf_map or len(set(positions)) != len(positions):
            raise ValueError('duplicate replacement-map entry/position')
        if any(p < 1 or p > arity for p in positions):
            raise ValueError('invalid CPF replacement-map position')
        cpf_map[name] = (arity, positions)
        if name in used:
            if (arity, positions) != (signature[name], replacement[name]):
                raise ValueError(f'replacement map differs for {name}')
        else:
            extras[repr(name)] = (arity, positions)
    if not used <= cpf_map.keys():
        raise ValueError('replacement-map entries missing for benchmark rules')
    if [n.tag for n in root.find('property')] != ['termination']:
        raise ValueError('wrong claimed property')
    answer = [n.tag for n in root.find('answer')]
    if answer != [expected_status] or expected_status not in ('yes', 'no'):
        raise ValueError('wrong claimed polarity')
    return dict(rules=len(benchmark_rules), rule_symbols=len(used),
        unused_benchmark_declarations=sorted(signature.keys() - used),
        unused_cpf_map_entries=extras, symbol_spelling_aliases=aliases,
        rule_multiset_equal=True, replacement_map_equal_on_rule_signature=True,
        property='termination', answer=expected_status)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--details', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--ceta', required=True)
    args = parser.parse_args()
    rows = [r for r in json.loads(args.details.read_text()) if r['category'] == 'TRS_Contextsensitive']
    results = []
    for row in rows:
        proof = Path(row['artifact_dir']) / 'proof.cpf.xml'
        source = Path(row['path'])
        result = dict(path=str(source), proof=str(proof),
            benchmark_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            cpf_sha256=hashlib.sha256(proof.read_bytes()).hexdigest())
        try:
            result.update(compare(source.read_text(), proof.read_text(), row['status']))
            check = subprocess.run([args.ceta, str(proof)], capture_output=True, text=True, timeout=120)
            result['checker_certified'] = check.returncode == 0 and 'CERTIFIED' in check.stdout.splitlines()
            result['passed'] = result['checker_certified']
        except (ValueError, ET.ParseError, subprocess.TimeoutExpired) as error:
            result.update(passed=False, error=str(error))
        results.append(result)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as output:
        json.dump(results, output, indent=2)
    print(json.dumps(dict(roots=len(results), passed=sum(r['passed'] for r in results),
        failures=[r for r in results if not r['passed']])))
    raise SystemExit(0 if len(results) == 110 and all(r['passed'] for r in results) else 1)


if __name__ == '__main__':
    main()
