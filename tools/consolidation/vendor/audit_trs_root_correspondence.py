"""Independent Standard/Innermost/SRS ARI-to-CPF root correspondence audit.

No Ferrum parser or canonicalizer is used. TPDB's category directory determines
the requested strategy: its ARI TRS files do not encode innermost themselves.
Only per-rule variables and quoted identifier spellings may be normalized.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor
from functools import partial
from multiprocessing import get_context
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET

from audit_csr_root_correspondence import forms, ari_name, canonical_rule


CATEGORIES = {'TRS_Standard': 'full', 'TRS_Innermost': 'innermost', 'SRS_Standard': 'full'}


def read_ari(source):
    commands = forms(source)
    if [c for c in commands if c[0] == 'format'] != [['format', 'TRS']]:
        raise ValueError('expected exactly one TRS format declaration')
    signature, rules, used = {}, [], set()
    for command in commands:
        if command[0] == 'fun':
            if len(command) != 3:
                raise ValueError('unsupported TRS function declaration')
            name, arity = ari_name(command[1]), int(command[2])
            if name in signature or arity < 0:
                raise ValueError('duplicate symbol or negative arity')
            signature[name] = arity
        elif command[0] not in ('format', 'rule'):
            raise ValueError(f'unsupported ARI command {command[0]}')

    def term(t):
        name, args = (ari_name(t[0]), t[1:]) if isinstance(t, list) else (ari_name(t), [])
        if name not in signature:
            if isinstance(t, list):
                raise ValueError('undeclared applied symbol')
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
    return signature, rules, used


def compare(source, certificate, expected_status, category):
    expected_strategy = CATEGORIES[category]
    signature, rules, used = read_ari(source)
    def variables(t):
        return {t[1]} if t[0] == 'v' else set().union(*(variables(a) for a in t[2]))
    proper_rules = all(lhs[0] == 'f' and variables(rhs) <= variables(lhs) for lhs, rhs in rules)
    # With a non-variable lhs and no extra rhs variables, innermost's proper
    # subterm NF condition already forces every rule variable's substitution
    # to be normal. Thus the explicit nfs=true adds no restriction.
    if expected_strategy == 'innermost' and not proper_rules:
        raise ValueError('innermost nfs equivalence requires non-variable lhs and no extra variables')
    root = certificate if isinstance(certificate, ET.Element) else ET.fromstring(certificate)
    if root.tag != 'certificationProblem' or len(root.findall('input')) != 1:
        raise ValueError('not a single certification problem/input')
    inputs = root.findall('./input/*')
    if len(inputs) != 1 or inputs[0].tag != 'trsInput':
        raise ValueError('not a TRS root input')
    inp = inputs[0]
    tags = [n.tag for n in inp]
    if tags not in (['trs'], ['trs', 'strategy']):
        raise ValueError('relative/extra/duplicate root input context')
    if [n.tag for n in inp.find('trs')] != ['rules']:
        raise ValueError('unexpected root TRS context')
    strategy = inp.find('strategy')
    if expected_strategy == 'full':
        if strategy is not None:
            raise ValueError('Standard root restricts the rewrite strategy')
    else:
        if strategy is None or [n.tag for n in strategy] != ['innermost']:
            raise ValueError('Innermost root lacks the exact innermost strategy')
        inner = strategy[0]
        # Check Ferrum's explicit innermost input contract. CeTA defaults an
        # omitted nfs flag to false; do not silently identify the two contexts.
        if not (len(inner) == 1 and inner[0].tag == 'nfs'
                and inner[0].text == 'true' and len(inner[0]) == 0):
            raise ValueError('changed normal-form-substitution/Q context')
    aliases, cpf_spellings = {}, {}

    def term(node):
        if node.tag == 'var' and len(node) == 0 and node.text:
            return ('v', node.text)
        if node.tag != 'funapp' or not len(node) or node[0].tag != 'name' or len(node[0]):
            raise ValueError('non-plain CPF root term/symbol')
        raw_name = name = node[0].text
        if name not in signature and name is not None and ari_name(name) in signature:
            aliases[name] = ari_name(name)
            name = ari_name(name)
        args = [n[0] if n.tag == 'arg' and len(n) == 1 else n for n in list(node)[1:]]
        if name not in signature or len(args) != signature[name]:
            raise ValueError('CPF root symbol or arity differs')
        if cpf_spellings.setdefault(name, raw_name) != raw_name:
            raise ValueError('distinct CPF symbols collapse under spelling normalization')
        return ('f', name, tuple(term(n) for n in args))

    cpf_rules = []
    for rule in inp.findall('./trs/rules/*'):
        if rule.tag != 'rule' or len(rule) != 2:
            raise ValueError('unsupported CPF root rule')
        cpf_rules.append(canonical_rule(tuple(term(t) for t in rule)))
    if Counter(rules) != Counter(cpf_rules):
        raise ValueError('root rule multisets differ')
    for tag, expected in [('property', 'termination'), ('answer', expected_status)]:
        nodes = root.findall(tag)
        if len(nodes) != 1 or len(nodes[0]) != 1 or nodes[0][0].tag != expected or len(nodes[0][0]):
            raise ValueError(f'wrong or ambiguous {tag}')
    if expected_status not in ('yes', 'no'):
        raise ValueError('not a decided root')
    return dict(rule_multiset_equal=True, strategy_equal=True,
                strategy=expected_strategy, answer=expected_status,
                rules=len(rules), rule_symbols=len(used),
                nonvariable_lhs_and_no_extra_variables=proper_rules,
                symbol_spelling_aliases=aliases,
                unused_benchmark_declarations=sorted(signature.keys() - used))


def root_metadata(path):
    """Parse through EOF, retaining root obligations but not the proof tree.

    CeTA independently checks the full proof. Keeping its expanded XML tree
    here is unnecessary and can exhaust memory on large labeled SRS proofs.
    Duplicate root obligations and malformed trailing XML remain visible.
    """
    stack = []
    parser = ET.iterparse(path, events=('start', 'end'))
    for event, node in parser:
        if event == 'start':
            stack.append(node)
        else:
            if len(stack) >= 2 and stack[1].tag not in {'input', 'property', 'answer'}:
                node.clear()
                if len(stack) > 2:
                    stack[-2].remove(node)
            stack.pop()
    return parser.root


def file_hash(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def audit(row, ceta, checker_timeout=120):
    source = Path(row['path'])
    proof = Path(row['artifact_dir']) / 'proof.cpf.xml'
    result = dict(path=str(source), proof=str(proof), category=row['category'])
    try:
        if [p for p in source.parts if p in CATEGORIES] != [row['category']]:
            raise ValueError('benchmark directory and recorded category disagree')
        source_bytes = source.read_bytes()
        proof_digest = file_hash(proof)
        result.update(benchmark_sha256=hashlib.sha256(source_bytes).hexdigest(),
                      cpf_sha256=proof_digest)
        result.update(compare(source_bytes.decode(), root_metadata(proof), row['status'], row['category']))
        check = subprocess.run([ceta, str(proof)], capture_output=True, text=True, timeout=checker_timeout)
        result['checker_certified'] = check.returncode == 0 and 'CERTIFIED' in check.stdout.splitlines()
        result['artifacts_unchanged'] = source.read_bytes() == source_bytes and file_hash(proof) == proof_digest
        result['passed'] = result['checker_certified'] and result['artifacts_unchanged']
        if not result['checker_certified']:
            result['checker_error'] = (check.stdout + check.stderr)[-4000:]
    except (ValueError, OSError, ET.ParseError, subprocess.TimeoutExpired) as error:
        result.update(passed=False, error=str(error))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--details', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--ceta', required=True)
    parser.add_argument('--jobs', type=int, default=16)
    parser.add_argument('--processes', action='store_true',
                        help='Use isolated workers for CPU-bound streaming XML parsing')
    parser.add_argument('--checker-timeout', type=float, default=120)
    parser.add_argument('--expected-standard', type=int, required=True)
    parser.add_argument('--expected-innermost', type=int, required=True)
    parser.add_argument('--expected-srs', type=int, default=0)
    parser.add_argument('--certified-only', action='store_true')
    args = parser.parse_args()
    if not 0 < args.checker_timeout < float('inf'):
        parser.error('--checker-timeout must be finite and positive')
    rows = [r for r in json.loads(args.details.read_text()) if r['category'] in CATEGORIES
            and (not args.certified_only or r.get('certified'))]
    if len({r['path'] for r in rows}) != len(rows):
        raise ValueError('duplicate benchmark paths')
    expected = {k: v for k, v in {'TRS_Standard': args.expected_standard,
                'TRS_Innermost': args.expected_innermost, 'SRS_Standard': args.expected_srs}.items() if v}
    if Counter(r['category'] for r in rows) != expected:
        raise ValueError('category counts do not match the required audit scope')
    checker_hash = hashlib.sha256(Path(args.ceta).read_bytes()).hexdigest()
    with args.output.open('x') as output:
        executor = (ProcessPoolExecutor(max_workers=args.jobs, mp_context=get_context('spawn'))
                    if args.processes else ThreadPoolExecutor(max_workers=args.jobs))
        with executor as pool:
            results = list(pool.map(partial(audit, ceta=args.ceta, checker_timeout=args.checker_timeout), rows))
        report = dict(roots=len(results), passed=sum(r['passed'] for r in results),
                      categories=dict(Counter(r['category'] for r in results if r['passed'])),
                      ceta_sha256=checker_hash, worker_mode='processes' if args.processes else 'threads',
                      checker_unchanged=checker_hash == hashlib.sha256(Path(args.ceta).read_bytes()).hexdigest(),
                      results=results)
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}))
    print(json.dumps({'failures': [r for r in results if not r['passed']]}))
    raise SystemExit(0 if report['checker_unchanged'] and all(r['passed'] for r in results) else 1)


if __name__ == '__main__':
    main()
