#!/usr/bin/env python3
"""Lexical compatibility/call-site audit; Isabelle supplies formal verification."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = subprocess.check_output(['git', 'rev-parse', '7e9ac72'], cwd=ROOT, text=True).strip()
PATHS = [
    'thys/CSR_Checker/Extensions/CSR_Conservative_Checker.thy',
    'thys/CSR_Checker/Guarded_List_Measure_Check/CSR_Guarded_List_Checker.thy',
    'thys/CSR_Checker/Guarded_List_Measure_Check/CSR_Guarded_List_Measure.thy',
    'thys/CSR_Checker/Muterm_Ext/CSR_Muterm_Innermost_Usable_Exec.thy',
    'thys/Proof_Checker/CSR_Standalone_DP_Checker.thy',
    'thys/Proof_Checker/CSR_GM_Transformation.thy',
]


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def statements(source):
    return dict(re.findall(
        r'^(?:lemma|theorem) (\w+):\n(.*?)(?=^proof\b|^  using\b|^  unfolding\b|^  by\b|^  apply\b)',
        source, re.M | re.S))


def executable(source):
    return re.findall(
        r'^(?:definition|fun|primrec|datatype|record)\b.*?(?=^(?:lemma|theorem|text|definition|fun|primrec|datatype|record|end)\b)',
        source, re.M | re.S)


def main():
    records = []
    for path in PATHS:
        old = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT, text=True)
        new = (ROOT / path).read_text()
        before, after = statements(old), statements(new)
        assert all(after.get(name) == statement for name, statement in before.items()), path
        assert executable(old) == executable(new), path
        assert not re.search(r'\b(?:sorry|oops|axiomatization|axioms)\b', '\n'.join(
            line[1:] for line in subprocess.check_output(
                ['git', 'diff', BASE, '--', path], cwd=ROOT, text=True).splitlines()
            if line.startswith('+') and not line.startswith('+++'))), path
        records.append(dict(path=path, sha256=sha(new), unchanged_existing_theorems=len(before),
                            new_theorems=sorted(after.keys() - before.keys()),
                            executable_declarations_unchanged=True))
    context_sites = []
    for path in PATHS:
        for line, text in enumerate((ROOT / path).read_text().splitlines(), 1):
            if 'plain_csr_dpp_mk_context[' in text:
                context_sites.append(dict(path=path, line=line, text=text.strip()))
    assert len(context_sites) == 9
    # Both routes must retain their existing calls to the same processor engine.
    routes = [
        ('nonminimal CSR', 'check_csr_dp_termination_proof_core',
         'thys/CSR_Checker/Core/CSR_Checker.thy', PATHS[4],
         'finite_csr_dpp; standalone rejects processors requiring minimality'),
        ('minimal improved CSR', 'check_guarded_improved_csr_dp_proof',
         PATHS[1], PATHS[4],
         'finite_min_csr_dpp; root additionally checks construction coverage'),
        ('typed innermost MU-TERM', 'check_muterm_i4_root_proof',
         PATHS[5], PATHS[4],
         'finite_muterm_i4_good_typed_dpp; preserve exact unhiding, map, signature and minimality guards'),
    ]
    engines = []
    for problem, engine, root, residual, contract in routes:
        for path in [root, residual]:
            assert engine in (ROOT / path).read_text(), (path, engine)
        engines.append(dict(problem=problem, shared_engine=engine,
                            shared_soundness=engine + '_sound', root_path=root,
                            residual_path=residual, contract=contract))
    result = dict(base=BASE, sources=records, representation_call_sites=context_sites,
                  shared_engines=engines, deferred=['relative ADP', 'outermost-RZ'],
                  scope='Lexical audit of the listed CSR/MU-TERM routes; not an exhaustive equivalence proof for all problem types.',
                  runtime_coverage_is_not_theorem_coverage=True)
    out = ROOT / 'docs/consolidation/shared-checking-audit.json'
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('Preserved', sum(r['unchanged_existing_theorems'] for r in records),
          'theorem interfaces; 9 representation sites share one lemma; executable declarations unchanged.')


if __name__ == '__main__':
    main()
