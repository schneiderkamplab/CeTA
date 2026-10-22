#!/usr/bin/env python3
"""Verify/export an LP checker using an existing parent heap (--tocl09 for full semantics).

No parent session builds or search implementations. The warm home must contain
the matching HOL-AFP heap as well as Proof_Checker and its private dependencies.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tocl09', action='store_true', help='Export the verified infinite-tree TOCL09 bridge')
    for key in ('isabelle', 'ghc', 'warm-home', 'base-sessions', 'afp', 'out'):
        p.add_argument('--' + key, required=True, type=Path)
    a = p.parse_args()
    suffix = 'TOCL09' if a.tocl09 else 'Finite'
    check_name = 'tocl09' if a.tocl09 else 'finite'
    executable = 'ceta-lp-' + check_name
    root = Path(__file__).resolve().parents[1]
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    private = out / 'isabelle-user/.isabelle/lp_private'
    private.parent.mkdir(parents=True)
    subprocess.run(['cp', '-a', '--reflink=auto', str(a.warm_home.resolve()), str(private)], check=True)
    source = out / 'source'
    source.mkdir()
    for path in (root / 'thys/Logic_Programming').glob('*.thy'):
        shutil.copy2(path, source / path.name)
    shutil.copy2(root / ('src/Haskell/Main_LP_' + suffix + '.hs'), source)
    generated = out / 'generated'
    generated.mkdir()
    export = '''theory LP_Export
imports LP_Finite_Checker
begin
ML \\<open>
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name check_lp_finite_xml}] "Haskell" "LP_Finite_Generated" NONE [];
val _ = List.app (fn (names, content) => File.write
  (Path.append (Path.explode ''' + json.dumps(str(generated)) + ''') (Path.make names))
  (Bytes.content content)) modules;
\\<close>
end
'''
    if a.tocl09:
        export = export.replace('LP_Finite_Checker', 'LP_Constructor_XML').replace(
            'check_lp_finite_xml', 'check_lp_constructor_any_xml').replace('LP_Finite_Generated', 'LP_TOCL09_Generated')
        export = export.replace('[@{const_name check_lp_constructor_any_xml}]',
            '[@{const_name check_lp_constructor_any_xml}, @{const_name check_lp_nontermination_all_xml}]')
        export = export.replace('imports LP_Constructor_XML',
                                'imports LP_Constructor_XML LP_Source_Unify_XML')
    (source / 'LP_Export.thy').write_text(export)
    env = dict(os.environ, USER_HOME=str(out / 'isabelle-user'),
               ISABELLE_IDENTIFIER='lp_private', AFP=str(a.afp.resolve()))
    cmd = [str(a.isabelle), 'console', '-n', '-l', 'Proof_Checker',
           '-d', str(a.base_sessions.resolve()), '-o', 'threads=4', '-o', 'parallel_proofs=0']
    ml = ('((Thy_Info.use_thy_legacy ' + json.dumps(str(source / 'LP_Export')) +
          '; writeln "LP_FINITE_EXPORT_VERIFIED"; OS.Process.exit OS.Process.success) '
          'handle exn => (Runtime.exn_message exn |> writeln; OS.Process.exit OS.Process.failure));\n')
    started = time.monotonic()
    with (out / 'isabelle.log').open('w') as log:
        subprocess.run(cmd, input=ml, text=True, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=600)
    if 'LP_FINITE_EXPORT_VERIFIED' not in (out / 'isabelle.log').read_text():
        raise RuntimeError('missing verified export marker')
    theory_seconds = time.monotonic() - started
    (out / 'ghc').mkdir()
    started = time.monotonic()
    with (out / 'ghc.log').open('w') as log:
        subprocess.run([str(a.ghc), '-O1', '-i' + str(generated), '-outputdir', str(out / 'ghc'),
                        str(source / ('Main_LP_' + suffix + '.hs')), '-o', str(out / executable)],
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=1800)
    paths = list(source.glob('*')) + list(generated.glob('*.hs')) + [out / executable]
    report = dict(semantics=('leftmost resolution over possibly infinite trees, including no-occurs-check rational unification'
                            if a.tocl09 else 'finite-term leftmost resolution; not rational-tree Prolog'),
                  parent=str(a.warm_home.resolve()), theory_seconds=theory_seconds,
                  ghc_seconds=time.monotonic() - started,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                  hashes={str(f.relative_to(out)): hashlib.sha256(f.read_bytes()).hexdigest() for f in paths})
    (out / 'identity.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
