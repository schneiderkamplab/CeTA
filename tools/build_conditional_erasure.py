#!/usr/bin/env python3
"""Check/export the ordinary CTRS bridge using an existing verified parent heap.

No parent sessions are rebuilt. The private heap clone and console log retain
the exact check/export provenance; proof errors terminate the process.
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
    for name in ('isabelle', 'ghc', 'warm-home', 'base-sessions', 'afp', 'out'):
        p.add_argument('--' + name, type=Path, required=True)
    a = p.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    private = out / 'isabelle-user/.isabelle/ordinary_private'
    private.parent.mkdir(parents=True)
    subprocess.run(['cp', '-a', '--reflink=auto', str(a.warm_home.resolve()), str(private)], check=True)
    source = out / 'source'
    source.mkdir()
    shutil.copy2(root / 'thys/Conditional_Ordinary/Conditional_Erasure.thy', source)
    shutil.copy2(root / 'src/Haskell/Main_Conditional_Ordinary.hs', source)
    (out / 'generated').mkdir()
    (source / 'Erasure_Export.thy').write_text('''theory Erasure_Export
imports Conditional_Erasure
begin
ML \\<open>
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name check_conditional_erasure_xml}] "Haskell" "Conditional_Erasure_Generated" NONE [];
val _ = List.app (fn (names, content) => File.write
  (Path.append (Path.explode ''' + json.dumps(str(out / 'generated')) + ''') (Path.make names))
  (Bytes.content content)) modules;
\\<close>
end
''')
    env = dict(os.environ, USER_HOME=str(out / 'isabelle-user'),
               ISABELLE_IDENTIFIER=private.name, AFP=str(a.afp.resolve()))
    cmd = [str(a.isabelle), 'console', '-n', '-l', 'Proof_Checker',
           '-d', str(a.base_sessions.resolve()), '-o', 'threads=4', '-o', 'parallel_proofs=0']
    ml = ('((Thy_Info.use_thy_legacy ' + json.dumps(str(source / 'Erasure_Export')) +
          '; writeln "ORDINARY_ERASURE_EXPORT_VERIFIED"; OS.Process.exit OS.Process.success) '
          'handle exn => (Runtime.exn_message exn |> writeln; OS.Process.exit OS.Process.failure));\n')
    start = time.monotonic()
    with (out / 'isabelle.log').open('w') as log:
        subprocess.run(cmd, input=ml, text=True, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    assert 'ORDINARY_ERASURE_EXPORT_VERIFIED' in (out / 'isabelle.log').read_text()
    isabelle_seconds = time.monotonic() - start
    (out / 'ghc').mkdir()
    cmd = [str(a.ghc), '-O2', '-i' + str(out / 'generated'), '-outputdir', str(out / 'ghc'),
           str(source / 'Main_Conditional_Ordinary.hs'), '-o', str(out / 'ceta-conditional-erasure')]
    start = time.monotonic()
    with (out / 'ghc.log').open('w') as log:
        subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, check=True)
    paths = list(source.glob('*')) + list((out / 'generated').glob('*.hs')) + [out / 'ceta-conditional-erasure']
    report = dict(parent=str(a.warm_home.resolve()),
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                  isabelle_seconds=isabelle_seconds, ghc_seconds=time.monotonic() - start,
                  hashes={str(f.relative_to(out)): hashlib.sha256(f.read_bytes()).hexdigest() for f in paths})
    (out / 'identity.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
