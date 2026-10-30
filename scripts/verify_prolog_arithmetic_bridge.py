#!/usr/bin/env python3
"""Check arithmetic source/ITS expression lemmas from a verified Prolog heap.

This is a component proof, not a source-root verdict or a substitute checker.
Standard session: isabelle build -d thys -d thys/ITS_Ext
  -d thys/Logic_Programming Prolog_Arithmetic_Bridge
Run this focused check through `isabelle env`. The input heap is read-only.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--heap', required=True, type=Path)
p.add_argument('--log', required=True, type=Path)
p.add_argument('--save-heap', type=Path)
p.add_argument('--export', type=Path)
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
if a.save_heap:
    if a.save_heap.exists() or a.save_heap.resolve() == a.heap.resolve():
        p.error('save heap must be a fresh path, distinct from the parent')
    a.save_heap.parent.mkdir(parents=True, exist_ok=True)
load = ('fun chain p = (case PolyML.SaveState.showParent p of NONE => [] '
        '| SOME q => chain q) @ [p]; PolyML.SaveState.loadHierarchy (chain '
        + json.dumps(str(a.heap.resolve())) + ');')
# Load the existing ITS theories under their real session qualifier, then
# freeze this verified dependency snapshot just as a normal parent heap does.
resources = 'ignore (Thy_Info.use_theories (Options.default ()) "ITS_Arithmetic" [('+json.dumps(str(root/'thys/ITS_Ext/Arithmetic/IA4_Normalization'))+', Position.none)]); Thy_Info.finish ();\n'
with tempfile.TemporaryDirectory(prefix='prolog-arithmetic-bridge-') as tmp:
    theory = root/'thys/Logic_Programming/LP_Prolog_Arithmetic_ITS'
    if a.export:
        a.export.mkdir(parents=True, exist_ok=False)
        driver = Path(tmp)/'Prolog_Arithmetic_Export.thy'
        driver.write_text('theory Prolog_Arithmetic_Export\n imports '+json.dumps(str(theory))+r'''
begin
ML \<open>
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name lpp_check_expression_bridge}] "Haskell" "Prolog_Arithmetic_Generated" NONE [];
val root = Path.explode '''+json.dumps(str(a.export.resolve()))+r''';
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
\<close>
end
''')
        theory = driver.with_suffix('')
    save = '' if not a.save_heap else 'ML_Heap.save_child '+json.dumps(str(a.save_heap.resolve()))+';'
    command = resources + '\n((Thy_Info.use_thy_legacy '+json.dumps(str(theory))+''';
      writeln "PROLOG_ARITHMETIC_BRIDGE_VERIFIED"; '''+save+'''
      OS.Process.exit OS.Process.success)
      handle exn => (writeln (Runtime.exn_message exn); OS.Process.exit OS.Process.failure));
'''
    a.log.parent.mkdir(parents=True, exist_ok=True)
    with a.log.open('w') as log:
        result = subprocess.run([str(Path(os.environ['POLYML_HOME'])/'x86_64-linux/poly'),
            '-q', '--minheap', '1000', '--gcthreads', '4', '--eval', load, '-i'],
            input=command, text=True, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode or 'PROLOG_ARITHMETIC_BRIDGE_VERIFIED' not in a.log.read_text():
        raise SystemExit(1)
print('Arithmetic expression bridge and theorem dependency audit passed')
