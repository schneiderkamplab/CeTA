#!/usr/bin/env python3
"""Check guarded Prolog backend component lemmas from a verified Prolog heap.

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
p.add_argument('--save-failure-heap', type=Path)
p.add_argument('--export', type=Path)
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
for saved in (a.save_heap, a.save_failure_heap):
    if saved:
        if saved.exists() or saved.resolve() == a.heap.resolve():
            p.error('save heap must be a fresh path, distinct from the parent')
        saved.parent.mkdir(parents=True, exist_ok=True)
if a.save_heap and a.save_failure_heap and a.save_heap.resolve() == a.save_failure_heap.resolve():
    p.error('success and failure heaps must be distinct')
load = ('fun chain p = (case PolyML.SaveState.showParent p of NONE => [] '
        '| SOME q => chain q) @ [p]; PolyML.SaveState.loadHierarchy (chain '
        + json.dumps(str(a.heap.resolve())) + ');')
# Load the existing ITS theories under their real session qualifier, then
# freeze this verified dependency snapshot just as a normal parent heap does.
resources = ''
for session, name, relative in [
    ('ITS_Arithmetic', 'ITS_Arithmetic.IA4_Definability', 'thys/ITS_Ext/Arithmetic/IA4_Definability'),
    ('ITS_Ext', 'ITS_Ext.IA4_Parser', 'thys/ITS_Ext/Integration/IA4_Parser'),
]:
    resources += ('(if can Thy_Info.get_theory ' + json.dumps(name) + ' then () else '
        '(ignore (Thy_Info.use_theories (Options.default ()) ' + json.dumps(session)
        + ' [(' + json.dumps(str(root/relative)) + ', Position.none)]); Thy_Info.finish ()));\n')

with tempfile.TemporaryDirectory(prefix='prolog-arithmetic-bridge-') as tmp:
    theory = root/'thys/Logic_Programming/LP_Prolog_Guarded_Backends'
    if a.export:
        a.export.mkdir(parents=True, exist_ok=False)
        driver_name = 'Prolog_Backend_Export_' + __import__('uuid').uuid4().hex
        driver = Path(tmp)/(driver_name + '.thy')
        driver.write_text('theory ' + driver_name + '\n imports '+json.dumps(str(theory))+' '+json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Context_Graph_Regression'))+r'''
begin
ML \<open>
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name lpp_check_expression_bridge}, @{const_name lpp_check_numeric_guard},
   @{const_name lpp_check_path_types}, @{const_name check_lpp_success_transfer_xml},
   @{const_name lpp_integer_node_regressions}, @{const_name lpp_integer_action_regressions}, @{const_name lpp_context_node_regressions}, @{const_name lpp_context_arithmetic_regressions}, @{const_name lpp_context_graph_regressions}, @{const_name lpp_context_staged_regressions}, @{const_name check_lpp_context_table_xml}, @{const_name check_lpp_numeric_row_guard_xml}, @{const_name check_lpp_numeric_path_xml}] "Haskell" "Prolog_Transfer_Generated" NONE [];
val root = Path.explode '''+json.dumps(str(a.export.resolve()))+r''';
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
\<close>
end
''')
        theory = driver.with_suffix('')
    save = '' if not a.save_heap else 'ML_Heap.save_child '+json.dumps(str(a.save_heap.resolve()))+';'
    failure_save = '' if not a.save_failure_heap else 'ML_Heap.save_child '+json.dumps(str(a.save_failure_heap.resolve()))+';'
    command = '((' + resources + '\nThy_Info.use_thy_legacy '+json.dumps(str(theory))+''';
      writeln "PROLOG_ARITHMETIC_BRIDGE_VERIFIED"; '''+save+'''
      OS.Process.exit OS.Process.success)
      handle exn => (writeln (Runtime.exn_message exn); '''+failure_save+''' OS.Process.exit OS.Process.failure));
'''
    a.log.parent.mkdir(parents=True, exist_ok=True)
    with a.log.open('w') as log:
        result = subprocess.run([str(Path(os.environ['POLYML_HOME'])/'x86_64-linux/poly'),
            '-q', '--minheap', '1000', '--gcthreads', '4', '--eval', load, '-i'],
            input=command, text=True, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode or 'PROLOG_ARITHMETIC_BRIDGE_VERIFIED' not in a.log.read_text():
        raise SystemExit(1)
print('Guarded backend component theorems and dependency audits passed; no source verdict')
