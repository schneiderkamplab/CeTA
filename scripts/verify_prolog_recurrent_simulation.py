#!/usr/bin/env python3
"""Verify shared source recurrent simulation from a checked Isabelle heap.

Run with `isabelle env`; this does not certify a benchmark root.
"""
import argparse
import json
import os
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--heap', type=Path, required=True)
parser.add_argument('--log', type=Path, required=True)
parser.add_argument('--save-heap', type=Path)
parser.add_argument('--export-directory', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
if args.save_heap:
    if args.save_heap.exists() or args.save_heap.resolve() == args.heap.resolve():
        parser.error('save heap must be fresh and distinct from the parent')
    args.save_heap.parent.mkdir(parents=True, exist_ok=True)
poly = Path(os.environ['POLYML_HOME']) / 'x86_64-linux/poly'
os.environ.setdefault('ML_HOME', str(poly.parent))
os.environ.setdefault('ML_PLATFORM', 'x86_64-linux')
load = ('fun chain p = (case PolyML.SaveState.showParent p of NONE => [] | SOME q => chain q) @ [p]; '
        'PolyML.SaveState.loadHierarchy (chain ' + json.dumps(str(args.heap.resolve())) + ');')
theories = [root / 'thys/Logic_Programming/LP_Prolog_Integer_Recurrence_XML']
if args.export_directory:
    export = args.export_directory.resolve()
    export.mkdir(parents=True, exist_ok=False)
    driver = export / 'Prolog_Integer_Recurrence_Export.thy'
    driver.write_text(
        'theory Prolog_Integer_Recurrence_Export\n imports ' + json.dumps(str(theories[0])) + ' ' +
        json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Integer_Recurrence_Code')) +
        '\nbegin\nML \\<open>\n' +
        'val (modules, _) = Code_Target.produce_code @{context} true\n' +
        '  [@{const_name check_lpp_integer_recurrence_xml}] "Haskell" "Prolog_Recurrence_Generated" NONE [];\n' +
        'val root = Path.explode ' + json.dumps(str(export)) + ';\n' +
        'val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;\n' +
        '\\<close>\nend\n')
    theories.append(driver.with_suffix(''))
resources = ('(if can Thy_Info.get_theory \"ITS_Ext.ITS4_Parser\" then () else '
    '(ignore (Thy_Info.use_theories (Options.default ()) \"ITS_Ext\" [('
    + json.dumps(str(root/'thys/ITS_Ext/Integration/ITS4_Parser'))
    + ', Position.none)]); Thy_Info.finish ()));\n')
save = '' if not args.save_heap else 'ML_Heap.save_child ' + json.dumps(str(args.save_heap.resolve())) + ';'
command = ('((' + resources + '; '.join('Thy_Info.use_thy_legacy ' + json.dumps(str(theory))
                           for theory in theories) +
           '; ' + save + ' writeln "SOURCE_RECURRENT_SIMULATION_VERIFIED"; OS.Process.exit OS.Process.success) '
           'handle exn => (writeln (Runtime.exn_message exn); OS.Process.exit OS.Process.failure));\n')
args.log.parent.mkdir(parents=True, exist_ok=True)
with args.log.open('w') as log:
    result = subprocess.run([str(poly), '-q', '--minheap', '1000', '--gcthreads', '4',
                             '--eval', load, '-i'], input=command, text=True,
                            stdout=log, stderr=subprocess.STDOUT)
if result.returncode or 'SOURCE_RECURRENT_SIMULATION_VERIFIED' not in args.log.read_text():
    raise SystemExit(1)
print('Source recurrent simulation and dependency audit passed')
