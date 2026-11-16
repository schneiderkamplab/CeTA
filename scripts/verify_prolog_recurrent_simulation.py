#!/usr/bin/env python3
"""Verify shared source recurrent simulation from a checked Isabelle heap.

Run with `isabelle env`; this does not certify a benchmark root.
"""
import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--heap', type=Path, required=True)
parser.add_argument('--log', type=Path, required=True)
parser.add_argument('--save-heap', type=Path)
parser.add_argument('--export-directory', type=Path)
parser.add_argument('--export-call-rows', action='store_true',
                    help='Export the exact multi-location arithmetic call checker')
parser.add_argument('--export-partial-call-rows', action='store_true',
                    help='Export partial arithmetic calls with pending continuations')
parser.add_argument('--export-helper-call-rows', action='store_true',
                    help='Export source call rows with checked finite helper prefixes')
parser.add_argument('--export-stable-guarded', action='store_true',
                    help='Export established graph assembly with stable numeric bounds')
parser.add_argument('--export-stable-mixed', action='store_true',
                    help='Export relational graph assembly with structural and numeric SCC children')
parser.add_argument('--export-stopped-mixed', action='store_true',
                    help='Export established mixed graphs with checked stopped-answer contracts')
parser.add_argument('--extra-theory', type=Path, action='append', default=[])
args = parser.parse_args()
if sum((args.export_call_rows, args.export_partial_call_rows,
        args.export_helper_call_rows, args.export_stable_guarded, args.export_stable_mixed, args.export_stopped_mixed)) > 1:
    parser.error('select at most one export route')
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
theories.extend(p.resolve().with_suffix('') for p in args.extra_theory)
if args.export_directory:
    export = args.export_directory.resolve()
    export.mkdir(parents=True, exist_ok=False)
    driver_name = 'Prolog_Integer_Recurrence_Export_' + hashlib.sha256(str(export).encode()).hexdigest()[:12]
    driver = export / (driver_name + '.thy')
    export_theory = (root / 'thys/Logic_Programming/LP_Prolog_Integer_Call_XML'
                     if args.export_call_rows else theories[0])
    export_constant = ('check_lpp_integer_calls_xml' if args.export_call_rows
                       else 'check_lpp_integer_recurrence_xml')
    export_module = ('Prolog_Integer_Calls_Generated' if args.export_call_rows
                     else 'Prolog_Recurrence_Generated')
    if args.export_partial_call_rows:
        export_theory = root / 'thys/Logic_Programming/LP_Prolog_Partial_Integer_XML'
        export_constant = 'check_lpp_partial_integer_calls_xml'
        export_module = 'Prolog_Partial_Integer_Calls_Generated'
    if args.export_helper_call_rows:
        export_theory = root / 'thys/Logic_Programming/LP_Prolog_Helper_Call_XML'
        export_constant = 'check_lpp_helper_integer_calls_xml'
        export_module = 'Prolog_Helper_Integer_Calls_Generated'
    if args.export_stable_guarded:
        export_theory = root / 'thys/Logic_Programming/LP_Prolog_Stable_Guarded_XML'
        export_constant = 'check_lpp_established_stable_guarded_xml'
        export_module = 'Prolog_Stable_Guarded_Generated'
    if args.export_stable_mixed:
        export_theory = root / 'thys/Logic_Programming/LP_Prolog_Stable_Mixed_XML'
        export_constant = 'check_lpp_established_stable_mixed_xml'
        export_module = 'Prolog_Stable_Mixed_Generated'
    export_constants = [export_constant]
    if args.export_stopped_mixed:
        export_theory = root / 'thys/Logic_Programming/LP_Prolog_Stopped_Mixed_XML'
        export_constants = ['check_lpp_established_stable_mixed_xml',
                            'check_lpp_established_stopped_mixed_xml',
                            'check_lpp_ground_integer_no_xml',
                            'check_lpp_machine_no_xml',
                            'check_lpp_call_trace_xml',
                            'check_lpp_scalar_recurrence_xml',
                            'check_lpp_domain_recurrence_xml',
                            'check_lpp_domain_graph_xml']
        export_module = 'Prolog_Stable_Mixed_Generated'
    driver.write_text(
        'theory ' + driver_name + '\n imports ' + json.dumps(str(export_theory)) + ' ' +
        json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Integer_Recurrence_Code')) +
        ((' ' + json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Ground_Integer_NO_Code')) + ' ' + json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Binary64_NO_Code')) +
          ' ' + json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_NO_Call_Trace_XML')) +
          ' ' + json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_List_Observation_Code')) +
          ' ' + json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Domain_Graph_XML'))) if args.export_stopped_mixed else '') +
        '\nbegin\n' +
        ('code_printing constant Array \\<rightharpoonup> (Haskell) \"Array.Array\"\n' +
         'code_printing type_constructor array \\<rightharpoonup> (Haskell) \"Array.Array/ _\"\n'
         if args.export_stopped_mixed else '') +
        'ML \\<open>\n' +
        'val (modules, _) = Code_Target.produce_code @{context} true\n' +
        '  [' + ', '.join('@{const_name ' + name + '}' for name in export_constants) + '] "Haskell" "' + export_module + '" NONE [];\n' +
        'val root = Path.explode ' + json.dumps(str(export)) + ';\n' +
        'val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;\n' +
        '\\<close>\nend\n')
    theories.append(driver.with_suffix(''))
resources = ('let val names = Thy_Info.get_names (); '
 'val dirs = map (fn n => (Path.implode (Thy_Info.master_directory n), Resources.theory_qualifier n)) names; '
 'val globals = map_filter (fn n => Option.map (pair n) (Resources.global_theory n)) names; '
 'in Resources.init_session {session_positions=[], session_directories=[' +
 ','.join('(' + json.dumps(str(root/path)) + ',' + json.dumps(namespace) + ')' for namespace,path in [
 ('Draft','thys/Logic_Programming'), ('ITS_Ground','thys/ITS_Ext/Ground'), ('ITS_Arithmetic','thys/ITS_Ext/Arithmetic'),
 ('ITS_Ext','thys/ITS_Ext/Integration')]) +
 '] @ dirs, command_timings=[], load_commands=[], scala_functions=[], global_theories=globals, '
 'loaded_theories=filter Resources.loaded_theory names} end; '
 'ignore (Thy_Info.use_theories (Options.default ()) "ITS_Ext" [('
 + json.dumps(str(root/'thys/ITS_Ext/Integration/ITS4_Parser')) + ', Position.none)]); ')
save = '' if not args.save_heap else 'ML_Heap.save_child ' + json.dumps(str(args.save_heap.resolve())) + ';'
command = ('((' + resources + '; '.join('Thy_Info.use_thy_legacy ' + json.dumps(str(theory))
                           for theory in theories) +
           '; ' + save + ' writeln "SOURCE_RECURRENT_SIMULATION_VERIFIED"; OS.Process.exit OS.Process.success) '
           'handle exn => (writeln (Runtime.exn_message exn); ML_Heap.save_child ' + json.dumps(str(args.log.resolve().with_suffix('.dependencies.heap'))) + '; OS.Process.exit OS.Process.failure));\n')
args.log.parent.mkdir(parents=True, exist_ok=True)
with args.log.open('w') as log:
    result = subprocess.run([str(poly), '-q', '--minheap', '1000', '--gcthreads', '4',
                             '--eval', load, '-i'], input=command, text=True,
                            stdout=log, stderr=subprocess.STDOUT)
if result.returncode or 'SOURCE_RECURRENT_SIMULATION_VERIFIED' not in args.log.read_text():
    raise SystemExit(1)
print('Source recurrent simulation and dependency audit passed')
