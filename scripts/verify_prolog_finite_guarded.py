#!/usr/bin/env python3
"""Check finite guarded source composition lemmas from a verified Isabelle heap.

Run with `isabelle env`. This verifies theorem dependencies, not a source root
certificate or a generated checker export. The standard session is
Prolog_Arithmetic_Bridge.
"""
import argparse
import json
import os
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--heap', type=Path, required=True)
parser.add_argument('--log', type=Path, required=True)
parser.add_argument('--export-directory', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
poly = Path(os.environ['POLYML_HOME']) / 'x86_64-linux/poly'
os.environ.setdefault('ML_HOME', str(poly.parent))
os.environ.setdefault('ML_PLATFORM', 'x86_64-linux')
load = ('fun chain p = (case PolyML.SaveState.showParent p of NONE => [] | SOME q => chain q) @ [p]; '
        'PolyML.SaveState.loadHierarchy (chain ' + json.dumps(str(args.heap.resolve())) + ');')
theories = [root / 'thys/Logic_Programming' / name for name in (
    'LP_Prolog_Finite_Guarded_Composition',
    'LP_Prolog_Finite_Numeric_Projection_Regression')]
if args.export_directory:
    export = args.export_directory.resolve()
    export.mkdir(parents=True, exist_ok=False)
    theory_file = export / 'Prolog_Finite_Guarded_Export.thy'
    theory_file.write_text(
        'theory Prolog_Finite_Guarded_Export\n imports ' + json.dumps(str(theories[0])) +
        '\nbegin\nML \\<open>\n' +
        'val (modules, _) = Code_Target.produce_code @{context} true\n' +
        '  [@{const_name check_lpp_established_finite_guarded_xml}] "Haskell" "Prolog_Guarded_Generated" NONE [];\n' +
        'val root = Path.explode ' + json.dumps(str(export)) + ';\n' +
        'val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;\n' +
        '\\<close>\nend\n')
    theories.append(theory_file.with_suffix(''))
command = ('((' + '; '.join('Thy_Info.use_thy_legacy ' + json.dumps(str(theory))
                           for theory in theories) +
           '; writeln "PROLOG_FINITE_GUARDED_VERIFIED"; OS.Process.exit OS.Process.success) '
           'handle exn => (writeln (Runtime.exn_message exn); OS.Process.exit OS.Process.failure));\n')
args.log.parent.mkdir(parents=True, exist_ok=True)
with args.log.open('w') as log:
    result = subprocess.run([str(poly), '-q', '--minheap', '1000', '--gcthreads', '4',
                             '--eval', load, '-i'], input=command, text=True,
                            stdout=log, stderr=subprocess.STDOUT)
if result.returncode or 'PROLOG_FINITE_GUARDED_VERIFIED' not in args.log.read_text():
    raise SystemExit(1)
print('Finite guarded composition and dependency audit passed')
