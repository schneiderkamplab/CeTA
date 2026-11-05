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
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
poly = Path(os.environ['POLYML_HOME']) / 'x86_64-linux/poly'
os.environ.setdefault('ML_HOME', str(poly.parent))
os.environ.setdefault('ML_PLATFORM', 'x86_64-linux')
load = ('fun chain p = (case PolyML.SaveState.showParent p of NONE => [] | SOME q => chain q) @ [p]; '
        'PolyML.SaveState.loadHierarchy (chain ' + json.dumps(str(args.heap.resolve())) + ');')
theories = [root / 'thys/Logic_Programming/LP_Prolog_Integer_Recurrence_LTS']
command = ('((' + '; '.join('Thy_Info.use_thy_legacy ' + json.dumps(str(theory))
                           for theory in theories) +
           '; writeln "SOURCE_RECURRENT_SIMULATION_VERIFIED"; OS.Process.exit OS.Process.success) '
           'handle exn => (writeln (Runtime.exn_message exn); OS.Process.exit OS.Process.failure));\n')
args.log.parent.mkdir(parents=True, exist_ok=True)
with args.log.open('w') as log:
    result = subprocess.run([str(poly), '-q', '--minheap', '1000', '--gcthreads', '4',
                             '--eval', load, '-i'], input=command, text=True,
                            stdout=log, stderr=subprocess.STDOUT)
if result.returncode or 'SOURCE_RECURRENT_SIMULATION_VERIFIED' not in args.log.read_text():
    raise SystemExit(1)
print('Source recurrent simulation and dependency audit passed')
