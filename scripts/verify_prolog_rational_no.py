#!/usr/bin/env python3
"""Verify/export source-bound rational NO certificates from a verified parent heap.

The parent may contain unchanged verified dependencies, but must not contain
the executable/export theories being checked. Changed dependencies require a
fresh parent. All output and scratch files stay below the persistent checkout.
"""
import argparse, json, os, subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--heap',type=Path,required=True)
p.add_argument('--log',type=Path,required=True)
p.add_argument('--export',type=Path,required=True)
p.add_argument('--save-heap',type=Path)
p.add_argument('--save-base-heap',type=Path,help='checkpoint the verified XML theory before code generation')
a=p.parse_args();root=Path(__file__).resolve().parents[1]
a.export=a.export.resolve();a.export.mkdir(parents=True,exist_ok=False)
if a.save_heap and a.save_heap.exists():p.error('save heap must be fresh')
driver=a.export/'Prolog_Rational_NO_Reexport.thy'
driver.write_text('theory Prolog_Rational_NO_Reexport\n imports '+json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Rational_NO_Executable'))+r'''
begin
ML \<open>
val checked = [@{thm check_lpp_rational_no_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted rational NO export dependency" else ();
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name check_lpp_rational_no_xml}] "Haskell" "Prolog_Rational_NO_Generated" NONE [];
val root = Path.explode '''+json.dumps(str(a.export))+r''';
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
\<close>
end
''')
poly=Path(os.environ['POLYML_HOME'])/'x86_64-linux/poly'
os.environ.setdefault('ML_HOME',str(poly.parent));os.environ.setdefault('ML_PLATFORM','x86_64-linux')
load='fun chain p = (case PolyML.SaveState.showParent p of NONE => [] | SOME q => chain q) @ [p]; PolyML.SaveState.loadHierarchy (chain '+json.dumps(str(a.heap.resolve()))+');'
save=('ML_Heap.save_child '+json.dumps(str(a.save_heap.resolve()))+'; ') if a.save_heap else ''
base=''
if a.save_base_heap:
 if a.save_base_heap.exists():p.error('base heap must be fresh')
 base='Thy_Info.use_thy_legacy '+json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Rational_NO_XML'))+'; ML_Heap.save_child '+json.dumps(str(a.save_base_heap.resolve()))+'; '
command='(('+base+'Thy_Info.use_thy_legacy '+json.dumps(str(driver.with_suffix('')))+'; '+save+'writeln "PROLOG_RATIONAL_NO_VERIFIED"; OS.Process.exit OS.Process.success) handle exn => (writeln (Runtime.exn_message exn); OS.Process.exit OS.Process.failure));'
a.log.parent.mkdir(parents=True,exist_ok=True)
with a.log.open('w') as log:
 result=subprocess.run([str(poly),'-q','--minheap','1000','--gcthreads','4','--eval',load,'-i'],input=command,text=True,stdout=log,stderr=subprocess.STDOUT)
if result.returncode or 'PROLOG_RATIONAL_NO_VERIFIED' not in a.log.read_text().splitlines():raise SystemExit(1)
print('Rational source NO theorem, oracle audit, and generated export verified')
