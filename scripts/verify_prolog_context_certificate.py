#!/usr/bin/env python3
"""Replay Prolog source theorems from an existing verified Isabelle heap.

Run through `isabelle env`; the heap is read-only. No proof admissions or
modifications of generated checker code are used. Standard session alternative:
isabelle build -d thys -d thys/Logic_Programming Prolog_Arithmetic_Bridge
"""
import argparse,json,os,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--heap',type=Path,required=True)
p.add_argument('--log',type=Path,required=True)
p.add_argument('--export',type=Path,help='also regenerate the Haskell export into a new directory')
p.add_argument('--save-heap',type=Path,help='save a fresh verified child heap for subsequent replay')
a=p.parse_args()
if a.save_heap:
 a.save_heap=a.save_heap.resolve()
 if a.save_heap.exists():p.error('save-heap must name a fresh artifact')
 a.save_heap.parent.mkdir(parents=True,exist_ok=True)
root=Path(__file__).resolve().parents[1]
poly=Path(os.environ['POLYML_HOME'])/'x86_64-linux/poly'
os.environ.setdefault('ML_HOME',str(poly.parent))
os.environ.setdefault('ML_PLATFORM','x86_64-linux')
code='fun chain p = (case PolyML.SaveState.showParent p of NONE => [] | SOME q => chain q) @ [p]; PolyML.SaveState.loadHierarchy (chain '+json.dumps(str(a.heap.resolve()))+');'
theory=str(root/'thys/Logic_Programming/LP_Prolog_Triple_XML')
temporary=None
if a.export:
 a.export.mkdir(parents=True,exist_ok=False)
 temporary=tempfile.TemporaryDirectory(prefix='prolog-static-export-')
 driver=Path(temporary.name)/'Prolog_Context_Reexport.thy'
 driver.write_text('theory Prolog_Context_Reexport\n imports '+json.dumps(theory)+' '+json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Context_Certificate'))+' '+json.dumps(str(root/'thys/Logic_Programming/LP_Prolog_Context_Composed_Certificate'))+r'''
begin
ML \<open>
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name check_lpp_context_certificate_xml}, @{const_name check_lpp_context_composed_certificate_xml},
   @{const_name check_lpp_established_triples_xml}, @{const_name lpp_established_triples_diagnostics_xml}] "Haskell" "Prolog_Context_Generated" NONE [];
val root = Path.explode '''+json.dumps(str(a.export.resolve()))+r''';
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
\<close>
end
''')
 theory=str(driver.with_suffix(''))
save=('ML_Heap.save_child '+json.dumps(str(a.save_heap))+'; ') if a.save_heap else ''
command='((Thy_Info.use_thy_legacy '+json.dumps(theory)+'; '+save+'writeln "PROLOG_STATIC_VERIFIED"; OS.Process.exit OS.Process.success) handle exn => (writeln (Runtime.exn_message exn); OS.Process.exit OS.Process.failure));\n'
a.log.parent.mkdir(parents=True,exist_ok=True)
with a.log.open('w') as log:
 r=subprocess.run([str(poly),'-q','--minheap','1000','--gcthreads','4','--eval',code,'-i'],input=command,text=True,stdout=log,stderr=subprocess.STDOUT)
if r.returncode or 'PROLOG_STATIC_VERIFIED' not in a.log.read_text():raise SystemExit(1)
print('Prolog source theorem and dependency audit passed')

if temporary: temporary.cleanup()
