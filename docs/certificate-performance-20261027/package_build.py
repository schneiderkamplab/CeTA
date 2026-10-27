from pathlib import Path
import time,json,shutil,subprocess,hashlib
R=Path.cwd();O=R/'target/certificate-performance-20261027'
modules=['LP_SEG_Certificate_Generated','LP_SEG_Projected_Generated','LP_Return_Module_Generated','LP_Cut_Projected_Generated','LP_Triples_Generated','LP_Cut_NO_Generated']
while not all((O/(m+'.json')).exists() for m in modules):time.sleep(5)
for m in modules:
 d=json.loads((O/(m+'.json')).read_text());assert d['verified'],d
 if m=='LP_Cut_NO_Generated':assert d['baseline_matches_production']
merged=O/'lp-final-export';merged.mkdir(exist_ok=True)
for m in modules:
 for p in (O/'lp-performance'/m).glob('*.hs'):
  dest=merged/p.name
  if dest.exists():assert dest.read_bytes()==p.read_bytes(),p
  else:shutil.copyfile(p,dest)
subprocess.run(['python3','tools/consolidation/package_unified_export.py','--category','lp','--directory',str(merged),'--theory','thys/Certificate_Performance/Certificate_Performance.thy'],check=True)
subprocess.run(['python3','scripts/build_unified_checker.py','--output','target/unified-certificate-performance-20261027','--jobs','4'],check=True)
