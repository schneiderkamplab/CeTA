from pathlib import Path
import json,subprocess,time,hashlib,gzip,shutil
R=Path.cwd();O=R/'target/usable-membership-20261026';D=R/'docs/usable-membership-20261026';B=R/'target/unified-usable-membership-20261026/ceta'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((B.parent/'build.json').read_text());assert sha(B)==receipt['binary_sha256']
spec=json.loads((R/'scripts/unified-exports.json').read_text())
for lib in receipt['libraries']:
 assert lib['identity']['sources']==spec[lib['category']]['sources']
 assert [a for a in lib['command'] if a in ['-O','-O0','-O1','-O2','-O3']]==['-O2']
with (O/'dispatch-final.json').open('w') as f:subprocess.run(['python','tests/unified/check_dispatch.py',str(B)],stdout=f,check=True)
subprocess.run(['python','tests/unified/check_negatives.py',str(B),'--output',str(O/'negatives-final.json.gz')],check=True)
old=json.loads((R/'docs/h31-profile-20261026/production.json').read_text());cmd=[str(B),*old['command'][1:]];runs=[]
for i in range(2):
 t=time.monotonic();p=subprocess.run(cmd,capture_output=True,text=True);row=dict(seconds=time.monotonic()-t,returncode=p.returncode,stdout=p.stdout,stderr=p.stderr);runs.append(row);print('h31',i,row['seconds'],p.returncode,flush=True);assert p.returncode==0 and p.stdout=='CERTIFIED YES\n'
(O/'h31-final.json').write_text(json.dumps(dict(command=cmd,binary_sha256=sha(B),source_sha256=old['source_sha256'],child_sha256=old['child_sha256'],baseline_seconds=old['seconds'],runs=runs),indent=2)+'\n')
cmd=['python','tests/unified/check_frontier.py','--binary',str(B),'--provenance','target/compact-frontier-20261026/provenance.json','--baseline-results','../CeTA-Lean/target/production-certification-benchmark-20261025/ceta.json.gz','--archive','target/compact-frontier-20261026/frontier-5412-compact.zip','--output',str(O/'frontier-final.json.gz'),'--workers','32']
subprocess.run(cmd,check=True)
for name in ['dispatch-final.json','negatives-final.json.gz','h31-final.json','frontier-final.json.gz','exports-build.json','erasure-build.json']:shutil.copy2(O/name,D/name)
for name in ['exports-build.log','final-native-build-verified.log']:(D/(name+'.gz')).write_bytes(gzip.compress((O/name).read_bytes(),mtime=0))
shutil.copy2(B.parent/'build.json',D/'unified-build.json')
print('FINAL_VALIDATION_PASSED',flush=True)
