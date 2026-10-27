from pathlib import Path
import json,gzip,hashlib,subprocess,time,copy
R=Path.cwd();O=R/'target/certificate-performance-20261027';S=R/'target/shared-frontier-compatible-20261027';B=R/'target/unified-certificate-performance-20261027/ceta'
def read(p):return json.loads(gzip.decompress(p.read_bytes()))
def save(p,x):p.write_bytes(gzip.compress(json.dumps(x).encode(),mtime=0))
while not (S/'reexport.json.gz').exists():time.sleep(5)
prior_path=O/'frontier-before-lookup-compatibility.json.gz'
if not prior_path.exists():prior_path.write_bytes((O/'frontier.json.gz').read_bytes())
prior=read(prior_path);oldrows={r['root']:r for r in prior['results']};manifest=read(S/'manifest.json.gz');roots={r['root']:r for r in manifest['roots']}
meta=json.loads((R/'target/compact-frontier-20261026/provenance.json').read_text());meta['archive_sha256']=manifest['artifact_archive_sha256'];meta['manifest_sha256']=hashlib.sha256((S/'manifest.json.gz').read_bytes()).hexdigest();meta['jobs']=[dict(r,proof_sha256=roots[r['root']]['proof_sha256'],compact_proof_sha256=r['proof_sha256']) for r in meta['jobs']]
(S/'provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
changed={k for k in roots if roots[k]['proof_sha256']!=oldrows[k]['proof_sha256']};assert {k for k,r in oldrows.items() if r['status']!='accepted'}<=changed
scoped=dict(meta,jobs=[r for r in meta['jobs'] if r['root'] in changed]);p=O/'lookup-scoped-provenance.json';p.write_text(json.dumps(scoped,indent=2)+'\n')
base=read(R.parent/'CeTA-Lean/target/production-certification-benchmark-20261025/ceta.json.gz');base['results']=[r for r in base['results'] if r['root'] in changed];basepath=O/'lookup-scoped-baseline.json.gz';save(basepath,base)
result=O/'lookup-scoped-results.json.gz';cmd=['python3','tests/unified/check_frontier.py','--binary',str(B),'--provenance',str(p),'--baseline-results',str(basepath),'--archive',str(S/'frontier-5412-shared.zip'),'--output',str(result),'--workers','32','--child-spec','tests/unified/shared-children.json']
with (O/'lookup-scoped.log').open('w') as f:subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,check=True)
new=read(result);assert new['binary_sha256']==prior['binary_sha256'];merged={**oldrows,**{r['root']:r for r in new['results']}};assert set(merged)==set(roots)
for k,r in merged.items():assert r['status']=='accepted' and r['proof_sha256']==roots[k]['proof_sha256'] and r['input_sha256']==roots[k]['input_sha256']
final=dict(prior,archive_sha256=meta['archive_sha256'],provenance_sha256=hashlib.sha256((S/'provenance.json').read_bytes()).hexdigest(),results=[merged[k] for k in sorted(merged)],counts={'accepted':len(merged)},seconds=prior['seconds']+new['seconds'],full_run_seconds=prior['seconds'],followup_seconds=new['seconds'],validation_kind='full run followed by changed-representation rechecks',full_run_roots=len(oldrows),rechecked_changed_roots=len(changed),reused_unchanged_roots=len(roots)-len(changed),full_run_report_sha256=hashlib.sha256(prior_path.read_bytes()).hexdigest(),followup_report_sha256=hashlib.sha256(result.read_bytes()).hexdigest())
tmp=O/'frontier-final.tmp';save(tmp,final);tmp.replace(O/'frontier.json.gz');print(final['counts'],'rechecked',len(changed),'reused',len(roots)-len(changed),flush=True)
