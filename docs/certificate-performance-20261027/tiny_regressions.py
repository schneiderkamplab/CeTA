from pathlib import Path
import json,gzip,zipfile,tempfile,subprocess,time,statistics
R=Path.cwd();O=R/'target/certificate-performance-20261027';D=R/'docs/certificate-performance-20261027';small=json.loads((D/'serial-slowdowns.json').read_text());roots=[r['root'] for r in small['results'] if r['ratio']>1.2];meta=json.loads((R/'target/shared-frontier-compatible-20261027/provenance.json').read_text());jobs={r['root']:r for r in meta['jobs']};report=[]
for root in roots:
 job=jobs[root]
 with tempfile.TemporaryDirectory(dir=O) as tmp:
  paths={}
  for form,archive in [('explicit','compact-frontier-20261026/frontier-5412-compact.zip'),('shared','shared-frontier-compatible-20261027/frontier-5412-shared.zip')]:
   with zipfile.ZipFile(R/'target'/archive) as z:data=z.read(job['proof'])
   if job['proof'].endswith('.gz'):data=gzip.decompress(data)
   p=Path(tmp)/form;p.write_bytes(data);paths[form]=p
  runs=[]
  for i in range(15):
   variants=[('before','explicit'),('after','explicit'),('after','shared')]
   variants=variants[i%3:]+variants[:i%3]
   for variant,form in variants:
    binary=R/'target'/('unified-usable-membership-20261026' if variant=='before' else 'unified-certificate-performance-20261027')/'ceta';t=time.monotonic();r=subprocess.run([str(binary),*job['flags'],str(paths[form])],capture_output=True,text=True);assert r.returncode==0;runs.append(dict(variant=variant,form=form,seconds=time.monotonic()-t))
  med={v+'_'+f:statistics.median(r['seconds'] for r in runs if r['variant']==v and r['form']==f) for v,f in variants};report.append(dict(root=root,runs=runs,median=med,bytes={k:p.stat().st_size for k,p in paths.items()}))
(D/'tiny-regressions.json').write_text(json.dumps(report,indent=2)+'\n');print([(r['root'],r['median'],r['bytes']) for r in report])
