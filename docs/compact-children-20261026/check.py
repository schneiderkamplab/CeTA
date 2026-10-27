from pathlib import Path
import json,gzip,zipfile,subprocess,time,hashlib,concurrent.futures
L=Path('../CeTA-Lean');F=Path('../ferrum-compact-certificates/target/compact-children');O=Path('target/compact-children-20261026').resolve();B=Path('target/unified-performance-final-20261026/ceta').resolve();meta=json.loads((L/'target/production-certification-benchmark-20261025/provenance.json').read_text());rows=[r for r in meta['jobs'] if r['child']];manifest={r['original_sha256']:r for r in json.loads((F/'manifest.json').read_text())}
def run(row):
 with zipfile.ZipFile(L/'target/corpus/frontier-5412.zip') as z:data=z.read(row['proof'])
 if row['proof'].endswith('.gz'):data=gzip.decompress(data)
 assert hashlib.sha256(data).hexdigest()==row['proof_sha256']
 p=O/(row['proof_sha256']+'.source');p.write_bytes(data);child=F/Path(row['child']).name;record=manifest[child.stem];assert hashlib.sha256(child.read_bytes()).hexdigest()==record['compact_sha256'];checks=[]
 for _ in range(2):
  t=time.monotonic();r=subprocess.run([str(B),'--category','higher-order-delegation',str(p),str(child)],capture_output=True,text=True);checks.append(dict(seconds=time.monotonic()-t,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr));assert r.returncode==0 and r.stdout.strip()=='CERTIFIED YES',(row['root'],r)
 result=dict(root=row['root'],source_sha256=row['proof_sha256'],**record,checks=checks);print(row['root'],[round(c['seconds'],3) for c in checks],flush=True);return result
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(run,rows))
(O/'results.json').write_text(json.dumps(dict(binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),workers=4,results=results),indent=2)+'\n');print('PASS',len(results))
