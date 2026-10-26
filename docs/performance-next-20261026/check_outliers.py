from pathlib import Path
import subprocess,json,gzip,hashlib,time,concurrent.futures
O=Path('target/performance-next-20261026').resolve();L=Path('../CeTA-Lean').resolve();source=L/'target/outlier-profiles-20261026';jobs=json.loads((source/'jobs.json').read_text());old=json.loads(gzip.decompress((L/'target/production-certification-benchmark-20261025/ceta.json.gz').read_bytes()));expected={r['root']:r['checks'][0]['verdict'] for r in old['results']};binary=Path('target/unified-performance-final-20261026/ceta').resolve()
def run(r):
 checks=[];category='lp' if r['id']==7 else 'higher-order-delegation' if r['id']==11 else 'cpf'
 for _ in range(2):
  cmd=[str(binary),'--category',category,*r['flags'],str(source/str(r['id'])/'proof')]
  if r['child']:cmd.append(r['child'])
  t=time.monotonic();p=subprocess.run(cmd,capture_output=True,text=True);result=dict(seconds=time.monotonic()-t,returncode=p.returncode,stdout=p.stdout,stderr=p.stderr);checks.append(result);print(r['id'],result,flush=True);assert p.returncode==0 and p.stdout.strip()==expected[r['root']]
 return dict(id=r['id'],root=r['root'],proof_sha256=r['proof_sha256'],checks=checks)
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:rows=list(pool.map(run,[r for r in jobs if r['id']>=5]))
(O/'final-outliers.json').write_text(json.dumps(dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),results=rows),indent=2))
