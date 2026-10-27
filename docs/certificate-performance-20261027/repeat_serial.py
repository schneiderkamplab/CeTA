from pathlib import Path
import json,gzip,zipfile,subprocess,time,concurrent.futures,tempfile,statistics
R=Path.cwd();O=R/'target/certificate-performance-20261027';D=R/'docs/certificate-performance-20261027'
while not (O/'controlled-161533.json').exists() or len(json.loads((O/'controlled-161533.json').read_text())['runs'])<8:time.sleep(5)
subprocess.run(['python3',str(O/'summarize.py')],check=True)
comparison=json.loads((D/'comparison.json').read_text());rows=[r for r in json.loads((D/'controlled-slowdowns.json').read_text())['results'] if r['ratio']>1.2];meta=json.loads((R/'target/compact-frontier-20261026/provenance.json').read_text());jobs={r['root']:r for r in meta['jobs']};final={r['root']:r for r in json.loads(gzip.decompress((O/'frontier.json.gz').read_bytes()))['results']}
bins=dict(before=R/'target/unified-usable-membership-20261026/ceta',after=R/'target/unified-certificate-performance-20261027/ceta');archives=dict(before=R/'target/compact-frontier-20261026/frontier-5412-compact.zip',after=R/'target/shared-frontier-compatible-20261027/frontier-5412-shared.zip')
def run(row):
 root=row['root'];job=jobs[root];runs=[]
 with tempfile.TemporaryDirectory(dir=O) as tmp:
  paths={}
  for variant,archive in archives.items():
   with zipfile.ZipFile(archive) as z:data=z.read(job['proof'])
   if job['proof'].endswith('.gz'):data=gzip.decompress(data)
   p=Path(tmp)/variant;p.write_bytes(data);paths[variant]=p
  for repeat in range(3):
   for variant in (['before','after'] if repeat%2==0 else ['after','before']):
    cmd=[str(bins[variant]),'--category',final[root]['category'],*job['flags'],str(paths[variant])]
    if job['child']:cmd.append(str(O/'shared-children'/Path(job['child']).name))
    t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0 and r.stdout==final[root]['stdout'],(root,r)
    runs.append(dict(variant=variant,repeat=repeat,seconds=time.monotonic()-t))
 med={v:statistics.median(r['seconds'] for r in runs if r['variant']==v) for v in bins};return dict(root=root,runs=runs,median=med,ratio=med['after']/med['before'])
with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:results=list(pool.map(run,rows))
(D/'serial-slowdowns.json').write_text(json.dumps(dict(workers=1,roots=len(results),results=results),indent=2)+'\n');print('REPEATED',len(results),flush=True)
