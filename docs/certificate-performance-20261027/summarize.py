from pathlib import Path
import json,gzip,statistics,csv
R=Path.cwd();O=R/'target/certificate-performance-20261027';D=R/'docs/certificate-performance-20261027'
def read(p):return json.loads(gzip.decompress(p.read_bytes()))
def stats(values):
 v=sorted(values)
 def pct(p):
  x=(len(v)-1)*p;i=int(x);return v[i]+(v[min(i+1,len(v)-1)]-v[i])*(x-i)
 return dict(count=len(v),min=v[0],median=statistics.median(v),mean=statistics.mean(v),p95=pct(.95),p99=pct(.99),max=v[-1],sum=sum(v))
old=read(R/'docs/usable-membership-20261026/frontier-final.json.gz');new=read(O/'frontier.json.gz');a={r['root']:r for r in old['results']};b={r['root']:r for r in new['results']};assert set(a)==set(b)
for root in a:
 assert a[root]['status']==b[root]['status']=='accepted'
 assert a[root]['input_sha256']==b[root]['input_sha256'] and a[root]['answer']==b[root]['answer']
 assert a[root]['original_proof_sha256']==b[root]['original_proof_sha256']
report=dict(roots=len(a),before_wall_seconds=old['seconds'],after_wall_seconds=new['seconds'],before_native=stats([r['native_seconds'] for r in a.values()]),after_native=stats([r['native_seconds'] for r in b.values()]),before_preparation=stats([r['preparation_seconds'] for r in a.values()]),after_preparation=stats([r['preparation_seconds'] for r in b.values()]))
rows=[dict(root=k,before=a[k]['native_seconds'],after=b[k]['native_seconds'],ratio=b[k]['native_seconds']/a[k]['native_seconds'],category=b[k]['category'],before_preparation=a[k]['preparation_seconds'],after_preparation=b[k]['preparation_seconds']) for k in sorted(a)]
report['slowdowns_to_repeat']=[r for r in rows if r['ratio']>1.2 and r['after']-r['before']>.2]
report['worst_before']=sorted(rows,key=lambda r:-r['before'])[:20];report['worst_after']=sorted(rows,key=lambda r:-r['after'])[:20]
(D/'comparison.json').write_text(json.dumps(report,indent=2)+'\n')
with (D/'per-root-times.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print(json.dumps({k:v for k,v in report.items() if not isinstance(v,list)},indent=2))
