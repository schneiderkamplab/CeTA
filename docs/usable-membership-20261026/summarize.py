from pathlib import Path
import gzip,json,statistics,collections,csv,hashlib
R=Path.cwd();D=R/'docs/usable-membership-20261026'
old=json.loads(gzip.decompress((R/'docs/performance-next-20261026/frontier-final.json.gz').read_bytes()));new=json.loads(gzip.decompress((D/'frontier-final.json.gz').read_bytes()))
a={r['root']:r for r in old['results']};b={r['root']:r for r in new['results']};assert set(a)==set(b)
for key,x in b.items():
 assert x['status']==a[key]['status']=='accepted'
 assert x['input_sha256']==a[key]['input_sha256'] and x['answer']==a[key]['answer']
 assert x['original_proof_sha256']==a[key]['proof_sha256']
def stats(rows,key):
 vals=sorted(r[key] for r in rows);n=len(vals)
 def pct(p):
  x=(n-1)*p;i=int(x);return vals[i]+(vals[min(i+1,n-1)]-vals[i])*(x-i)
 slow=max(rows,key=lambda r:r[key])
 return dict(min=min(vals),median=statistics.median(vals),mean=statistics.mean(vals),p95=pct(.95),p99=pct(.99),max=max(vals),max_root=slow['root'],sum=sum(vals))
summary=dict(roots=len(b),workers=new['workers'],checks_per_root=new['checks_per_root'],binary_sha256=new['binary_sha256'],exact_identities_preserved=True,baseline_wall_seconds=old['seconds'],wall_seconds=new['seconds'],categories=dict(collections.Counter(r['category'] for r in b.values())))
for name,data in [('before',old),('after',new)]:summary[name]={key:stats(data['results'],key) for key in ['native_seconds','preparation_seconds','seconds']}
rows=[dict(root=k,category=b[k]['category'],before_native=a[k]['native_seconds'],after_native=b[k]['native_seconds'],before_preparation=a[k]['preparation_seconds'],after_preparation=b[k]['preparation_seconds'],input_sha256=b[k]['input_sha256'],original_proof_sha256=b[k]['original_proof_sha256'],compact_proof_sha256=b[k]['proof_sha256']) for k in sorted(b)]
with (D/'per-root-times.csv').open('w') as f:w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
summary['largest_native_after']=sorted(rows,key=lambda r:r['after_native'],reverse=True)[:20]
summary['largest_native_slowdowns']=sorted(rows,key=lambda r:r['after_native']-r['before_native'],reverse=True)[:20]
(D/'comparison.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if not k.startswith('largest')},indent=2))
