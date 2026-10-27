from pathlib import Path
import json,gzip,zipfile,subprocess,time,hashlib,concurrent.futures
R=Path.cwd();O=R/'target/usable-membership-20261026/regressions';O.mkdir(exist_ok=True)
old=R/'target/unified-performance-final-20261026/ceta';new=R/'target/unified-usable-membership-20261026/ceta';manifest=json.loads(gzip.decompress((R/'target/compact-frontier-20261026/manifest.json.gz').read_bytes()));rows={r['root']:r for r in manifest['roots']};names=['SRS_Standard/ICFP_2010/'+n+'.ari' for n in ['68989','85782','29415']]
with zipfile.ZipFile(R/'target/compact-frontier-20261026/frontier-5412-compact.zip') as z:
 for name in names:
  row=rows[name];p=O/(Path(name).stem+'.xml');data=gzip.decompress(z.read(row['proof']));assert hashlib.sha256(data).hexdigest()==row['proof_sha256'];p.write_bytes(data)
def run(name):
 result=dict(root=name,compact_proof_sha256=rows[name]['proof_sha256'],runs=[])
 for variant in ['old','new','new','old']:
  binary=old if variant=='old' else new;cmd=[str(binary),'--category','cpf',str(O/(Path(name).stem+'.xml'))];start=time.monotonic();p=subprocess.run(cmd,capture_output=True,text=True);r=dict(variant=variant,seconds=time.monotonic()-start,returncode=p.returncode,stdout=p.stdout,stderr=p.stderr);result['runs'].append(r);print(name,variant,r['seconds'],p.returncode,flush=True);assert p.returncode==0 and p.stdout.strip()=='CERTIFIED'
 return result
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:results=list(pool.map(run,names))
report=dict(workers=3,order=['old','new','new','old'],same_compact_certificates=True,old_binary_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),new_binary_sha256=hashlib.sha256(new.read_bytes()).hexdigest(),results=results)
(R/'docs/usable-membership-20261026/controlled-regressions.json').write_text(json.dumps(report,indent=2)+'\n')
