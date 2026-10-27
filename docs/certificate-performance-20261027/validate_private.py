from pathlib import Path
import json,subprocess,time,hashlib
R=Path.cwd();O=R/'target/certificate-performance-20261027';B=R/'target/unified-certificate-performance-20261027/ceta';receipt=B.parent/'build.json';bad='a2655eee0458ef7efcd310a0b77d37a3a075b28b5d7a24151209cfb0140f79ea'
while json.loads(receipt.read_text())['binary_sha256']==bad:time.sleep(5)
rows=[]
for repeat in range(2):
 for variant,binary in [('before',R/'target/unified-usable-membership-20261026/ceta'),('after',B)]:
  cmd=[str(binary),str(O/'128056-explicit.xml'),'+RTS','-s'];t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);rec=dict(variant=variant,repeat=repeat,seconds=time.monotonic()-t,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr);assert r.returncode==0;rows.append(rec);print(variant,rec['seconds'],flush=True)
(O/'private-export-regression-check.json').write_text(json.dumps(dict(binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),runs=rows),indent=2)+'\n')
a=sum(r['seconds'] for r in rows if r['variant']=='after');b=sum(r['seconds'] for r in rows if r['variant']=='before');assert a/b<1.2,(a,b)
with (O/'validation-driver-private.log').open('w') as f:subprocess.run(['python3',str(O/'validate.py')],stdout=f,stderr=subprocess.STDOUT,check=True)
