from pathlib import Path
import subprocess,time,json,hashlib
R=Path.cwd();O=R/'target/certificate-performance-20261027'
while not (O/'frontier.json.gz').exists():time.sleep(5)
binaries=dict(before=R/'target/unified-usable-membership-20261026/ceta',after=R/'target/unified-certificate-performance-20261027/ceta')
proofs=dict(explicit=R/'target/srs161533-profile-20261027/proof.xml',shared=O/'161533-shared.xml')
rows=[]
for repeat in range(2):
 for form in ['explicit','shared']:
  for variant in (['before','after'] if repeat==0 else ['after','before']):
   cmd=[str(binaries[variant]),str(proofs[form]),'+RTS','-s','-RTS'];t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
   rec=dict(repeat=repeat,variant=variant,form=form,command=cmd,seconds=time.monotonic()-t,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr)
   assert r.returncode==0 and r.stdout.strip()=='CERTIFIED',rec
   rows.append(rec);print(variant,form,rec['seconds'],flush=True)
   (O/'controlled-161533.json').write_text(json.dumps(dict(binary_sha256={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in binaries.items()},proof_sha256={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in proofs.items()},runs=rows),indent=2)+'\n')
