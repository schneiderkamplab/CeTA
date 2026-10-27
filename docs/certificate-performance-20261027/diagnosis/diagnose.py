from pathlib import Path
import subprocess,time,json
R=Path.cwd();O=R/'target/certificate-performance-20261027';rows=[]
for variant,bin in [('before',R/'target/unified-usable-membership-20261026/ceta'),('parser',O/'ceta-parser-only'),('after',R/'target/unified-certificate-performance-20261027/ceta')]:
 for form in ['explicit','shared']:
  cmd=[str(bin),str(O/('128056-'+form+'.xml')),'+RTS','-s','-RTS'];t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);rec=dict(variant=variant,form=form,seconds=time.monotonic()-t,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr,command=cmd);rows.append(rec);print(variant,form,rec['seconds'],r.returncode,flush=True);(O/'regression-128056.json').write_text(json.dumps(rows,indent=2)+'\n')
