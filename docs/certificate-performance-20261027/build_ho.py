from pathlib import Path
import os,subprocess,json,time
R=Path.cwd();O=R/'target/certificate-performance-20261027';base=R/'target/equational-production-20261019/source/thys';dirs=[base,base/'Relative_ADP',base/'RFC_Absolute_Ext',R/'thys/Usable_Rules_Membership',R/'thys/Certificate_Performance']+[p.parent for p in (R/'thys').glob('Higher_Order_*/ROOT')];args=[a for d in dirs for a in ['-d',str(d)]]
env=dict(os.environ,USER_HOME=str(R/'target/usable-membership-20261026/user'),ISABELLE_IDENTIFIER='usable_membership_20261026',AFP=str(R/'target/consolidation-build/afp-source/thys'));cmd=['/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle','build','-v','-b','-j2','-o','threads=4','-o','parallel_proofs=0',*args,'Certificate_Performance_HO_Export'];t=time.monotonic()
with (O/'ho-build.log').open('w') as f:p=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
(O/'ho-build.json').write_text(json.dumps(dict(command=cmd,seconds=time.monotonic()-t,returncode=p.returncode),indent=2));print(p.returncode);raise SystemExit(p.returncode)
