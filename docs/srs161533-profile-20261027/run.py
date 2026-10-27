from pathlib import Path
import subprocess,time,json,hashlib
r=Path.cwd();o=r/'target/srs161533-profile-20261027';src=r/'target/unified-usable-membership-20261026/exports/cpf'
def run(cmd,name):
 t=time.monotonic();p=subprocess.run(cmd,cwd=o,capture_output=True,text=True);d=dict(command=cmd,seconds=time.monotonic()-t,returncode=p.returncode,stdout=p.stdout,stderr=p.stderr);(o/(name+'.json')).write_text(json.dumps(d,indent=2));print(name,d['seconds'],p.returncode,flush=True);assert p.returncode==0;return d
cmd=['ghc','-j4','-O2','-prof','-fprof-auto','-rtsopts','-fforce-recomp','-package','array','-XRankNTypes','-i'+str(src),'-i'+str(r/'src/Haskell'),'-outputdir',str(o/'objects'),'--make',str(o/'Main.hs'),'-o',str(o/'ceta-profile')]
run(cmd,'build')
run([str(r/'target/unified-usable-membership-20261026/ceta'),'--category','cpf',str(o/'proof.xml'),'+RTS','-s','-RTS'],'production')
run([str(o/'ceta-profile'),str(o/'proof.xml'),'+RTS','-p','-s','-RTS'],'profile')
