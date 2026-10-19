#!/usr/bin/env python3
"""Build the verified cycle extension on an unchanged, private warm parent heap."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--isabelle',type=Path,required=True)
    ap.add_argument('--ghc',type=Path,required=True)
    ap.add_argument('--warm-home',type=Path,required=True,help='Existing .isabelle/IDENTIFIER directory')
    ap.add_argument('--base-sessions',type=Path,required=True,help='Frozen consolidated thys used to build the warm parent')
    ap.add_argument('--afp',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();root=Path(__file__).resolve().parents[1]
    out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
    source=out/'source';shutil.copytree(root/'thys/Cycle_Checker',source)
    shutil.copy2(root/'src/Haskell/Main_Cycle.hs',source/'Main_Cycle.hs')
    private=out/'isabelle-user/.isabelle/cycle_private'
    private.parent.mkdir(parents=True)
    subprocess.run(['cp','-a','--reflink=auto',str(args.warm_home.resolve()),str(private)],check=True)
    env=dict(os.environ,USER_HOME=str(out/'isabelle-user'),ISABELLE_IDENTIFIER=private.name,AFP=str(args.afp.resolve()))
    def run(command,name):
        (out/(name+'.command.json')).write_text(json.dumps(list(map(str,command)),indent=2)+'\n')
        with (out/(name+'.log')).open('w') as log:
            subprocess.run(list(map(str,command)),env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
    run([args.isabelle,'build','-j1','-o','threads=4','-o','parallel_proofs=0','-d',args.base_sessions.resolve(),'-D',source,'Cycle_Checker'],'isabelle')
    run([args.isabelle,'export','-n','-d',args.base_sessions.resolve(),'-d',source,'-O',out/'export','-x','*:code/**','Cycle_Checker'],'export')
    generated=out/'export/Cycle_Checker.Cycle_Morphism/code/export1'
    (out/'ghc').mkdir()
    run([args.ghc,'-O2','-i'+str(generated),'-outputdir',out/'ghc',source/'Main_Cycle.hs','-o',out/'ceta-cycle'],'ghc')
    files=list(source.rglob('*'))+list(generated.glob('*.hs'))+[out/'ceta-cycle']
    identity={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files if p.is_file()}
    identity['base_commit']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    identity['parent_sessions']=str(args.base_sessions.resolve())
    identity['trusted_build']='Isabelle kernel, no sorry or quick_and_dirty; generated Haskell'
    (out/'identity.json').write_text(json.dumps(identity,indent=2)+'\n')
    print(json.dumps(identity,indent=2))


if __name__=='__main__':main()
