#!/usr/bin/env python3
"""Build the conditional extension on an isolated copy of a verified parent."""
import argparse, hashlib, json, os, shutil, subprocess, time
from pathlib import Path


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('isabelle','ghc','warm-home','base-sessions','afp','out'):
        p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();root=Path(__file__).resolve().parents[1];out=a.out.resolve()
    out.mkdir(parents=True,exist_ok=False)
    source=out/'source';shutil.copytree(root/'thys/Conditional_Checker',source)
    shutil.copy2(root/'src/Haskell/Main_Conditional.hs',source/'Main_Conditional.hs')
    private=out/'isabelle-user/.isabelle/conditional_private'
    private.parent.mkdir(parents=True)
    subprocess.run(['cp','-a','--reflink=auto',str(a.warm_home.resolve()),str(private)],check=True)
    env=dict(os.environ,USER_HOME=str(out/'isabelle-user'),ISABELLE_IDENTIFIER=private.name,AFP=str(a.afp.resolve()))
    times={}
    def run(cmd,name):
        cmd=list(map(str,cmd));(out/(name+'.command.json')).write_text(json.dumps(cmd,indent=2))
        start=time.monotonic()
        with (out/(name+'.log')).open('w') as log:
            subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
        times[name]=time.monotonic()-start
    run([a.isabelle,'build','-j1','-o','threads=4','-o','parallel_proofs=0','-d',a.base_sessions.resolve(),'-D',source,'Conditional_Checker'],'isabelle')
    run([a.isabelle,'export','-n','-d',a.base_sessions.resolve(),'-d',source,'-O',out/'export','-x','*:code/**','Conditional_Checker'],'export')
    generated=out/'export/Conditional_Checker.Conditional_Nontermination/code/export1'
    (out/'ghc').mkdir()
    run([a.ghc,'-O2','-i'+str(generated),'-outputdir',out/'ghc',source/'Main_Conditional.hs','-o',out/'ceta-conditional'],'ghc')
    files=[p for p in source.rglob('*') if p.is_file()]+list(generated.glob('*.hs'))+[out/'ceta-conditional']
    identity=dict(source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
                  source_dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)),
                  parent_sessions=str(a.base_sessions.resolve()),seconds=times,
                  hashes={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (out/'identity.json').write_text(json.dumps(identity,indent=2)+'\n');print(json.dumps(identity,indent=2))


if __name__=='__main__':main()
