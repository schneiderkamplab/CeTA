#!/usr/bin/env python3
"""Build a committed source revision, all exports and three CLIs in a new directory.

Requires Isabelle2025-2 and GHC9.6.7. No live worktree sources or shared writable
heaps are used. A cold build deliberately does not require another campaign.
"""
import argparse,gzip,json,os,pathlib,shutil,subprocess,tarfile
from replay import execute,sha,write
ROOT=pathlib.Path(__file__).resolve().parents[2]
DIRS=['thys','thys/Relative_ADP','thys/RFC_Absolute_Ext']
TARGETS=['Outermost_RZ_Ext','Proof_Checker','Code','RFC_Absolute_Ext','Relative_ADP_Ceta_Dev']

def main():
 p=argparse.ArgumentParser();p.add_argument('--revision',required=True);p.add_argument('--isabelle',type=pathlib.Path,required=True);p.add_argument('--ghc',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--jobs',type=int,default=2);p.add_argument('--threads',type=int,default=8);a=p.parse_args()
 if a.jobs<1 or a.threads<1:p.error('Positive jobs and threads required')
 revision=subprocess.check_output(['git','rev-parse','--verify',a.revision+'^{commit}'],cwd=ROOT,text=True).strip()
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);source=out/'source';logs=out/'logs';logs.mkdir();env={k:v for k,v in os.environ.items() if not k.startswith(('ISABELLE_','ML_','HPCTIX')) and k not in ['AFP','USER_HOME']}
 isabelle=a.isabelle.resolve();ghc=a.ghc.resolve()
 if subprocess.check_output([str(isabelle),'version'],env=env,text=True).strip()!='Isabelle2025-2':raise ValueError('Isabelle version differs from pinned toolchain')
 if subprocess.check_output([str(ghc),'--numeric-version'],env=env,text=True).strip()!='9.6.7':raise ValueError('GHC version differs from pinned toolchain')
 archive=out/'source.tar'
 with archive.open('wb') as f:subprocess.run(['git','archive',revision],cwd=ROOT,stdout=f,check=True)
 with tarfile.open(archive) as t:t.extractall(source,filter='data')
 assets=source/'tools/consolidation/build-assets';manifest=json.loads((assets/'manifest.json').read_text())
 for name,info in manifest['files'].items():
  if sha(assets/name)!=info['sha256']:raise ValueError('Build asset changed: '+name)
 with tarfile.open(assets/'afp-source.tar.gz') as t:t.extractall(out/'afp',filter='data')
 # Archive layout and every dependency file are checked against the frozen map.
 with gzip.open(assets/'afp-files.json.gz','rt') as f:files=json.load(f)
 # Manifest records exact path, byte count and SHA256 for each file.
 for item in files:
  name,digest=item['path'],item['sha256']
  path=(out/'afp'/name).resolve()
  if not path.is_relative_to(out/'afp') or sha(path)!=digest:raise ValueError('AFP identity mismatch: '+name)
 home=out/'isabelle-user';identifier='consolidated_verified';settings=home/'.isabelle'/identifier/'etc';settings.mkdir(parents=True)
 settings.joinpath('settings').write_text('ML_PLATFORM="$ISABELLE_PLATFORM64"\nML_HOME="$POLYML_HOME/$ML_PLATFORM"\nML_OPTIONS="$ML_OPTIONS64"\nISABELLE_HEAPS_SYSTEM="$USER_HOME/private-system-heaps"\n')
 env.update(USER_HOME=str(home),ISABELLE_IDENTIFIER=identifier,AFP=str(out/'afp/thys'))
 def run(name,cmd,cwd=source,timeout=43200):
  r=execute(cmd,cwd,env,logs/name,timeout);write(logs/(name+'.json'),r)
  if r['returncode']!=0 or r['timed_out']:raise RuntimeError('Build failed: '+name)
  return r
 dirs=sum((['-d',str(source/d)] for d in DIRS),[])
 run('isabelle',[str(isabelle),'build','-v','-j',str(a.jobs),'-o',f'threads={a.threads}','-o','parallel_proofs=0',*dirs,*TARGETS])
 exports={'ordinary':('Code','Code.Code_Haskell','Main.hs'),'rfc':('RFC_Absolute_Ext','RFC_Absolute_Ext.RFC_Absolute_Code','Main_RFC.hs'),'relative':('Relative_ADP_Ceta_Dev','Relative_ADP_Ceta_Dev.Relative_ADP_Code_Haskell','Main_Relative_ADP.hs')}
 binaries={};export_hashes={}
 for name,(session,theory,adapter) in exports.items():
  destination=out/('export-'+name)
  run('export-'+name,[str(isabelle),'export','-n',*dirs,'-O',str(destination),'-p','3','-x',theory+':code/export1/**',session])
  modules=list(destination.glob('*.hs'))
  if not modules:raise ValueError('Empty generated export: '+name)
  export_hashes[name]={x.name:sha(x) for x in modules}
  shutil.copyfile(source/'src/Haskell'/adapter,destination/'Main.hs')
  binary=out/('ceta-'+name)
  run('ghc-'+name,[str(ghc),'-O2','-package','array','-XRankNTypes','-odir',str(out/('ghc-'+name)),'-hidir',str(out/('ghc-'+name)),'--make','Main.hs','-o',str(binary)],destination,3600)
  binaries[name]=dict(path=str(binary),sha256=sha(binary))
  if name=='rfc':
   hpc=out/'ceta-hpc'
   run('ghc-hpc',[str(ghc),'-O2','-package','array','-XRankNTypes','-odir',str(out/'ghc-hpc'),'-hidir',str(out/'ghc-hpc'),'-fhpc','-hpcdir',str(out/'hpc-mix'),'--make','Main.hs','-o',str(hpc)],destination,3600)
   binaries['hpc']=dict(path=str(hpc),sha256=sha(hpc))
 for tool in ['ExportMix','ExportTix']:
  run('ghc-'+tool,[str(ghc),'-O2','-package','hpc','-odir',str(out/('ghc-'+tool)),'-hidir',str(out/('ghc-'+tool)),str(source/'tools/consolidation'/(tool+'.hs')),'-o',str(out/tool)],source,600)
 write(out/'summary.json',dict(revision=revision,archive_sha256=sha(archive),isabelle_version='Isabelle2025-2',ghc_version='9.6.7',binaries=binaries,exports=export_hashes,passed=True))

if __name__=='__main__':main()
