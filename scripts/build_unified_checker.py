#!/usr/bin/env python3
"""Build one CeTA executable from isolated, hash-verified category libraries (-O2).

The export directory contains CATEGORY/*.hs matching unified-exports.json.
Only the changed category libraries are rebuilt; no shared worktree outputs are used.
"""
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,time,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def run(cmd,log):
    with log.open('w') as f:subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,check=True)
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--exports',type=Path,help='Override the committed, hash-verified export snapshots')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=4)
    a=ap.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    exports=a.exports.resolve() if a.exports else out/'exports'
    ghc=shutil.which(os.environ.get('GHC','ghc'));pkg=shutil.which(os.environ.get('GHC_PKG','ghc-pkg'));ar=shutil.which('ar')
    version=subprocess.check_output([ghc,'--numeric-version'],text=True).strip()
    dependencies=[subprocess.check_output([pkg,'field',p,'id','--simple-output'],text=True).strip() for p in ['base','array']]
    manifest=json.loads((ROOT/'scripts/unified-exports.json').read_text())
    db=out/'packages'
    if not db.exists():subprocess.run([pkg,'init',str(db)],check=True)
    def library(item):
        key,spec=item;source=exports/key;adapter=ROOT/spec['adapter']
        if not all(re.fullmatch(r'-D[A-Za-z_][A-Za-z_0-9]*(?:=[A-Za-z_0-9]+)?',flag) for flag in spec['cpp']):
            raise ValueError(f'Unexpected compiler flags in category manifest: {key}')
        if not a.exports:
            archive=ROOT/spec['archive']
            if sha(archive)!=spec['archive_sha256']:raise ValueError(f'Archive hash mismatch: {key}')
            source.mkdir(parents=True,exist_ok=True)
            # A newer verified export can remove or merge generated modules.
            # Drop obsolete files only in the builder's private extraction cache.
            for stale in source.glob('*.hs'):
                if stale.name not in spec['sources']:stale.unlink()
            with tarfile.open(archive,'r:gz') as bundle:
                for member in bundle.getmembers():
                    if not member.isfile() or member.name not in spec['sources'] or Path(member.name).name!=member.name:
                        raise ValueError(f'Unexpected archive member: {member.name}')
                    (source/member.name).write_bytes(bundle.extractfile(member).read())
        actual={p.name:sha(p) for p in source.glob('*.hs')}
        if actual!=spec['sources']:raise ValueError(f'Export snapshot mismatch: {key}')
        for p in source.glob('*.hs'):
            if re.search(r'OPTIONS_GHC[^\n]*(?:-O(?:0|1|3)?\b|-fno-)',p.read_text()):
                raise ValueError(f'Optimization override in {p}')
        helpers={str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'src/Haskell/Ceta/Input').glob('*.hs')}
        identity=dict(sources=actual,adapter=sha(adapter),helpers=helpers,ghc=version,cpp=spec['cpp'],optimization='-O2')
        digest=hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest()
        unit='ceta-'+key+'-1.0-'+digest[:16];work=out/unit;work.mkdir(exist_ok=True);receipt=work/'build.json'
        if receipt.exists():
            old=json.loads(receipt.read_text())
            if old['identity']==identity and sha(work/('libHS'+unit+'.a'))==old['archive_sha256']:return old
        # Fresh private objects ensure every generated module gets -O2.
        obj=work/'objects'
        if obj.exists():shutil.rmtree(obj)
        obj.mkdir();modules=[]
        for p in source.glob('*.hs'):
            match=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
            if not match:raise ValueError(f'No module declaration: {p}')
            modules.append(match[1])
        cmd=[ghc,'-j4','-O2','-fforce-recomp','-rtsopts','-package','array','-XRankNTypes',*spec['cpp'],'-this-unit-id',unit,'-i','-i'+str(source),'-i'+str(ROOT/'src/Haskell'),'-outputdir',str(obj),'--make','-no-link',str(adapter)]
        t=time.monotonic();run(cmd,work/'build.log')
        modules=sorted('.'.join(p.relative_to(obj).with_suffix('').parts) for p in obj.rglob('*.hi') if '.'.join(p.relative_to(obj).with_suffix('').parts)!=spec['module'])
        archive=work/('libHS'+unit+'.a');subprocess.run([ar,'crs',str(archive),*[str(p) for p in sorted(obj.rglob('*.o'))]],check=True)
        conf=work/'package.conf'
        conf.write_text(f'name: ceta-{key}\nversion: 1.0\nid: {unit}\nkey: {unit}\nexposed: True\nexposed-modules: {spec["module"]}\nhidden-modules: '+ ' '.join(sorted(modules))+f'\nimport-dirs: {obj}\nlibrary-dirs: {work}\nhs-libraries: HS{unit}\ndepends: '+ ' '.join(dependencies)+'\n')
        data=dict(category=key,unit=unit,identity=identity,command=cmd,seconds=time.monotonic()-t,archive_sha256=sha(archive),configuration=str(conf))
        save(receipt,data);print('Built',key,round(data['seconds'],1),flush=True);return data
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:records=list(pool.map(library,manifest.items()))
    # Package-db mutations are sequential, after independent compilations finish.
    for r in records:subprocess.run([pkg,'--package-db='+str(db),'update',r['configuration']],check=True,stdout=subprocess.DEVNULL)
    obj=out/'main';obj.mkdir(exist_ok=True);binary=out/'ceta'
    cmd=[ghc,'-j4','-O2','-fforce-recomp','-rtsopts','-package-db',str(db),'-outputdir',str(obj)]
    for r in records:cmd+=['-package-id',r['unit']]
    temporary=out/'ceta.linked'
    cmd+=['--make',str(ROOT/'src/Haskell/Main_Unified.hs'),'-o',str(temporary)]
    t=time.monotonic();run(cmd,out/'link.log');temporary.replace(binary)
    save(out/'build.json',dict(binary=str(binary),binary_sha256=sha(binary),compiler=version,command=cmd,link_seconds=time.monotonic()-t,main_sha256=sha(ROOT/'src/Haskell/Main_Unified.hs'),libraries=records))
    print(binary,flush=True)
if __name__=='__main__':main()
