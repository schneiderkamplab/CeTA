#!/usr/bin/env python3
"""Sequential formal checks of reconstructed feature commits in a private source.

Run only after other builds using this private Isabelle identifier have finished.
No source worktree, branch, or shared dependency heap is modified. Validation
stops on the first failing intermediate commit and preserves its build receipt.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,tarfile
from replay import execute,write,sha
ROOT=pathlib.Path(__file__).resolve().parents[2]


def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)


def targets(title,source):
    if title in ['AAECC full-to-innermost criterion','Zantema QDP-to-SRS criterion','General rule strengthening']:
        return ['Proof_Checker_Base']
    if title.startswith(('Full and complete GM04','Standalone CSR','CPF adapters')):
        return ['Proof_Checker']
    if title=='Shared production export configuration':return ['Proof_Checker','Code']
    if title.startswith(('RFC deletion','Recursive split','Full termination to outermost')):return ['RFC_Absolute_Ext']
    if title.startswith('Shared outermost'):return ['Outermost_RZ_Ext','Proof_Checker']
    if title=='Complete CSR tail-core soundness case':return ['CSR_Checker_Extensions']
    if title=='Specialize finite conservative coverage':return ['CSR_Checker_Extensions']
    if title.startswith(('Share guarded','Share non-strict')):return ['CSR_Guarded_List_Measure_Check']
    if title.startswith('Factor usable-rule'):return ['CSR_Muterm_Ext']
    if title.startswith('Share root and residual CSR'):return ['Proof_Checker']
    if title.startswith('Generalize compound'):return ['Relative_ADP_Checker_Dev']
    if title.startswith(('Production ADP','Single-parse','Reuse the verified','Root-sensitive','Argument-filtered')):
        return ['Relative_ADP_Checker_Dev','Relative_ADP_Ceta_Dev']
    if title=='Freeze regression tools corpora and verification evidence':return []
    return ['Proof_Checker','Code','RFC_Absolute_Ext','Relative_ADP_Checker_Dev','Relative_ADP_Ceta_Dev','Outermost_RZ_Ext']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['manifest','source','output','isabelle','user-home','afp']:
        p.add_argument('--'+key,type=pathlib.Path,required=True)
    p.add_argument('--identifier',required=True)
    p.add_argument('--start',type=int,default=1)
    p.add_argument('--stop',type=int)
    a=p.parse_args();source=a.source.resolve();out=a.output.resolve()
    for private in [source,out,a.user_home.resolve()]:
        if not private.is_relative_to(ROOT/'target'):raise ValueError('All mutable validation paths must be private target directories')
    manifest=json.loads(a.manifest.read_text());series=manifest['series']
    if a.start<1 or a.start>len(series):p.error('Invalid starting patch')
    out.mkdir(parents=True,exist_ok=False);source.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith(('ISABELLE_','ML_','HPCTIX')) and k not in ['AFP','USER_HOME']}
    env.update(USER_HOME=str(a.user_home.resolve()),ISABELLE_IDENTIFIER=a.identifier,AFP=str(a.afp.resolve()))
    production=lambda path:path.startswith(('thys/','dev/','src/')) or path in ['Makefile','ROOTS']
    allpaths=set()
    for rev in [manifest['base']]+[r['commit'] for r in series]:
        allpaths.update(x for x in git('ls-tree','-r','--name-only',rev).decode().splitlines() if production(x))
    receipts=[]
    for number,row in enumerate(series,1):
        if number<a.start or (a.stop and number>a.stop):continue
        commit=row['commit'];run=out/f'{number:04d}';run.mkdir()
        patch=git('diff',row['parent'],commit,'--','thys','dev').decode()
        admissions=[line for line in patch.splitlines() if line.startswith('+') and not line.startswith('+++') and re.search(r'\b(sorry|oops|axiomatization|skip_proof)\b',line)]
        if admissions:raise ValueError('New admission or unchecked assumption in patch '+str(number)+': '+repr(admissions))
        names=[x for x in git('ls-tree','-r','--name-only',commit).decode().splitlines() if production(x)]
        for name in allpaths-set(names):(source/name).unlink(missing_ok=True)
        tops=sorted({x.split('/')[0] for x in names})
        archive=run/'production-source.tar'
        with archive.open('wb') as handle:subprocess.run(['git','archive',commit,*tops],cwd=ROOT,stdout=handle,check=True)
        source_hashes={}
        with tarfile.open(archive) as tar:
            for member in tar:
                if not member.isfile():continue
                path=(source/member.name).resolve()
                if not path.is_relative_to(source):raise ValueError('Source archive escapes private directory')
                data=tar.extractfile(member).read();source_hashes[member.name]=hashlib.sha256(data).hexdigest()
                if not path.exists() or path.read_bytes()!=data:
                    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
        write(run/'source-hashes.json',source_hashes)
        dirs=['thys']
        if (source/'thys/Relative_ADP/ROOTS').exists():dirs.append('thys/Relative_ADP')
        else:dirs.extend(str(x.parent.relative_to(source)) for x in sorted((source/'dev/Relative_ADP_Dev').rglob('ROOT')))
        if (source/'thys/RFC_Absolute_Ext/ROOT').exists():dirs.append('thys/RFC_Absolute_Ext')
        selected=targets(row['title'],source)
        if selected:
            cmd=[str(a.isabelle.resolve()),'build','-v','-j','2','-o','threads=8','-o','parallel_proofs=0']+sum((['-d',str(source/d)] for d in dirs),[])+selected
            result=execute(cmd,source,env,run/'build',43200)
        else:result=dict(returncode=0,timed_out=False,scope='No production-source change; formal build not applicable')
        result.update(commit=commit,title=row['title'],targets=selected,source_hashes_sha256=sha(run/'source-hashes.json'))
        result['passed']=result['returncode']==0 and not result['timed_out'];write(run/'result.json',result);receipts.append(result)
        write(out/'summary.json',dict(manifest_sha256=sha(a.manifest),results=receipts,passed=all(r['passed'] for r in receipts),complete=len(receipts)==len(series),scope='Per-feature formal checks; executable regression receipts are recorded separately.'))
        print(json.dumps(dict(patch=number,title=row['title'],passed=result['passed'])),flush=True)
        if not result['passed']:raise SystemExit(1)


if __name__=='__main__':main()
