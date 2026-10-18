#!/usr/bin/env python3
"""Reconstruct all consolidation changes against the pinned main prerequisite.

Never changes a branch or the working index. Exact application is checked at
EVERY patch. Build validation is a separate receipt, never inferred from apply.
The target excludes the subsequently committed series artifacts themselves.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[2]


def git(*args,env=None,data=None):
    return subprocess.check_output(['git',*args],cwd=ROOT,env=env,input=data)


def ordinary_stage(full,keep):
    text=full
    for feature,constructor,number in [('rule','Rule_Strengthening',54),('qdp','Zantema_To_SRS_Proc',53)]:
        if feature in keep:continue
        text=re.sub(r'^\| '+constructor+r'[^\n]*\n','',text,flags=re.M)
        text=re.sub(r'^\| "(?:sn|dp)_assms [^\n]*\('+constructor+r'[^\n]*\n','',text,flags=re.M)
        pattern=r'^\| "check_(?:trs|dp)_termination_proof [^\n]*\('+constructor+r'[^\n]*\n.*?(?=^\| |^  by pat_completeness)'
        text,n=re.subn(pattern,'',text,flags=re.M|re.S)
        if n!=1:raise ValueError('Processor equation boundary changed: '+feature)
        pattern=r'^next\n  case \('+str(number)+r' [^\n]*\n.*?(?=^next\n|^qed\n)'
        text,n=re.subn(pattern,'',text,flags=re.M|re.S)
        if n!=1:raise ValueError('Soundness case boundary changed: '+feature)
    if 'qdp' not in keep:text=text.replace(' QDP_To_SRS_Zantema','')
    if 'rule' not in keep:text=text.replace(' Rule_Strengthening\n','\n')
    return text.encode()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--target',required=True)
    p.add_argument('--parent-feature',default='8259236')
    p.add_argument('--root-feature',required=True)
    p.add_argument('--filter-feature',required=True)
    p.add_argument('--promotion-feature')
    p.add_argument('--output',type=pathlib.Path,required=True)
    a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    base=git('rev-parse','e52c7ce').decode().strip();target=git('rev-parse',a.target).decode().strip()
    def content(rev,path):return git('show',rev+':'+path)
    def paths(rev,prefix):return [x for x in git('ls-tree','-r','--name-only',rev).decode().splitlines() if x.startswith(prefix)]
    def changed(before,after):return git('diff','--name-only','--no-renames',before,after).decode().splitlines()
    stages=[]
    def add(title,rev,names,overrides=None):
        if names:stages.append((title,rev,names,overrides or {}))
    ct='thys/Proof_Checker_Base/Check_Termination.thy';rootbase=content(base,'thys/ROOT').decode();root85=content('85b6876','thys/ROOT').decode()
    marker='session Proof_Checker_Base ';end='session CSR_Checker_Base '
    section=root85[root85.index(marker):root85.index(end)]
    full=content('85b6876',ct).decode()
    for title,keep,theory in [('AAECC full-to-innermost criterion',set(),'thys/CSR_Checker/AAECC/AAECC_Innermost_Switch.thy'),('Zantema QDP-to-SRS criterion',{'qdp'},'thys/Proof_Checker_Base/QDP_To_SRS_Zantema.thy'),('General rule strengthening',{'qdp','rule'},'thys/Proof_Checker_Base/Rule_Strengthening.thy')]:
        rootsection=section if 'qdp' in keep else section.replace('    QDP_To_SRS_Zantema\n','')
        stage_root=rootbase[:rootbase.index(marker)]+rootsection+rootbase[rootbase.index(end):]
        add(title,'85b6876',[theory,ct,'thys/ROOT']+(['thys/Proof_Checker/CSR_Muterm_Typed_Checker.thy','thys/CSR_Checker/Extensions/CSR_Minimal_CSDP_Proofs.thy'] if keep=={'qdp'} else []),{ct:ordinary_stage(full,keep),'thys/ROOT':stage_root.encode()})
    pc='thys/Proof_Checker/'
    add('Full and complete GM04 transformation semantics','85b6876',[pc+n+'.thy' for n in ['GM04_Sanitizing_Phase','GM04_Full_Transformation','GM04_Complete_Transformation','GM04_Complete_Checker']])
    add('Standalone CSR and GM04 residual interfaces','85b6876',[pc+n+'.thy' for n in ['GM04_Standalone_DP_Checker','CSR_Standalone_DP_Checker','Ceta_Problem_Spec','Proof_Checker']])
    add('CPF adapters for transformation and residual certificates','85b6876',[pc+'CPF_Input_Parser.thy',pc+'CPF_Proof_Parser.thy'])
    add('Shared production export configuration','85b6876',[pc+'Code_Haskell_Configuration.thy',pc+'Code_CSR_Production.thy','thys/Code/Code_Haskell.thy','thys/ROOT','dev/Relative_ADP_Dev/Integration/Relative_ADP_Code_Haskell.thy'])
    add('RFC deletion with absolute residual checking','85b6876',paths('85b6876','thys/RFC_Absolute_Ext/'))
    add('Isolated build and compatible checker command lines','85b6876',['Makefile','src/Haskell/Main_RFC.hs','src/Haskell/Main_Relative_ADP.hs'])
    reloc=[x for x in changed('85b6876','1b655c5') if x.startswith(('thys/Relative_ADP/','dev/Relative_ADP_Dev/'))]
    add('Production ADP organization and shared proof interfaces','1b655c5',reloc)
    parent_changed=bool(changed('8259236',a.parent_feature))
    if parent_changed:
        add('Reuse the verified ordinary heap for ADP integration',a.parent_feature,['thys/Relative_ADP/Integration/ROOT','thys/Relative_ADP/Integration/Base/Relative_ADP_Integration_Base.thy'])
    add('Shared outermost RZ validation interface','1b655c5',['thys/Outermost_RZ_Ext/Outermost_RZ_Checker.thy','thys/Outermost_RZ_Ext/Outermost_RZ_Checker_Tests.thy','thys/ROOT'])
    csr='thys/CSR_Checker/'
    add('Specialize finite conservative coverage','7e9ac72',[csr+'Extensions/CSR_Improved_CSDP_Proofs.thy'])
    add('Share guarded rank and endpoint corollaries','7e9ac72',[csr+'Guarded_List_Measure_Check/CSR_Guarded_List_Measure.thy'])
    add('Share non-strict endpoint tail reasoning','9876673',[csr+'Guarded_List_Measure_Check/CSR_Guarded_List_Measure.thy'])
    add('Factor usable-rule pair-set restriction','9876673',[csr+'Muterm_Ext/CSR_Muterm_Innermost_Usable_Exec.thy'])
    add('Share root and residual CSR representations','9876673',[csr+'Extensions/CSR_Conservative_Checker.thy',csr+'Guarded_List_Measure_Check/CSR_Guarded_List_Checker.thy',pc+'CSR_Standalone_DP_Checker.thy',pc+'CSR_GM_Transformation.thy'])
    adp='thys/Relative_ADP/'
    add('Generalize compound ADP orders with explicit argument strictness','8259236',[adp+'Checker/Relative_ADP_Checker_Adapter.thy',adp+'Checker/Relative_ADP_Checker_Tests.thy']+paths('8259236',adp+'Semantics/Reduction_Pair/'))
    add('Recursive split checking through the RFC engine','8259236',['thys/RFC_Absolute_Ext/RFC_Absolute_Check.thy'])
    add('Full termination to outermost bridge','8259236',['thys/RFC_Absolute_Ext/RFC_Absolute_Cert.thy'])
    add('Single-parse ordinary and ADP dispatch','8259236',paths('8259236',adp+'Integration/'),
        {adp+'Integration/ROOT':content(a.parent_feature,adp+'Integration/ROOT')} if parent_changed else {})
    add('Root-sensitive ADP graphs through one shared estimator engine',a.root_feature,[x for x in changed(a.parent_feature,a.root_feature) if x.startswith('thys/')])
    add('Argument-filtered nonminimal ADP derelatification',a.filter_feature,[x for x in changed(a.root_feature,a.filter_feature) if x.startswith('thys/')])
    if a.promotion_feature:
        add('Relative rule promotion through the shared ADP root checker',a.promotion_feature,[x for x in changed(a.filter_feature,a.promotion_feature) if x.startswith('thys/')])
    add('Regenerate verified Haskell exports',target,sorted(set(paths(base,'generated/')) | set(paths(target,'generated/'))))
    with tempfile.TemporaryDirectory(prefix='feature-series-',dir=ROOT/'target') as tmp:
        env=dict(os.environ,GIT_INDEX_FILE=tmp+'/index',GIT_AUTHOR_NAME='CeTA consolidation',GIT_AUTHOR_EMAIL='consolidation@example.invalid',GIT_COMMITTER_NAME='CeTA consolidation',GIT_COMMITTER_EMAIL='consolidation@example.invalid',GIT_AUTHOR_DATE='2026-10-18T12:00:00+00:00',GIT_COMMITTER_DATE='2026-10-18T12:00:00+00:00')
        git('read-tree',base,env=env);parent=base;records=[]
        def emit(title,rev,names,overrides):
            nonlocal parent
            tree_paths=set(git('ls-tree','-r','--name-only',rev).decode().splitlines())
            for name in names:
                if name not in tree_paths and name not in overrides:git('update-index','--force-remove','--',name,env=env);continue
                data=overrides[name] if name in overrides else content(rev,name)
                blob=git('hash-object','-w','--stdin',data=data).decode().strip()
                mode=git('ls-tree',rev,'--',name).decode().split()[0]
                git('update-index','--add','--cacheinfo',mode,blob,name,env=env)
            tree=git('write-tree',env=env).decode().strip()
            if tree==git('rev-parse',parent+'^{tree}').decode().strip():raise ValueError('Empty feature: '+title)
            commit=git('commit-tree',tree,'-p',parent,env=env,data=(title+'\n').encode()).decode().strip()
            patch=git('format-patch','--stdout','--no-signature','--full-index','--binary','-1',commit)
            filename=f'{len(records)+1:04d}-'+re.sub(r'[^a-z0-9]+','-',title.lower()).strip('-')+'.patch';(out/filename).write_bytes(patch)
            records.append(dict(title=title,file=filename,sha256=hashlib.sha256(patch).hexdigest(),commit=commit,parent=parent,tree=tree,paths=names,build_validation=None))
            parent=commit
        for stage in stages:emit(*stage)
        remaining=git('diff','--name-only','--no-renames',parent,target).decode().splitlines()
        unexpected=[x for x in remaining if x.startswith(('thys/','dev/','src/','generated/')) or x=='Makefile']
        if unexpected:raise ValueError('Unassigned production changes: '+repr(unexpected))
        if remaining:emit('Freeze regression tools corpora and verification evidence',target,remaining,{})
        expected=git('rev-parse',target+'^{tree}').decode().strip()
        if records[-1]['tree']!=expected:raise ValueError('Series does not reproduce complete target tree')
        git('read-tree',base,env=env)
        for row in records:
            patch=(out/row['file']).read_bytes();git('apply','--cached','--check',env=env,data=patch);git('apply','--cached',env=env,data=patch)
            if git('write-tree',env=env).decode().strip()!=row['tree']:raise ValueError('Intermediate apply mismatch')
    report=dict(base=base,base_description='Pinned CeTA main at consolidation start; inherited pre-consolidation features are prerequisites.',upstream_ceta_39_base='8e6e5f9',target=target,final_tree=expected,series=records,complete_target_tree=True,exact_apply_verified=True,independent_builds_verified=False,status='Complete consolidation delta; independent intermediate builds pending. Not a CeTA 3.9 prerequisite reconstruction.')
    (out/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Exactly applied',len(records),'feature patches; full target tree matched')


if __name__=='__main__':main()
