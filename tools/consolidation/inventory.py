#!/usr/bin/env python3
"""Inventory pinned objects, never live files. Lexical discovery, not semantic proof."""
import json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT/'docs/consolidation'
def git(*a): return subprocess.check_output(['git','-C',str(ROOT),*a],text=True).strip()
def save(n,x): (OUT/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
    pins=json.loads((OUT/'snapshot.json').read_text()); baseline=pins['baseline']; tips={}
    for repo in pins['development_repositories']:
        for ref,oid in repo['refs'].items(): tips.setdefault(oid,[]).append(repo['repository']+':'+ref)
    main=pins['repositories']['CeTA']['refs']['refs/heads/main']
    csr=pins['repositories']['CeTA-CSR']['refs']['refs/heads/main']
    variants={}; branches=[]; surface=[]
    for tip,refs in sorted(tips.items()):
        changes=[dict(status=l.split('\t')[0],path=l.split('\t')[-1]) for l in git('diff','--name-status',baseline,tip).splitlines()]
        branches.append(dict(commit=tip,refs=refs,changed_files=changes,
            commits_not_in_ceta_main=git('log','--format=%H %s',main+'..'+tip).splitlines(),
            commits_not_in_csr_main=git('log','--format=%H %s',csr+'..'+tip).splitlines()))
        tree={line.split('\t',1)[1]:line.split()[2] for line in git('ls-tree','-r',tip).splitlines()}
        for change in changes:
            path=change['path']
            if path not in tree: continue
            if path.endswith('.thy'):
                oid=tree[path]; key=path+'@'+oid
                if key not in variants:
                    content=git('cat-file','blob',oid); declarations=[]
                    pattern=r'(?m)^\s*(definition|fun|function|primrec|datatype|record|locale|lemma|theorem|corollary|abbreviation)\s+(?:\(in [^)]*\)\s*)?([A-Za-z_][A-Za-z_0-9\x27]*)'
                    for m in re.finditer(pattern,content):
                        declarations.append(dict(kind=m[1],name=m[2],line=content.count('\n',0,m.start())+1))
                    imports=re.search(r'\bimports\s+(.*?)\bbegin\b',content,re.S)
                    xml_tags=sorted(set(re.findall(r"(?:XMLdo|xml_singleton)\s*\(STR ''([^']+)''\)",content)))
                    candidates=[d for d in declarations if d['kind'] in ('definition','fun','function','primrec') and re.search(r'check|_tt$|_dp$|processor|xml2',d['name'])]
                    generated='generated/Haskell/'+pathlib.Path(path).stem+'.hs'
                    variants[key]=dict(path=path,blob=oid,refs=[],declarations=declarations,
                        imports_lexical=imports[1].strip() if imports else None,
                        xml_tags_lexical=xml_tags,checker_candidates=candidates,
                        soundness_candidates=[d for d in declarations if re.search(r'sound|processor|imp_SN|criterion',d['name'])],
                        generated_module=generated,generated_blobs={},
                        coverage_status='gap: no eligible positive or semantic rejection mapped yet',
                        classification='defer pending family assessment and per-branch coverage')
                v=variants[key];v['refs']+=refs
                if v['generated_module'] in tree: v['generated_blobs'][tip]=tree[v['generated_module']]
            if pathlib.Path(path).name in ('ROOT','ROOTS','Makefile') or path.endswith('.hs') and not path.startswith('generated/'):
                surface.append(dict(commit=tip,path=path,blob=tree[path]))
    save('source-inventory.json',dict(schema_version=1,method='Lexical discovery over all changed theories at every pinned tip; names/imports are candidates, not proven semantic maps.',
        baseline=baseline,variants=sorted(variants.values(),key=lambda x:(x['path'],x['blob'])),integration_surface=surface))
    save('branches.json',dict(ceta_main=main,csr_main=csr,merge_base=git('merge-base',main,csr),
        main_only=git('log','--format=%H %s',csr+'..'+main).splitlines(),csr_only=git('log','--format=%H %s',main+'..'+csr).splitlines(),branches=branches))
    counts=dict(unique_theory_variants=len(variants),unique_theory_paths=len({v['path'] for v in variants.values()}),
        pinned_tips=len(tips),checker_candidates=sum(len(v['checker_candidates']) for v in variants.values()),
        eligible_positive_proofs=0,verified_negative_tests=0,instrumented_checker_branches=None,
        minimum_cardinality_proved=False,stage='assessment only',
        gaps=['Every lexical checker candidate requires a context-sensitive processor/theorem/CPF map.',
              'No candidate is admitted before provenance, input correspondence and twice checking.',
              'HPC instrumentation and production agreement are not measured.',
              'Relative and outermost strict witness-free replay provenance remains to be established.',
              'No semantic equivalence or deletion is established by this lexical inventory.'])
    save('coverage-gaps.json',counts); print(json.dumps(counts))
if __name__=='__main__':main()
