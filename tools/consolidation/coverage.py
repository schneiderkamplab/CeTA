#!/usr/bin/env python3
"""CPF structural coverage and explicit gaps, separate from instrumented execution.
The structural contexts below are syntactic observations, not reconstructed
semantic DP states. Unmapped state transitions remain gates on restructuring.
"""
import argparse,collections,gzip,hashlib,json,pathlib,re,subprocess,xml.etree.ElementTree as ET
ROOT=pathlib.Path(__file__).resolve().parents[2];REV='17dbee4b822733cd25235a64178db2ccf590a10e'
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args]).decode('latin1')
def registry():
    paths=git('ls-tree','-r','--name-only',REV).splitlines();texts={};known=set();branches=collections.defaultdict(list)
    for path in paths:
        if not path.endswith('.thy') or not path.startswith(('thys/','dev/')):continue
        # All executable checker/parser theories and their imported semantic families.
        if not any(s in path for s in ('Checker','Check_','Parser','RFC_Absolute','Relative_ADP_Ceta')):continue
        text=git('show',REV+':'+path);texts[path]=text
        if 'Parser' in path or 'Relative_ADP_Ceta' in path or 'RFC_Absolute' in path:
            known.update(re.findall(r"STR ''([A-Za-z][A-Za-z0-9_-]*)''",text))
        for m in re.finditer(r'"(check_[\w]+)[^"=\n]*(?:\n[^"=]*)?=',text):
            equation=m[0];constructors=re.findall(r'\(([A-Z][A-Za-z_0-9]+)\b',equation)
            for c in constructors:
                if c in {'STR','Some','None','True','False','Fun','Var','Inl','Inr','Pair','Left','Right'}:continue
                ds=re.findall(r'(?m)^(?:lemma|theorem|corollary)\s+(?:\(in [^)]*\)\s*)?([A-Za-z_0-9]+)',text)
                sound=[d for d in ds if m[1] in d]
                branches[c].append(dict(theory=path,checker=m[1],line=text.count('\n',0,m.start())+1,theorems=sound,status='driver correspondence; criterion premises require explicit mapping'))
    tags=collections.defaultdict(list)
    for path,text in texts.items():
        if not ('Parser' in path or 'Relative_ADP_Ceta' in path or 'RFC_Absolute' in path):continue
        for m in re.finditer(r"XMLdo\s*\(STR ''([A-Za-z][A-Za-z0-9_-]*)''\)\s*\{",text):
            depth=1;j=m.end()
            while j<len(text) and depth:
                depth+=(text[j]=='{')-(text[j]=='}');j+=1
            body=text[m.end():j-1]
            returns=list(re.finditer('xml_return',body))
            if not returns:continue
            returned=body[returns[-1].end():]
            cs=sorted(set(re.findall(r'\b[A-Z][A-Za-z_0-9]+\b',returned))&branches.keys())
            if cs:tags[m[1]].append(dict(parser_theory=path,parser_line=text.count('\n',0,m.start())+1,constructors=cs,checker_branches=[b for c in cs for b in branches[c]]))
    return dict(revision=REV,structural_schema_version=2,known_xml_tags=sorted(known),processor_candidates=dict(tags),limitations=['Lexical links require review; runtime execution never executes Isabelle theorems.','Nested DP state transformations are not inferred from tag names.'])

def inspect(path,category,reg):
    known=set(reg['known_xml_tags']);processors=reg['processor_candidates'];features=set();unknown=collections.Counter();observed=collections.Counter();nodes=[];stack=[];child_counts=[];proof_depth=None;frames=[];version=reg.get('structural_schema_version',1)
    wrappers={'proof','trsTerminationProof','dpProof','dpTerminationProof','trsNonterminationProof','dpNonterminationProof','csrTerminationProof','csrDpTerminationProof','csrDpProof','relativeAdpTerminationProof','csrGuardedTerminationProof','csrImprovedDpProof','csrMutermTypedDpProof'}
    with (gzip.open(path,'rb') if str(path).endswith('.gz') else path.open('rb')) as f:
        for event,node in ET.iterparse(f,events=('start','end')):
            if event=='start':
                if child_counts:child_counts[-1]+=1
                child_counts.append(0);stack.append(node);frames.append(None)
                if len(stack)==2 and node.tag=='proof':proof_depth=2
                if proof_depth:
                    tag=node.tag
                    if version>=2:
                        if tag in wrappers:
                            for frame in frames[:-1]:
                                if frame is not None:frame['has_child_proof']=True
                        if len(stack)>=3 and stack[-2].tag in {'domain','type','criterion'}:
                            features.add('representation|'+category+'|'+stack[-3].tag+'/'+stack[-2].tag+'='+tag)
                    if tag not in known and tag not in wrappers:unknown[tag]+=1
                    context_tags=[x.tag for x in stack[:-1]]
                    data_only=(tag=='usableRules' and not any('complexity' in t.lower() for t in context_tags))
                    if tag in processors and not data_only:
                        ancestor_tags=[x.tag for x in stack[2:-1]]
                        proof_ancestors=[t for t in ancestor_tags if t in processors]
                        placement='root' if not proof_ancestors else 'nested'
                        container=next((t for t in reversed(ancestor_tags) if t in wrappers),'proof')
                        key='cpf|'+category+'|'+container+'|'+placement+'|'+tag
                        features.add(key);observed[tag]+=1
                        # Ordered parent-child composition, distinct from tag presence.
                        if proof_ancestors:features.add('composition|'+category+'|'+proof_ancestors[-1]+'>'+tag)
                        frame=dict(tag=tag,container=container,placement=placement,ancestor_processors=proof_ancestors)
                        if version>=2:frame['has_child_proof']=False;frames[-1]=frame
                        nodes.append(frame)
                continue
            if proof_depth:
                if version>=2 and frames[-1] is not None:
                    frame=frames[-1];features.add('flow|'+category+'|'+frame['container']+'|'+frame['tag']+'|'+('recursive' if frame['has_child_proof'] else 'terminal'))
                # Record explicit representations and boundary syntax without pretending
                # they are the complete semantic context of a nested obligation.
                if node.tag in {'minimal','nfs','dimension','domain','type','strictDimension'}:
                    value=(node.text or '').strip()
                    if value and len(value)<80:features.add('representation|'+category+'|'+node.tag+'='+value)
                if node.tag in {'rules','dps','usableRules','innermostLhss','replacementMap'}:
                    features.add('boundary|'+category+'|'+node.tag+'|'+('nonempty' if child_counts[-1] else 'empty'))
                if len(stack)==proof_depth:proof_depth=None
            # Free all nodes as the streaming pass advances. Boundary emptiness
            # uses child placeholders retained until parent end, not full subtrees.
            node.clear()
            if len(stack)>1:stack[-2].remove(node)
            stack.pop();child_counts.pop();frames.pop()
    return dict(features=sorted(features),processor_counts=dict(observed),unknown_proof_tags=dict(unknown),nodes=nodes,semantic_context_gaps=['Exact nested P/Pw/Q/R/Rw, minimality and replacement-map transition reconstruction pending per processor.'])

def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',required=True);p.add_argument('--registry-only',action='store_true');a=p.parse_args();stage=ROOT/'target/consolidation-corpus'/a.stage
    reg=registry();(stage/'processor-registry.json').write_text(json.dumps(reg,indent=2,sort_keys=True)+'\n')
    if a.registry_only:print('Processor tags',len(reg['processor_candidates']));return
    rows=[json.loads(l) for l in (stage/'results.jsonl').read_text().splitlines()];results=[]
    for row in rows:
        if not row['eligible']:continue
        result=inspect(stage/row['id']/'proof.cpf.xml',row['category'],reg);result['id']=row['id'];result['root']=row['root']
        (stage/row['id']/'structural-coverage.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');results.append(result)
    summary=dict(roots=len(results),features=sorted({x for r in results for x in r['features']}),unknown_tags=sorted({x for r in results for x in r['unknown_proof_tags']}),semantic_coverage='partial structural observations only; exact context mapping gaps retained')
    (stage/'structural-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n');print(json.dumps(summary))
if __name__=='__main__':main()
