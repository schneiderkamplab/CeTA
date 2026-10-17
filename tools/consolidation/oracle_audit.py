#!/usr/bin/env python3
"""Strict structural witness/composite scan of frozen search-only guidance.
A successful scan is necessary, not sufficient, for replay eligibility: the
recorded command must also disable fallback and each original root is audited.
"""
import argparse,collections,hashlib,json,pathlib,re
SCHEMA='ferrum.utility-guidance.v2'
FORBIDDEN_ACTION=re.compile(r'exact-|hex\s*=|proof\s*\(|witness|\b(?:seq|choice|repeat|try)\s*\(',re.I)
FORBIDDEN_FIELD=re.compile(r'witness|candidate_ref|proof|payload',re.I)
def audit(path):
    states=set();aliases=[];families=collections.Counter();schemas=collections.Counter();bad=[];count=0;digest=hashlib.sha256()
    def fields(x,line):
        if isinstance(x,dict):
            for k,v in x.items():
                if FORBIDDEN_FIELD.search(k):bad.append(dict(line=line,field=k))
                fields(v,line)
        elif isinstance(x,list):
            for y in x:fields(y,line)
    with path.open('rb') as stream:
        for n,line in enumerate(stream,1):
            digest.update(line);r=json.loads(line);schema=r.get('schema');schemas[schema]+=1
            if schema!=SCHEMA:bad.append(dict(line=n,reason='non-search schema'))
            key=r.get('problem_key')
            if not isinstance(key,str) or not re.fullmatch('[0-9a-f]{64}',key) or key in states:bad.append(dict(line=n,reason='missing malformed or duplicate state'))
            states.add(key);fields(r,n)
            if r.get('canonical_problem_key'):aliases.append((key,r['canonical_problem_key']))
            for bucket in ['prefer','possible','avoid','timeout']:
                for item in r.get(bucket,[]):
                    atom=item.get('candidate','');count+=1
                    if not isinstance(atom,str) or not atom or FORBIDDEN_ACTION.search(atom):bad.append(dict(line=n,action=atom))
                    else:families[re.split(r'\(|\s',atom)[0]]+=1
    return dict(sha256=digest.hexdigest(),schemas=dict(schemas),states=len(states),actions=count,action_families=dict(families),forbidden=bad,unresolved_aliases=[a for a in aliases if a[1] not in states])
def main():
    p=argparse.ArgumentParser();p.add_argument('oracle',type=pathlib.Path);p.add_argument('output',type=pathlib.Path);a=p.parse_args();r=audit(a.oracle);a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='action_families'}));raise SystemExit(bool(r['forbidden'] or r['unresolved_aliases']))
if __name__=='__main__':main()
