#!/usr/bin/env python3
"""Semantic mutations paired with accepted real ADP frontier certificates."""
import argparse,gzip,json,os,pathlib,xml.etree.ElementTree as ET
from replay import execute,certified,sha,write


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['manifest','checker','output']:
        p.add_argument('--'+key,type=pathlib.Path,required=True)
    p.add_argument('--hpc-checker',type=pathlib.Path)
    a=p.parse_args(); manifest=a.manifest.resolve();base=manifest.parent
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    binaries=[a.checker.resolve()]+([a.hpc_checker.resolve()] if a.hpc_checker else [])
    env={k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')};results=[]
    for row in json.loads(manifest.read_text())['roots']:
        if not row.get('new_nodes'):continue
        run=out/row['id'];run.mkdir();proof=run/'proof.cpf.xml'
        proof.write_bytes(gzip.decompress((base/row['id']/'proof.cpf.xml.gz').read_bytes()))
        if sha(proof)!=row['proof_sha256']:raise ValueError('Source certificate changed')
        source=[]
        for i,binary in enumerate(binaries):
            prefix=run/('source-'+str(i));c=execute([str(binary),str(proof)],run,env|{'HPCTIXFILE':str(run/'source.tix')},prefix,1200)
            c['certified']=certified(c,prefix);source.append(c)
        if not all(c['certified'] for c in source):raise ValueError('Mutation source not accepted: '+row['id'])
        for name,tag,diagnostic in [('missing-graph-child','relativeAdpRootDependencyGraph','relative ADP graph child count mismatch'),('invalid-filter-position','relativeAdpFilteredDerelatification','invalid DP argument filter')]:
            tree=ET.parse(proof)
            if name=='missing-graph-child':
                node=next((x for x in tree.iter(tag) if len(x)),None)
                if node is None:continue
                node.remove(node[0])
            else:
                node=tree.find('.//'+tag+'/argumentFilter//position')
                if node is None:continue
                node.text='999999'
            path=run/(name+'.xml');tree.write(path);checks=[]
            for i,binary in enumerate(binaries):
                prefix=run/(name+'-'+str(i));c=execute([str(binary),str(path)],run,env|{'HPCTIXFILE':str(run/'negative.tix')},prefix,1200)
                text=prefix.with_suffix('.stdout').read_text()+prefix.with_suffix('.stderr').read_text()
                c['semantic_rejection']=c['returncode']==1 and not c['timed_out'] and text.startswith('REJECTED') and diagnostic in text
                checks.append(c)
            results.append(dict(id=row['id'],root=row['root'],source_sha256=row['proof_sha256'],mutation_sha256=sha(path),mutation=name,diagnostic=diagnostic,source_checks=source,checks=checks,passed=all(c['semantic_rejection'] for c in checks)))
        (run/'negative.tix').unlink(missing_ok=True)
    covered={r['mutation'] for r in results}
    required={'missing-graph-child','invalid-filter-position'}
    report=dict(manifest_sha256=sha(manifest),checker_sha256=sha(a.checker),results=results,gaps=sorted(required-covered),passed=bool(results) and covered==required and all(r['passed'] for r in results))
    write(out/'summary.json',report);print(json.dumps(dict(cases=len(results),passed=report['passed'],gaps=report['gaps'])))
    raise SystemExit(not report['passed'])


if __name__=='__main__':main()
