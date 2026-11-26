#!/usr/bin/env python3
"""Check a freshly generated composed CPF certificate and split mutations."""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser()
for name in ['fixture','ceta','leta','out']:p.add_argument('--'+name,type=Path,required=True)
p.add_argument('--checker',choices=['both','ceta','leta'],default='both');a=p.parse_args()
a.out.mkdir(parents=True,exist_ok=False)
root=Path(__file__).resolve().parents[1];doc=E.parse(str(a.fixture));schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
schema.assertValid(doc);assert doc.find('.//returnSplit') is not None
cases=[('positive',doc,True)]
for tag in ['routing','projection','prefix','continuation','interface','returnVariables']:
    bad=copy.deepcopy(doc);s=bad.find('.//returnSplit');s.remove(s.find(tag));cases.append(('missing-'+tag,bad,False))
for i in [0,1]:
    for tag in ['nodes','contexts','actions']:
        bad=copy.deepcopy(doc);m=bad.find('.//returnSplit').findall('contextModule')[i];m.find(tag).clear()
        cases.append((f'module-{i}-empty-{tag}',bad,False))
binaries={};rows=[]
for who,binary,opts,verdict in [('ceta',a.ceta,['--category','prolog'],'CERTIFIED SOURCE-BOUND PROLOG'),('leta',a.leta,[],'CERTIFIED')]:
    if a.checker not in ['both',who]:continue
    binaries[who]=dict(path=str(binary.resolve()),sha256=hashlib.sha256(binary.read_bytes()).hexdigest())
    for name,tree,expected in cases:
        path=(a.out/(name+'.xml')).resolve();tree.write(str(path),encoding='utf-8')
        valid=schema.validate(tree)
        for repeat in [1,2]:
            cmd=[str(binary.resolve()),*opts,str(path)];r=subprocess.run(cmd,capture_output=True,text=True,timeout=120)
            accepted=r.returncode==0 and r.stdout.strip()==verdict
            row=dict(case=name,checker=who,repeat=repeat,expected=expected,accepted=accepted,schema_valid=valid,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,command=cmd);rows.append(row)
            (a.out/'results.json').write_text(json.dumps(dict(binaries=binaries,fixture=str(a.fixture.resolve()),results=rows),indent=2)+'\n')
            assert r.returncode>=0 and accepted==expected,row
print(len(rows),'fresh split checks passed')
