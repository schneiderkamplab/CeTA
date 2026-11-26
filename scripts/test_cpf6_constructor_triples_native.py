#!/usr/bin/env python3
"""Focused native integration gate; not an oracle replay or coverage census."""
import argparse,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser();p.add_argument('--ceta',type=Path,required=True);p.add_argument('--leta',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--checker',choices=['both','ceta','leta'],default='both');a=p.parse_args()
if a.checker in ("both","leta") and a.leta is None:p.error("--leta is required for the selected checker")
a.out.mkdir(parents=True,exist_ok=False)
root=Path(__file__).resolve().parents[1]
fixture=(root/'tests/fixtures/cpf6-constructor-triples/positive.xml').read_text()
mutations=[('version','6.0','5.0'),('answer','<yes/>','<no/>'),('profile','iso-rational-libraries-v1','other'),('source-query','<predicate>p</predicate>','<predicate>other</predicate>'),('child-query','<query><name>chain</name>','<query><name>other</name>'),('region-root','<root>0</root>','<root>1</root>'),('region-fuel','<fuel>16</fuel><root>','<fuel>15</fuel><root>'),('contexts','<contexts><sourceContext><facts/><guards/><observations/></sourceContext></contexts>','<contexts/>'),('rank','<value>2</value>','<value>0</value>'),('action','<cut><terminal/></cut>','<boundary/>'),('link','<target>2</target>','<target>0</target>'),('child-arity','<arity>0</arity>','<arity>1</arity>'),('extra','</proof>','<extra/></proof>')]
assert all(old in fixture for _,old,_ in mutations)
cases=[('positive',fixture,True)]+[(name,fixture.replace(old,new),False) for name,old,new in mutations]
schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
rows=[];binaries={}
for binary in ([a.ceta,a.leta] if a.checker=='both' else [a.ceta if a.checker=='ceta' else a.leta]):binaries[str(binary.resolve())]=hashlib.sha256(binary.read_bytes()).hexdigest()
for name,xml,expected in cases:
    path=(a.out/(name+'.xml')).resolve();path.write_text(xml)
    valid=schema.validate(E.fromstring(xml.encode()))
    if expected:assert valid
    for who,binary,opts,verdict in [('ceta',a.ceta,['--category','prolog'],'CERTIFIED SOURCE-BOUND PROLOG'),('leta',a.leta,[],'CERTIFIED')]:
        if a.checker != 'both' and who != a.checker:continue
        for repeat in [1,2]:
            cmd=[str(binary.resolve()),*opts,str(path)]
            q=subprocess.run(cmd,capture_output=True,text=True,timeout=120)
            accepted=q.returncode==0 and q.stdout.strip()==verdict
            row=dict(case=name,checker=who,repeat=repeat,expected=expected,accepted=accepted,schema_valid=valid,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,command=cmd)
            rows.append(row)
            (a.out/'results.json').write_text(json.dumps(dict(binaries=binaries,results=rows),indent=2)+'\n')
            assert q.returncode >= 0, row
            assert accepted==expected,row
print(len(rows),'native checks passed; focused fixture gate only')
