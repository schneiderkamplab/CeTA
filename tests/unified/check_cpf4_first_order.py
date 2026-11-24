#!/usr/bin/env python3
"""CPF 4 first-order parser, schema, dispatch and semantic rejection gate."""
import argparse,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser();p.add_argument('--checker',type=Path,required=True);p.add_argument('--fixtures',type=Path,default=Path(__file__).with_name('cpf4-first-order'));p.add_argument('--output',type=Path,required=True);a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=False)
checker=a.checker.resolve();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();identity=sha(checker)
schema=E.XMLSchema(E.parse(str(Path(__file__).resolve().parents[2]/'xml/cpf4.xsd')))
rows=[]
for kind,stem,flags in [('cycle','cycle',[]),('conditional','conditional',['--ordinary']),('conditional','conditional-operational',[])]:
 text=(a.fixtures/(stem+'.xml')).read_text();schema.assertValid(E.fromstring(text.encode()))
 cases=[('valid',text,True),('wrong-answer',text.replace('<no/>','<yes/>'),False),('wrong-version',text.replace('>4.0<','>3.0<'),False),('wrong-property',text.replace('<termination/>','<operationalTermination/>') if '<termination/>' in text else text.replace('<operationalTermination/>','<termination/>'),False),('trailing',text+'garbage',False),('extra-field',text.replace('</proof>','<extra/></proof>'),False),('negative-index',text.replace('<ruleIndex>0</ruleIndex>','<ruleIndex>-1</ruleIndex>'),False),('invalid-rule',text.replace('<ruleIndex>0</ruleIndex>','<ruleIndex>999999</ruleIndex>'),False)]
 for name,xml,expected in cases:
  dest=a.output/(stem+'-'+name+'.xml');dest.write_text(xml)
  command=[str(checker),'--category',kind,*flags,str(dest.resolve())]
  q=subprocess.run(command,capture_output=True,text=True,timeout=30)
  accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED'
  rows.append(dict(category=kind,name=name,expected=expected,passed=accepted==expected,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,command=command))
text=(a.fixtures/'erasure.xml').read_text();schema.assertValid(E.fromstring(text.encode()))
root=E.fromstring(text.encode());child=root.find('proof/conditionalErasureProof/trsTerminationProof');child.clear();E.SubElement(child,'rIsEmpty')
for name,xml,expected in [('valid',text,True),('wrong-answer',text.replace('<yes/>','<no/>'),False),('wrong-version',text.replace('>4.0<','>3.0<'),False),('wrong-property',text.replace('<termination/>','<operationalTermination/>'),False),('false-empty-proof',E.tostring(root).decode(),False)]:
 dest=a.output/('erasure-'+name+'.xml');dest.write_text(xml)
 command=[str(checker),'--category','conditional-erasure',str(dest.resolve())]
 q=subprocess.run(command,capture_output=True,text=True,timeout=30)
 accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED'
 rows.append(dict(category='conditional-erasure',name=name,expected=expected,passed=accepted==expected,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,command=command))
assert sha(checker)==identity
result=dict(checker_sha256=identity,passed=all(r['passed'] for r in rows),cases=rows)
(a.output/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cases'}))
raise SystemExit(0 if result['passed'] else 1)
