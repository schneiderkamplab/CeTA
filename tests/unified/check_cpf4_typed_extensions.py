#!/usr/bin/env python3
"""Gate the four typed-CSR XML extensions on a nonempty typed DP obligation."""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--checker',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
root=Path(__file__).resolve().parents[2];checker=a.checker.resolve();schema=E.XMLSchema(E.parse(str(root/'xml/cpf4.xsd')));rows=[]
for source in sorted(Path(__file__).with_name('cpf4-typed-extensions').glob('*.xml')):
 d=E.parse(str(source));schema.assertValid(d)
 # Expansion uses string_renameN: the selected pairs must name x0_x.
 mutations=['positive','false-pair','missing-invariant']
 if source.stem.startswith('expanded'):mutations.append('unexpanded-pair-reference')
 for mutation in mutations:
  m=copy.deepcopy(d)
  if mutation=='false-pair':
   pair=m.find('input/csrMutermTypedDpInput/dps/rules/rule');pair.remove(pair[1]);pair.append(copy.deepcopy(pair[0]))
  elif mutation=='unexpanded-pair-reference':
   for v in m.findall('proof//dps//var'):v.text='x'
  elif mutation=='missing-invariant':m.find('input/csrMutermTypedDpInput/minimal').text='false'
  schema.assertValid(m);path=a.output/(source.stem+'-'+mutation+'.xml');path.write_bytes(E.tostring(m));expected=mutation=='positive'
  for repeat in [1,2]:
   q=subprocess.run([str(checker),str(path)],capture_output=True,text=True,timeout=30);accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED'
   rows.append(dict(form=source.stem,mutation=mutation,repeat=repeat,expected=expected,accepted=accepted,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
r=dict(checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),checks=rows,passed=all(r['expected']==r['accepted'] for r in rows));(a.output/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print(len(rows),r['passed']);print([(r['form'],r['mutation']) for r in rows if r['expected']!=r['accepted']]);assert r['passed']
