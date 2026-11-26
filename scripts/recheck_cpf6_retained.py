#!/usr/bin/env python3
"""Check every retained CPF6 entry twice and audit its original source.

The input inventory must include explicit dispositions for unresolved entries.
Results bind the checker, producer, source, certificate and complete mode/root set.
"""
import argparse,concurrent.futures,hashlib,json,subprocess,time
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser();p.add_argument('--inventory',type=Path,required=True);p.add_argument('--ceta',type=Path,required=True);p.add_argument('--ferrum',type=Path,required=True);p.add_argument('--prolog-audit',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--workers',type=int,default=8);a=p.parse_args()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
schema=E.XMLSchema(E.parse(str(Path(__file__).resolve().parents[1]/'xml/cpf6.xsd')))
a.output.mkdir(parents=True,exist_ok=False);rows=json.loads(a.inventory.read_text());assert len({(r['mode'],r['root']) for r in rows})==len(rows)
pins={n:sha(v) for n,v in [('inventory',a.inventory),('ceta',a.ceta),('ferrum',a.ferrum),('prolog_audit',a.prolog_audit)]}
(a.output/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
def invoke(cmd):
 t=time.monotonic();q=subprocess.run([str(v) for v in cmd],capture_output=True,text=True,timeout=300)
 return dict(command=[str(v) for v in cmd],code=q.returncode,seconds=time.monotonic()-t,stdout=q.stdout,stderr=q.stderr)
def run(r):
 result=dict(id=r['id'],root=r['root'],mode=r['mode'],passed=False)
 try:
  assert sha(r['source'])==r['source_sha256'],'source changed'
  if r['disposition'] in ['baseline-unresolved','unresolved']:return dict(result,passed=True,disposition=r['disposition'])
  assert r['disposition']=='converted',r.get('error');assert sha(r['cpf'])==r['cpf_sha256']
  doc=E.parse(r['cpf'],E.XMLParser(huge_tree=True));schema.assertValid(doc)
  assert doc.findtext('cpfVersion')=='6.0' and doc.find('answer')[0].tag==r['answer'].lower(),'version or polarity mismatch'
  result.update(cpf_sha256=r['cpf_sha256'],source_sha256=r['source_sha256'],constructor=r['constructor'],disposition='certified')
  if r['category']=='Prolog':cmd=[a.prolog_audit,r['source'],r['cpf']]
  else:cmd=[a.ferrum,'logic-programming-cut-audit' if r['constructor'].startswith('lpCut') else 'logic-programming-audit',r['source'],r['cpf']]
  result['audit']=invoke(cmd);assert result['audit']['code']==0,'source audit failed'
  result['checks']=[invoke([a.ceta,'--category','prolog' if r['category']=='Prolog' else 'lp',r['cpf']]) for _ in range(2)]
  assert all(x['code']==0 and x['stdout'].startswith('CERTIFIED') for x in result['checks']),'certification failed'
  result['passed']=True
 except Exception as e:result.update(disposition='failure',error=str(e))
 return result
with (a.output/'results.jsonl').open('w') as log,concurrent.futures.ThreadPoolExecutor(a.workers) as pool:
 results=[]
 for result in pool.map(run,rows):results.append(result);log.write(json.dumps(result)+'\n');log.flush()
summary=dict(passed=all(r['passed'] for r in results),entries=len(rows),certified=sum(r['disposition']=='certified' for r in results),unresolved=sum(r['disposition'] in ['baseline-unresolved','unresolved'] for r in results),failures=[r['id'] for r in results if not r['passed']],pins=pins)
(a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary));raise SystemExit(0 if summary['passed'] else 1)
