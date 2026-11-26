#!/usr/bin/env python3
"""Convert pinned historical ITS/HO certificates to CPF5 and audit source binding."""
import argparse,concurrent.futures,hashlib,json,re,subprocess,sys
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser();p.add_argument('--inventory',type=Path,required=True);p.add_argument('--ferrum-source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--workers',type=int,default=8);a=p.parse_args();assert 1<=a.workers<=32
a.output.mkdir(parents=True,exist_ok=False);root=Path(__file__).resolve().parents[1];ferrum=a.ferrum_source.resolve()/'target/release/ferrum';converter=ferrum.parent/'examples/cpf5_higher_order';sys.path.insert(0,str(a.ferrum_source.resolve()/'scripts'));from audit_higher_order_native import source_matches
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();schema=E.XMLSchema(E.parse(str(root/'xml/cpf5.xsd')));inventory=json.loads(a.inventory.read_text());jobs=[r for r in inventory['rows'] if r['certified']];pins=dict(inventory_sha256=sha(a.inventory),ferrum_sha256=sha(ferrum),converter_sha256=sha(converter));(a.output/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
def run(index_row):
 i,r=index_row;row=dict(r);out=a.output/f'{i:04d}.xml'
 try:
  assert sha(Path(r['proof']))==r['proof_sha256'];assert sha(Path(r['source']))==r['source_sha256']
  if r['category']=='Higher_Order_Rewriting':
   cmd=[str(converter),r['proof']]
   if r.get('child'):assert sha(Path(r['child']))==r['child_sha256'];cmd.append(r['child'])
   q=subprocess.run(cmd,capture_output=True,timeout=300);assert q.returncode==0,q.stderr.decode();out.write_bytes(q.stdout);row['conversion_command']=cmd
  else:
   raw=Path(r['proof']).read_text();new,n=re.subn(r'(<cpfVersion>).*?(</cpfVersion>)',r'\g<1>5.0\g<2>',raw);assert n==1;out.write_text(new)
   row['conversion']='Only cpfVersion changed to 5.0'
  doc=E.parse(str(out),E.XMLParser(huge_tree=True));schema.assertValid(doc);assert doc.findtext('cpfVersion')=='5.0';assert doc.find('answer')[0].tag==r['expected']
  if r['category']=='Higher_Order_Rewriting':assert source_matches(Path(r['source']).read_text(),out.read_text(),r['expected'])
  else:
   cmd=[str(ferrum),'its-audit',r['source'],str(out.resolve())];q=subprocess.run(cmd,capture_output=True,text=True,timeout=60);row['audit_command']=cmd;row['audit_stdout']=q.stdout;assert q.returncode==0,q.stderr
  row.update(passed=True,certificate=str(out.resolve()),certificate_sha256=sha(out),schema_valid=True,source_audit=True)
 except Exception as e:row.update(passed=False,error=repr(e))
 return row
rows=[]
with (a.output/'results.jsonl').open('w') as journal,concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
 for row in pool.map(run,enumerate(jobs)):
  rows.append(row);journal.write(json.dumps(row)+'\n');journal.flush()
  if len(rows)%100==0:print(len(rows),'/',len(jobs),flush=True)
assert sha(ferrum)==pins['ferrum_sha256'] and sha(converter)==pins['converter_sha256']
r=dict(pins=pins,required=len(jobs),passed=sum(r['passed'] for r in rows),failures=[r for r in rows if not r['passed']],unresolved=sum(not r['certified'] for r in inventory['rows']));(a.output/'summary.json').write_text(json.dumps(r,indent=2)+'\n');print(r['passed'],'/',len(jobs));assert not r['failures']
