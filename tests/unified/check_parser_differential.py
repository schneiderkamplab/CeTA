#!/usr/bin/env python3
"""Compare complete old/new XML/CPF results, including malformed documents."""
import argparse, concurrent.futures, gzip, hashlib, json, subprocess, tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--before',type=Path,required=True);p.add_argument('--after',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();binaries=[str(x.resolve()) for x in (a.before,a.after)]
base=Path(__file__).resolve().parents[1]/'certification/compact'
m=json.loads((base/'manifest.json').read_text())
sources=[]
for row in m['negatives'][:12]:
 data=gzip.decompress((base/row['certificate']).read_bytes()).decode()
 sources.extend([('semantic',data),('truncated',data[:-20]),('unknown-tag',data.replace('<proof>','<unexpected>')),('unknown-entity',data.replace('<cpfVersion>','<cpfVersion>&bogus;')),('escaped-text',data.replace('<name>','<name>a&amp;&lt;&gt;&quot;&apos;')),('significant-space',data.replace('<name>','<name> ')),('attribute',data.replace('<proof>','<proof unexpected="yes">'))])
sources.extend((label,text) for label,text in [('empty',''),('text','hello'),('unclosed','<x>'),('mismatch','<x></y>'),('comment','<!-- test --><x/>'),('doctype','<!DOCTYPE x><x/>'),('cdata','<x><![CDATA[a&b]]></x>'),('pi','<?xml version="1.0"?><x/>'),('text-tail','<x/>tail'),('duplicate-root','<x/><x/>'),('empty-name','<>'),('entity','<x>&amp;</x>')])
def run(item):
 label,data=item
 with tempfile.TemporaryDirectory() as d:
  f=Path(d)/'proof.xml';f.write_text(data)
  results=[]
  for binary in binaries:
   r=subprocess.run([binary,str(f)],capture_output=True,text=True)
   results.append(dict(returncode=r.returncode,stdout=r.stdout,stderr=r.stderr))
 return dict(case=label,sha256=hashlib.sha256(data.encode()).hexdigest(),equal=results[0]==results[1],results=results)
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:rows=list(pool.map(run,sources))
report=dict(binary_sha256=[hashlib.sha256(Path(b).read_bytes()).hexdigest() for b in binaries],cases=len(rows),equal=sum(r['equal'] for r in rows),results=rows)
a.output.write_text(json.dumps(report,indent=2)+'\n');print(report['equal'],'/',report['cases']);assert all(r['equal'] for r in rows)
