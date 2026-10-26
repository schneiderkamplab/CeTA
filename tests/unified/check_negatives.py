#!/usr/bin/env python3
"""Recheck retained CPF semantic negatives with their expected diagnostics."""
import argparse,concurrent.futures,gzip,hashlib,json,re,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser();p.add_argument('binary',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();binary=a.binary.resolve();base=ROOT/'tests/certification/compact';manifest=json.loads((base/'manifest.json').read_text())
updates=json.loads((ROOT/'docs/unified-20261026/negative-diagnostic-updates.json').read_text());overrides={r['mutation_sha256']:r['current_diagnostic'] for r in updates}
def check(row):
 data=(base/row['certificate']).read_bytes();assert hashlib.sha256(data).hexdigest()==row['compressed_sha256'];data=gzip.decompress(data);assert hashlib.sha256(data).hexdigest()==row['mutation_sha256']
 with tempfile.TemporaryDirectory() as d:
  f=Path(d)/'proof.xml';f.write_bytes(data);t=time.monotonic();r=subprocess.run([str(binary),str(f)],capture_output=True,text=True)
 result=dict(id=row['id'],source_sha256=row['source_sha256'],mutation_sha256=row['mutation_sha256'],returncode=r.returncode,stdout=r.stdout,stderr=r.stderr,seconds=time.monotonic()-t)
 matches = (r.stderr==overrides[row['mutation_sha256']]) if row['mutation_sha256'] in overrides else re.search(row['expected_diagnostic_regex'],r.stdout+r.stderr,re.S) is not None
 result['semantic_rejection']=r.returncode==1 and r.stdout.strip()=='REJECTED' and matches
 return result
with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:rows=list(pool.map(check,manifest['negatives']))
report=dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),total=len(rows),semantic_rejections=sum(r['semantic_rejection'] for r in rows),results=rows)
a.output.write_bytes(gzip.compress(json.dumps(report).encode(),mtime=0));print(report['semantic_rejections'],'/',report['total']);assert all(r['semantic_rejection'] for r in rows)
