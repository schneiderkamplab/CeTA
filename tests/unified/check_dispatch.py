#!/usr/bin/env python3
"""The dispatcher must neither guess categories nor fall back after rejection."""
import argparse,json,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('binary',type=Path);a=p.parse_args();binary=str(a.binary.resolve())
expected=['cpf','cycle','conditional','conditional-erasure','lp','higher-order','higher-order-delegation','its']
r=subprocess.run([binary,'--list-categories'],capture_output=True,text=True);assert r.returncode==0 and r.stdout.splitlines()==expected
results=[]
with tempfile.TemporaryDirectory() as d:
 bad=Path(d)/'bad';bad.write_text('<unknown-certificate/>')
 for category in expected:
  args=['--category',category,str(bad)]
  if category=='higher-order-delegation':args.append(str(bad))
  r=subprocess.run([binary,*args],capture_output=True,text=True)
  assert r.returncode!=0 and 'CERTIFIED' not in r.stdout,(category,r)
  results.append(dict(category=category,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr))
 for args in [['--category'],['--category','unknown',str(bad)],['--category','cycle'],['--category','lp',str(bad),str(bad)]]:
  r=subprocess.run([binary,*args],capture_output=True,text=True);assert r.returncode!=0 and 'CERTIFIED' not in r.stdout
  results.append(dict(args=args,returncode=r.returncode))
print(json.dumps(results,indent=2))
