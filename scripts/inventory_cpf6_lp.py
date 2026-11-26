#!/usr/bin/env python3
"""Inventory exposed CPF6 syntax and bind it to transport/parser source files.

This is a static syntax inventory. Mathematical certification and replay coverage
are recorded separately in the milestone validation report.
"""
import argparse,hashlib,json,re
from pathlib import Path
from lxml import etree as E
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=root/'xml/cpf6-coverage.json');a=p.parse_args()
ns={'xs':'http://www.w3.org/2001/XMLSchema'};schema=E.parse(str(root/'xml/cpf6.xsd'))
refs={n.get('ref') for n in schema.findall('.//xs:element',ns)}
names=sorted(n for n in refs if n and n.startswith(('lp','prolog')) and n.endswith('Proof'))
adapter=root/'src/Haskell/Ceta/Input/Cpf6.hs';text=adapter.read_text()
assert all(n in text for n in names),'schema form lacks a transport entry'
record=dict(scope='CPF6 source and residual forms exposed by the unified LP/Prolog adapters; inherited CPF3-5 forms are separate. This static inventory is not a mathematical acceptance test.',roots=names,root_count=len(names),source_parsers={},excluded=[dict(constructor='prologContextReferencesDependencyTriplesProof',reason='Separate experimental formalization; not exported or dispatched by the current unified checker and not emitted by Ferrum.')])
for path in sorted((root/'thys/Logic_Programming').glob('*.thy')):
 for name in re.findall(r"XMLdo\s*\(STR\s*''((?:lp|prolog)\w+Proof)''\)",path.read_text()):
  if name in names:record['source_parsers'].setdefault(name,[]).append(dict(path=str(path.relative_to(root)),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
record['adapter_sha256']=hashlib.sha256(adapter.read_bytes()).hexdigest()
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(record,indent=2)+'\n');print(len(names),'CPF6 proof forms with transport entries')
