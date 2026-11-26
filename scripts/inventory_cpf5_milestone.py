#!/usr/bin/env python3
"""Freeze the authoritative ITS/HO strict and learned replay inputs and proofs."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--campaign',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=[];pins={}
for mode in ['other-oracle','other-learned-socket']:
 base=a.campaign/mode;manifest=json.loads((base/'manifest.json').read_text());snapshot=Path(manifest['snapshot']);roots={r['root']:r for r in json.loads((snapshot/'roots.json').read_text())};results=json.loads((base/'results.json').read_text());wanted={r['root']:r for r in results if r['category'] in ['Higher_Order_Rewriting','Integer_Transition_Systems']};found=set();pins[mode]=dict(results_sha256=sha(base/'results.json'),manifest_sha256=sha(base/'manifest.json'),root_manifest_sha256=sha(snapshot/'roots.json'),manifest=manifest)
 for f in sorted(base.glob('*/*/result.json')):
  r=json.loads(f.read_text())
  if r['root'] not in wanted:continue
  assert r==wanted[r['root']];assert r['root'] not in found;found.add(r['root']);source=Path(roots[r['root']]['source']);assert sha(source)==r['source_sha256']
  row=dict(mode=mode,root=r['root'],category=r['category'],expected=r['status'],certified=r['certified'],source=str(source),source_sha256=r['source_sha256'],artifact_dir=str(f.parent.resolve()),result_sha256=sha(f))
  if r['certified']:
   proof=Path(r['native']['proof']) if r['category']=='Higher_Order_Rewriting' else f.parent/'native/proof.cpf.xml';assert sha(proof)==r['certificate_sha256'],str(f)
   row.update(proof=str(proof.resolve()),proof_sha256=sha(proof))
   child=r.get('native',{}).get('child_proof')
   if child:row.update(child=child,child_sha256=sha(Path(child)))
  rows.append(row)
 assert found==set(wanted)
(a.output/'manifest.json').write_text(json.dumps(dict(pins=pins,rows=rows),indent=2)+'\n');print(len(rows),'inputs;',sum(r['certified'] for r in rows),'certificates')
