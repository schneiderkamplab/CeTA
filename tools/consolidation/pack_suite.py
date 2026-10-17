#!/usr/bin/env python3
"""Durably package selected genuine proofs and validated paired mutations."""
import argparse,gzip,json,pathlib,shutil
from replay import ROOT,CORPUS,sha,write

def main():
 p=argparse.ArgumentParser();p.add_argument('--stage',required=True);p.add_argument('--destination',type=pathlib.Path,required=True);p.add_argument('--scope',required=True);a=p.parse_args();stage=CORPUS/a.stage;dest=a.destination.resolve();dest.mkdir(parents=True,exist_ok=False)
 selection=json.loads((stage/'selection.json').read_text());metadata=json.loads((stage/'metadata.json').read_text());positives=[];negatives=[]
 budgets={r['root']:int(r.get('oracle_time_scale_percent',metadata['profile']['FERRUM_ORACLE_TIME_SCALE_PERCENT'])) for r in metadata['roots']}
 for rid in selection['selected_ids']:
  run=stage/rid;r=json.loads((run/'result.json').read_text());row=dict(root=r['root'],category=r['category'],answer=r['expected_answer'])
  if not r['eligible']:raise ValueError('Ineligible selected proof')
  source=pathlib.Path(r['replay']['command'][2]).resolve()
  if not source.is_relative_to(CORPUS.resolve()) or sha(source)!=r['input_sha256']:raise ValueError('Original replay input changed or escaped private corpus')
  inp=dest/'inputs'/row['root']
  if not inp.resolve().is_relative_to(dest):raise ValueError('Root escapes packaged inputs')
  inp.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,inp)
  proof=dest/'positives'/(rid+'.cpf.xml.gz');proof.parent.mkdir(exist_ok=True);shutil.copy2(run/'proof.cpf.xml.gz',proof)
  positives.append(dict(id=rid,root=row['root'],category=row['category'],answer=row['answer'],input=str(inp.relative_to(dest)),input_sha256=sha(inp),certificate=str(proof.relative_to(dest)),compressed_sha256=sha(proof),cpf_sha256=r['cpf_sha256'],reference_checks=r['checks'],reference_hpc=r['hpc'],replay=r['replay'],correspondence=r['correspondence'],oracle_time_scale_percent=budgets[row['root']]))
 source_negatives=stage/'negatives/manifest.json'
 if source_negatives.exists():
  negative_manifest=json.loads(source_negatives.read_text())
  write(dest/'negative-coverage-gaps.json',{k:v for k,v in negative_manifest.items() if k!='mutations'})
  for row in negative_manifest['mutations']:
   if not row['validated']:raise ValueError('Unvalidated negative cannot be packaged')
   path=dest/'negatives'/(row['id']+'.cpf.xml.gz');path.parent.mkdir(exist_ok=True)
   with (stage/'negatives'/row['id']/'proof.cpf.xml').open('rb') as src,path.open('wb') as out,gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as z:shutil.copyfileobj(src,z)
   negatives.append(row|dict(certificate=str(path.relative_to(dest)),compressed_sha256=sha(path)))
 shutil.copy2(stage/'coverage-denominator.json',dest/'coverage-denominator.json');shutil.copy2(stage/'processor-registry.json',dest/'processor-registry.json')
 write(dest/'manifest.json',dict(schema_version=1,scope=a.scope,positives=positives,negatives=negatives,selection=selection,provenance=metadata,coverage_denominator_sha256=sha(dest/'coverage-denominator.json'),gaps=['Criterion-level mapping and exact nested contexts remain incomplete.','Negative map/Q, mode-specific usable-rule, minimality, freshness, order and automaton closure coverage remains incomplete.']))
 print(json.dumps(dict(destination=str(dest),positives=len(positives),negatives=len(negatives),scope=a.scope)))
if __name__=='__main__':main()
