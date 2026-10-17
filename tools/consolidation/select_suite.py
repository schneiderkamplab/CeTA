#!/usr/bin/env python3
"""Select a fixed-denominator suite from eligible fresh proofs and their HPC ticks."""
import argparse,concurrent.futures,gzip,hashlib,json,pathlib,shutil
from coverage import inspect,registry
from setcover import select
from run_logged import memory_used
ROOT=pathlib.Path(__file__).resolve().parents[2]
REG=None
STAGE=None

def init_worker(reg,stage):
 global REG,STAGE
 REG=reg;STAGE=pathlib.Path(stage)

def analyze(row):
 run=STAGE/row['id'];proof=run/'proof.cpf.xml';dest=run/'proof.cpf.xml.gz'
 structural=inspect(proof,row['category'],REG)
 (run/'structural-coverage.json').write_text(json.dumps(structural,indent=2,sort_keys=True)+'\n')
 with proof.open('rb') as f,dest.open('wb') as out,gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0,compresslevel=1) as z:shutil.copyfileobj(f,z)
 with dest.open('rb') as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
 return dict(id=row['id'],root=row['root'],structural_features=structural['features'],unknown_tags=structural['unknown_proof_tags'],compressed_bytes=dest.stat().st_size,compressed_sha256=digest)

def main():
 p=argparse.ArgumentParser();p.add_argument('--stage',required=True);p.add_argument('--seconds',type=int,default=300);p.add_argument('--jobs',type=int,default=8);a=p.parse_args()
 if memory_used()>2*1024**4:raise SystemExit('Memory launch ceiling exceeded')
 stage=ROOT/'target/consolidation-corpus'/a.stage;summary=json.loads((stage/'summary.json').read_text())
 if summary['losses']:raise SystemExit('Baseline has unresolved losses; cannot freeze suite denominator')
 records=[json.loads(l) for l in (stage/'results.jsonl').read_text().splitlines()]
 if len(records)!=summary['roots'] or not all(r['eligible'] for r in records):raise SystemExit('Incomplete eligible corpus')
 records.sort(key=lambda r:r['root']);reg=registry();(stage/'processor-registry.json').write_text(json.dumps(reg,indent=2,sort_keys=True)+'\n')
 with concurrent.futures.ProcessPoolExecutor(max_workers=a.jobs,initializer=init_worker,initargs=(reg,str(stage))) as pool:analyses=list(pool.map(analyze,records))
 # Module hashes make instrumentation identity explicit. Cross-milestone changes
 # require an explicit mapping; counters from different binaries are never mixed.
 modules={}
 for r in records:
  with gzip.open(stage/r['id']/'coverage.tsv.gz','rt') as f:
   for line in f:
    name,digest,count,ticks=line.rstrip('\n').split('\t');entry=(digest,int(count))
    if name in modules and modules[name]!=entry:raise ValueError('Mixed HPC instrumentation for '+name)
    modules[name]=entry
 offsets={};total=0
 for name,(digest,count) in sorted(modules.items()):offsets[name]=total;total+=count
 structural_names=sorted({f for x in analyses for f in x['structural_features']}|{'root-kind|'+r['category']+'|'+r['expected_answer'] for r in records})
 structural_ids={f:total+i for i,f in enumerate(structural_names)};candidates=[]
 for row,ana in zip(records,analyses):
  features={structural_ids[f] for f in ana['structural_features']};features.add(structural_ids['root-kind|'+row['category']+'|'+row['expected_answer']])
  with gzip.open(stage/row['id']/'coverage.tsv.gz','rt') as f:
   for line in f:
    name,digest,count,ticks=line.rstrip('\n').split('\t')
    features.update(offsets[name]+int(i) for i in ticks.split(',') if i)
  candidates.append(dict(id=row['id'],features=features,time_us=round(sum(c['elapsed_seconds'] for c in row['checks'])*1e6),bytes=ana['compressed_bytes']))
 result=select(candidates,a.seconds);result['selected_ids']=[records[i]['id'] for i in result.pop('selected')];result['selected_roots']=[r['root'] for r in records if r['id'] in result['selected_ids']]
 universe=sorted(set().union(*(r['features'] for r in candidates)))
 denominator=dict(modules={n:dict(hash=d,count=c,offset=offsets[n]) for n,(d,c) in modules.items()},structural_features=structural_ids,required_obligations=universe,theorem_coverage='Not implied by HPC; criterion and exact semantic context gaps must be closed before restructuring affected paths.')
 (stage/'coverage-denominator.json').write_text(json.dumps(denominator,indent=2,sort_keys=True)+'\n')
 (stage/'candidate-costs.json').write_text(json.dumps(analyses,indent=2,sort_keys=True)+'\n')
 (stage/'selection.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result))
if __name__=='__main__':main()
