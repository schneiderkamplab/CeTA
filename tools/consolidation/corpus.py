#!/usr/bin/env python3
"""Freeze receipt-bound candidates. Import does NOT assert replay eligibility."""
import concurrent.futures,gzip,hashlib,json,pathlib,shutil,sys,time
from run_logged import memory_used
ROOT=pathlib.Path(__file__).resolve().parents[2]; SNAP=ROOT/'target/consolidation-snapshot'; OUT=ROOT/'target/consolidation-corpus'
sys.path.insert(0,str(pathlib.Path(__file__).parent/'vendor'))
import audit_trs_root_correspondence as trs
import audit_csr_root_correspondence as csr

def digest(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def compress(src,dst):
    with src.open('rb') as f,dst.open('wb') as out,gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as z:shutil.copyfileobj(f,z)
def main():
    if memory_used()>2*1024**4:raise SystemExit('Memory launch ceiling exceeded')
    if (OUT/'manifest.json').exists():raise SystemExit('Frozen corpus exists; no implicit replacement')
    OUT.mkdir(parents=True,exist_ok=True);jobs=[]
    for manifest in sorted((SNAP/'manifests').rglob('details.json')):
        receipts={}
        for p in sorted(manifest.parent.glob('*rechecks*.jsonl')):
            for line in p.read_text().splitlines():
                row=json.loads(line);receipts.setdefault(row.get('path'),set()).add(row.get('sha256'))
        for row in json.loads(manifest.read_text()):
            jobs.append((manifest,row,receipts.get(row['path'],set())))
    def one(job):
        manifest,row,hashes=job
        identity=row['path'].split('TPDB-ARI/',1)[1]
        rid=hashlib.sha256((identity+'\0'+row['status']).encode()).hexdigest()[:24]
        origin=str(manifest.parent.relative_to(SNAP/'manifests'))
        run=OUT/'candidates'/rid;run.mkdir(parents=True,exist_ok=True)
        result=dict(id=rid,root=identity,answer=row['status'],category=row['category'],origin=origin,prior_replay_seconds=row['elapsed_seconds'],eligibility='candidate only; fresh strict replay required')
        try:
            src=ROOT.parent/'TPDB-ARI'/identity
            proofdir=pathlib.Path(row['artifact_dir'])
            if not proofdir.is_absolute():proofdir=ROOT.parent/'ferrum-aaecc'/proofdir
            proof=proofdir/'proof.cpf.xml'
            ph=digest(proof)
            if ph not in hashes:raise ValueError('CPF hash absent from frozen check receipts')
            shutil.copy2(src,run/'input.ari')
            if digest(src)!=digest(run/'input.ari'):raise ValueError('Input changed during copy')
            compress(proof,run/'retained.cpf.xml.gz')
            with gzip.open(run/'retained.cpf.xml.gz','rb') as f:
                if hashlib.file_digest(f,'sha256').hexdigest()!=ph:raise ValueError('CPF changed during copy')
            if row['category']=='TRS_Contextsensitive':audit=csr.compare((run/'input.ari').read_text(),gzip.open(run/'retained.cpf.xml.gz','rt').read(),row['status'])
            else:
                with gzip.open(run/'retained.cpf.xml.gz','rb') as f:root=trs.root_metadata(f)
                audit=trs.compare((run/'input.ari').read_text(),root,row['status'],row['category'])
            result.update(input_sha256=digest(run/'input.ari'),cpf_sha256=ph,compressed_sha256=digest(run/'retained.cpf.xml.gz'),compressed_bytes=(run/'retained.cpf.xml.gz').stat().st_size,correspondence=audit,imported=True)
        except Exception as e:result.update(imported=False,error=type(e).__name__+': '+str(e))
        (run/'candidate.json').write_text(json.dumps(result,indent=2)+'\n')
        return result
    results=[];start=time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        for row in pool.map(one,jobs):
            results.append(row)
            if len(results)%250==0:print(json.dumps(dict(imported=len(results),errors=sum(not x['imported'] for x in results))),flush=True)
    ids=[r['id'] for r in results]
    if len(ids)!=len(set(ids)):raise RuntimeError('Duplicate roots across candidates require explicit resolution')
    data=dict(schema_version=1,elapsed_seconds=time.monotonic()-start,roots=sorted(results,key=lambda r:r['root']))
    (OUT/'manifest.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(roots=len(results),errors=sum(not x['imported'] for x in results),elapsed_seconds=data['elapsed_seconds'])))
if __name__=='__main__':main()
