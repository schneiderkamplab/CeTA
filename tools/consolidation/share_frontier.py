#!/usr/bin/env python3
"""Share repeated CPF terms and audit expansion; retain other formats unchanged."""
from audit_cpf_sharing import digest
import argparse,concurrent.futures,gzip,hashlib,json,os,shutil,subprocess,tempfile,time,zipfile
from pathlib import Path

def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def memory_ok():
 m={r.split(':')[0]:int(r.split()[1]) for r in Path('/proc/meminfo').read_text().splitlines()}
 return (m['MemTotal']-m['MemAvailable'])*1024<2*1024**4

def export(task):
 item,a,binary,binary_hash,exports=task
 name,row=item;h=row['proof_sha256'];receipt=exports/(h+'.json');dest=exports/(h+'.proof.gz')
 if receipt.exists():
  old=json.loads(receipt.read_text())
  if old['compactor_sha256']==binary_hash and dest.exists() and sha(dest)==old['compressed_sha256']:return name,old
 while not memory_ok():time.sleep(1)
 with tempfile.TemporaryDirectory(dir=a.output,prefix='export-') as tmp:
  source=Path(tmp)/'original';compact=Path(tmp)/'compact';t=time.monotonic()
  with zipfile.ZipFile(a.archive) as archive,archive.open(name) as member,source.open('wb') as f:
   if name.endswith('.gz'):
    with gzip.GzipFile(fileobj=member) as data:shutil.copyfileobj(data,f,1024*1024)
   else:shutil.copyfileobj(member,f,1024*1024)
  assert sha(source)==h
  with source.open('rb') as f:is_xml=f.read(4096).lstrip().startswith(b'<')
  if is_xml:
   result=subprocess.run([str(binary),str(source),str(compact)],capture_output=True,text=True)
   if result.returncode:raise RuntimeError(f'{name}: {result.stderr}')
  else:compact=source
  audit = None
  if sha(compact) != h:
   before,after=digest(source),digest(compact)
   assert before['expanded_tree_sha256']==after['expanded_tree_sha256'], name
   audit=dict(original=before,shared=after,equal=True)
  record=dict(expansion_audit=audit,original_sha256=h,compact_sha256=sha(compact),original_bytes=source.stat().st_size,compact_bytes=compact.stat().st_size,xml=is_xml,compactor_sha256=binary_hash,seconds=time.monotonic()-t)
  with compact.open('rb') as src,dest.open('wb') as raw,gzip.GzipFile(filename='',fileobj=raw,mode='wb',compresslevel=1,mtime=0) as gz:shutil.copyfileobj(src,gz,1024*1024)
  record['compressed_sha256']=sha(dest);receipt.write_text(json.dumps(record,indent=2)+'\n');return name,record

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--archive',type=Path,required=True);p.add_argument('--compactor',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--workers',type=int,default=4);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);exports=a.output/'exports';exports.mkdir(exist_ok=True)
 original=json.loads(gzip.decompress(a.manifest.read_bytes()));assert sha(a.archive)==original['artifact_archive_sha256'];binary=a.compactor.resolve();binary_hash=sha(binary);unique={r['proof']:r for r in original['roots']};started=time.monotonic()
 records={}
 with concurrent.futures.ProcessPoolExecutor(max_workers=a.workers) as pool:
  futures=[pool.submit(export,(item,a,binary,binary_hash,exports)) for item in unique.items()]
  for future in concurrent.futures.as_completed(futures):
   name,row=future.result();records[name]=row
   if len(records)%100==0:print(len(records),'/',len(unique),round(time.monotonic()-started,1),flush=True)
 final_archive=a.output/'frontier-5412-shared.zip'
 with zipfile.ZipFile(a.archive) as old,zipfile.ZipFile(final_archive,'w',compression=zipfile.ZIP_STORED,allowZip64=True) as new:
  for name in sorted({r['input'] for r in original['roots']}):
   with old.open(name) as src,new.open(name,'w',force_zip64=True) as dst:shutil.copyfileobj(src,dst,1024*1024)
  for name,record in sorted(records.items()):new.write(exports/(record['original_sha256']+'.proof.gz'),name)
 manifest=dict(original);manifest['roots']=[dict(r,original_proof_sha256=r.get('original_proof_sha256',r['proof_sha256']),compact_proof_sha256=r['proof_sha256'],proof_sha256=records[r['proof']]['compact_sha256']) for r in original['roots']];manifest['artifact_archive']=str(final_archive.resolve());manifest['artifact_archive_sha256']=sha(final_archive);manifest['original_archive_sha256']=original['artifact_archive_sha256'];manifest['original_manifest_sha256']=sha(a.manifest)
 (a.output/'manifest.json.gz').write_bytes(gzip.compress(json.dumps(manifest).encode(),mtime=0))
 report=dict(roots=len(manifest['roots']),unique_proofs=len(records),xml_proofs=sum(r['xml'] for r in records.values()),original_bytes=sum(r['original_bytes'] for r in records.values()),compact_bytes=sum(r['compact_bytes'] for r in records.values()),seconds=time.monotonic()-started,compactor_sha256=binary_hash,original_manifest_sha256=sha(a.manifest),original_archive_sha256=original['artifact_archive_sha256'],archive_sha256=manifest['artifact_archive_sha256'],records=records)
 (a.output/'reexport.json.gz').write_bytes(gzip.compress(json.dumps(report).encode(),mtime=0));print({k:v for k,v in report.items() if k!='records'},flush=True)
if __name__=='__main__':main()
