from pathlib import Path
import concurrent.futures,gzip,hashlib,json,subprocess,tempfile,zipfile,time,shutil
R=Path.cwd();O=R/'target/certificate-performance-20261027';S=R/'target/shared-frontier-compatible-20261027';B=R/'target/cpf-share-build/release/cpf-share';A=R/'target/compact-frontier-20261026/frontier-5412-compact.zip'
report=json.loads(gzip.decompress((S/'reexport.json.gz').read_bytes()))
def check(item):
 name,row=item
 if not row['xml']:return name
 with tempfile.TemporaryDirectory(dir=O) as tmp:
  old=Path(tmp)/'before';new=Path(tmp)/'after'
  with zipfile.ZipFile(A) as z,z.open(name) as member,old.open('wb') as out:
   if name.endswith('.gz'):
    with gzip.GzipFile(fileobj=member) as src:shutil.copyfileobj(src,out,1024*1024)
   else:shutil.copyfileobj(member,out,1024*1024)
  subprocess.run([str(B),str(old),str(new)],check=True,stdout=subprocess.DEVNULL)
  with new.open('rb') as f:actual=hashlib.file_digest(f,'sha256').hexdigest()
  assert actual==row['compact_sha256'],name
 return name
if __name__=='__main__':
 t=time.monotonic()
 with concurrent.futures.ProcessPoolExecutor(max_workers=16) as pool:rows=list(pool.map(check,report['records'].items()))
 result=dict(proofs=len(rows),identical=True,seconds=time.monotonic()-t,exporter_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),previous_exporter_sha256=report['compactor_sha256'],sources={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (R/'tools/cpf-share').rglob('*') if p.is_file()})
 (O/'sharing-reproduction.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
