from pathlib import Path
import sys,tarfile,io,subprocess,hashlib,json,gzip,time
R=Path.cwd();sys.path.insert(0,str(R/'tools/consolidation'));from audit_cpf_sharing import digest
O=R/'target/certificate-performance-20261027';D=O/'shared-children';D.mkdir(exist_ok=True)
spec=json.loads((R/'tests/unified/compact-children.json').read_text());records={};out=io.BytesIO();start=time.monotonic()
with tarfile.open(R/'tests/unified/compact-children.tar.gz','r:gz') as src,tarfile.open(fileobj=out,mode='w') as dst:
 for m in src.getmembers():
  data=src.extractfile(m).read();assert hashlib.sha256(data).hexdigest()==spec['children'][m.name]
  old=D/(m.name+'.before');new=D/m.name;old.write_bytes(data)
  r=subprocess.run([str(R/'target/cpf-share-build/release/cpf-share'),str(old),str(new)],capture_output=True,text=True,check=True)
  before,after=digest(old),digest(new);assert before['expanded_tree_sha256']==after['expanded_tree_sha256']
  newdata=new.read_bytes();rec=dict(compact_sha256=spec['children'][m.name],shared_sha256=hashlib.sha256(newdata).hexdigest(),original=before,shared=after,**json.loads(r.stdout));records[m.name]=rec
  i=tarfile.TarInfo(m.name);i.size=len(newdata);i.mode=0o644;dst.addfile(i,io.BytesIO(newdata))
packed=gzip.compress(out.getvalue(),mtime=0);(R/'tests/unified/shared-children.tar.gz').write_bytes(packed)
result=dict(original_archive_sha256=spec['original_archive_sha256'],compact_archive_sha256=spec['archive_sha256'],archive_sha256=hashlib.sha256(packed).hexdigest(),children={k:v['shared_sha256'] for k,v in records.items()},records=records,seconds=time.monotonic()-start)
(R/'tests/unified/shared-children.json').write_text(json.dumps(result,indent=2)+'\n');print(len(records),result['seconds'])
