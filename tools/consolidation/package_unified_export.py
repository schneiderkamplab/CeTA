#!/usr/bin/env python3
"""Package an Isabelle-generated category export and record its exact source hashes."""
import argparse,gzip,hashlib,io,json,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--category',required=True);p.add_argument('--directory',type=Path,required=True);p.add_argument('--theory',type=Path,required=True);a=p.parse_args();manifest=ROOT/'scripts/unified-exports.json';data=json.loads(manifest.read_text());entry=data[a.category];files=sorted(a.directory.glob('*.hs'));assert files and not any(p.name=='Main.hs' for p in files)
 out=io.BytesIO()
 with tarfile.open(fileobj=out,mode='w') as bundle:
  for path in files:
   content=path.read_bytes();info=tarfile.TarInfo(path.name);info.size=len(content);info.mode=0o644;bundle.addfile(info,io.BytesIO(content))
 packed=gzip.compress(out.getvalue(),mtime=0);(ROOT/entry['archive']).write_bytes(packed);entry.update(sources={p.name:sha(p.read_bytes()) for p in files},archive_sha256=sha(packed),origin=str(a.directory.resolve()),optimization_theory=str(a.theory),optimization_theory_sha256=sha(a.theory.read_bytes()));manifest.write_text(json.dumps(data,indent=2)+'\n');print(a.category,len(files),entry['archive_sha256'])
if __name__=='__main__':main()
