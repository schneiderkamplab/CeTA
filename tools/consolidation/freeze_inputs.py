#!/usr/bin/env python3
"""Freeze exact benchmark identities from pinned replay manifests independently of CPF import."""
import hashlib,json,pathlib,shutil
ROOT=pathlib.Path(__file__).resolve().parents[2];CORPUS=ROOT/'target/consolidation-corpus';SNAP=ROOT/'target/consolidation-snapshot'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
 out=CORPUS/'input-manifest.json'
 if out.exists():raise SystemExit('Inputs already frozen')
 rows=[];seen=set()
 for manifest in sorted((SNAP/'manifests').rglob('details.json')):
  for row in json.loads(manifest.read_text()):
   root=row['path'].split('TPDB-ARI/',1)[1]
   if root in seen:raise ValueError('Duplicate benchmark '+root)
   seen.add(root);src=ROOT.parent/'TPDB-ARI'/root;dst=CORPUS/'frozen-inputs'/root;dst.parent.mkdir(parents=True,exist_ok=True)
   before=sha(src);shutil.copy2(src,dst)
   if before!=sha(dst) or before!=sha(src):raise ValueError('Input changed '+root)
   rows.append(dict(id=hashlib.sha256((root+'\0'+row['status']).encode()).hexdigest()[:24],root=root,answer=row['status'],category=row['category'],prior_replay_seconds=row['elapsed_seconds'],input_sha256=before,reference_manifest=str(manifest.relative_to(ROOT))))
 out.write_text(json.dumps(dict(roots=sorted(rows,key=lambda x:x['root'])),indent=2)+'\n');print('Frozen inputs',len(rows))
if __name__=='__main__':main()
