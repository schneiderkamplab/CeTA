#!/usr/bin/env python3
"""Validate assessment artifacts, not theorem soundness or certificate acceptance."""
import hashlib,json,pathlib,subprocess,time
from snapshot import sha
ROOT=pathlib.Path(__file__).resolve().parents[2]; OUT=ROOT/'docs/consolidation'
def git(*a):return subprocess.check_output(['git','-C',str(ROOT),*a],text=True).strip()
def read(n):return json.loads((OUT/n).read_text())
def main():
 start=time.monotonic();s=read('snapshot.json');supp=read('supplemental-snapshot.json')
 artifacts=list(s['artifacts'].values())+s['manifests']+[s['ledger']]+supp['source_archives']+supp['toolchain']
 for a in artifacts:
  if 'gap' in a:continue
  p=ROOT/a['frozen']
  assert p.is_file(),str(p)
  assert p.stat().st_size==a['bytes'] and sha(p)==a['sha256'],str(p)
  if 'source' in a and pathlib.Path(a['source']).exists():
   assert not p.samefile(a['source']),f'Not a private copy: {p}'
 inv=read('source-inventory.json');g=read('coverage-gaps.json');families=read('families.json');branches=read('branches.json')
 keys={(v['path'],v['blob']) for v in inv['variants']}
 classified=[(v['path'],v['blob']) for f in families['families'] for v in f['theory_variants']]
 assert len(classified)==len(set(classified)) and set(classified)==keys
 assert len(keys)==g['unique_theory_variants']
 assert len({p for p,b in keys})==g['unique_theory_paths']
 assert sum(len(v['checker_candidates']) for v in inv['variants'])==g['checker_candidates']
 assert len(branches['branches'])==g['pinned_tips']
 assert g['eligible_positive_proofs']==g['verified_negative_tests']==0
 for v in inv['variants']:assert git('cat-file','-t',v['blob'])=='blob'
 for repo in s['development_repositories']:
  for ref,rev in repo['refs'].items():
   snapshot_ref='refs/consolidation-snapshot/'+repo['repository']+'/'+ref.removeprefix('refs/heads/')
   assert git('rev-parse',snapshot_ref)==rev,snapshot_ref
 baseline=s['repositories']['CeTA']['refs']['refs/heads/main']
 # All tracked edits outside the review packet are forbidden at this checkpoint.
 subprocess.run(['git','-C',str(ROOT),'diff','--exit-code',baseline,'--','.',':(exclude)docs/consolidation',':(exclude)tools/consolidation'],check=True)
 assert git('branch','--show-current')=='consolidated'
 parent_checks={}
 for name in ['CeTA','CeTA-CSR']:
  repo=ROOT.parent/name
  def parentgit(*a):return subprocess.check_output(['git','-C',str(repo),*a],text=True).strip()
  expected=s['repositories'][name]
  assert parentgit('rev-parse','HEAD')==expected['head'],name+' advanced externally; investigate before finalizing'
  assert hashlib.sha256(parentgit('diff','HEAD','--binary').encode()).hexdigest()==expected['tracked_diff_sha256'],name+' tracked diff changed'
  for ref,rev in expected['refs'].items():assert parentgit('rev-parse',ref)==rev,ref
  parent_checks[name]='original branch refs and tracked diff unchanged'
 result=dict(status='passed',scope='assessment integrity only; no Isabelle build, certificate check, HPC measurement or replay claimed',private_artifacts_checked=sum('gap' not in a for a in artifacts),theory_variants_checked=len(keys),parent_checks=parent_checks,elapsed_seconds=time.monotonic()-start)
 (OUT/'verification.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result))
if __name__=='__main__':main()
