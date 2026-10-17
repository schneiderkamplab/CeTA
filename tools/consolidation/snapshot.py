#!/usr/bin/env python3
"""Freeze assessment sources without builds or changes to source worktrees.
One-shot: an existing snapshot requires an explicit new milestone directory.
"""
import hashlib,json,pathlib,shutil,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[2]; BASE=ROOT.parent
OUT=ROOT/'docs/consolidation'; PRIVATE=ROOT/'target/consolidation-snapshot'
def git(repo,*args): return subprocess.check_output(['git','-C',str(repo),*args],text=True).strip()
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()
def freeze(src,label):
    dst=PRIVATE/label;dst.parent.mkdir(parents=True,exist_ok=True)
    before=sha(src);shutil.copy2(src,dst);after=sha(dst)
    if before!=after or before!=sha(src): raise RuntimeError(f'Source changed: {src}')
    return dict(source=str(src),frozen=str(dst.relative_to(ROOT)),sha256=after,bytes=dst.stat().st_size)
def main():
    if (OUT/'snapshot.json').exists():raise SystemExit('Snapshot exists; do not repin silently')
    mem={k:int(v.split()[0])*1024 for k,v in (l.split(':',1) for l in pathlib.Path('/proc/meminfo').read_text().splitlines())}
    used=mem['MemTotal']-mem['MemAvailable']
    if used>2*1024**4:raise SystemExit('Memory ceiling exceeded')
    start=time.time();pins=dict(created_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),memory_used_bytes=used,repositories={})
    def refs(repo):return {k:v for k,v in (l.split(' ',1) for l in git(repo,'for-each-ref','--format=%(refname) %(objectname)','refs/heads').splitlines()) if k!='refs/heads/consolidated'}
    for name in ['CeTA','CeTA-CSR','ferrum-aaecc']:
        repo=BASE/name
        pins['repositories'][name]=dict(head=git(repo,'rev-parse','HEAD'),refs=refs(repo),tracked_status=git(repo,'status','--porcelain','--untracked-files=no'),tracked_diff_sha256=hashlib.sha256(git(repo,'diff','HEAD','--binary').encode()).hexdigest())
    pins['baseline']=git(BASE/'CeTA','rev-parse','8e6e5f9');repos=[]
    for repo in sorted(BASE.glob('CeTA*')):
        if repo==ROOT or not (repo/'.git').exists():continue
        common=git(repo,'rev-parse','--path-format=absolute','--git-common-dir')
        if common in [r['common_dir'] for r in repos]:continue
        rs=refs(repo);repos.append(dict(repository=repo.name,common_dir=common,refs=rs))
        specs=[f'{oid}:refs/consolidation-snapshot/{repo.name}/{ref.removeprefix("refs/heads/")}' for ref,oid in rs.items()]
        if specs:subprocess.run(['git','-C',str(ROOT),'fetch','--no-tags','--no-write-fetch-head','--no-auto-maintenance',str(repo),*specs],check=True)
    pins['development_repositories']=repos;f=BASE/'ferrum-aaecc'
    paths={'production_checker':BASE/'CeTA-CSR/ceta','ceta_main_checker':BASE/'CeTA/ceta','ferrum_head_binary':f/'target/release/ferrum','ferrum_producing_binary':f/'target/competitor-recovery-20261017/ferrum-fresh-budget-v21','current_oracle':f/'target/srs-native-20261013/integrated-rfc-residual-v634/oracle.jsonl','complete_replay_binary':f/'target/srs-native-20261013/ferrum-weak-zero-v587','complete_replay_oracle':f/'target/srs-native-20261013/integrated-weak-zero-chains-v591/oracle.jsonl'}
    pins['artifacts']={key:freeze(p,'artifacts/'+key) for key,p in paths.items()}
    pins['complete_replay_source_revision']='afb4acbd86412fbac3d27d5cd005ea5b3391d622'
    pins['latest_producing_source_revision']=git(f,'rev-parse','b8b572f')
    manifests=[]
    campaigns=['srs-native-20261013/unified-final-v593','srs-native-20261013/integrated-rfc-residual-v634','srs-native-20261013/replay-strip-v625','srs-native-20261013/replay-fresh-v631','competitor-recovery-20261017/projection-replay-v9','competitor-recovery-20261017/pattern-replay-v14','competitor-recovery-20261017/srs-replay-v31']
    for campaign in campaigns:
        top=f/'target'/campaign
        if not top.is_dir():manifests.append(dict(source=str(top),gap='missing campaign'));continue
        for path in sorted(top.glob('*'))+sorted(top.glob('*/*')):
            if path.is_file() and path.suffix in ('.json','.jsonl','.py','.sh') and path.name!='oracle.jsonl' and path.parent.name!='run':manifests.append(freeze(path,'manifests/'+str(path.relative_to(f/'target'))))
    pins['manifests']=manifests;pins['ledger']=freeze(f/'docs/state-of-the-art.md','evidence/state-of-the-art.md')
    pins['source_binary_linkage']='Ledger claims only; reproducible rebuild not performed. HEAD binary is not assumed to match producing binary.'
    pins['elapsed_seconds']=time.time()-start
    (OUT/'snapshot.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(manifests=len(manifests),elapsed_seconds=pins['elapsed_seconds'])))
if __name__=='__main__':main()
