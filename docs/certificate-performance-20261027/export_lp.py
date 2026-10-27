from pathlib import Path
import os,json,re,subprocess,time,concurrent.futures,hashlib
R=Path.cwd();O=R/'target/certificate-performance-20261027';OLD=R/'target/usable-membership-20261026';W=O/'lp-wrappers';W.mkdir(exist_ok=True);S=OLD/'lp-source-committed/thys/Logic_Programming';perf=R/'thys/Certificate_Performance/Certificate_Performance';ur=R/'thys/Usable_Rules_Membership/Usable_Rules_Membership'
recipes=json.loads((OLD/'lp-recipes.json').read_text());recipes.append(dict(module='LP_Cut_NO_Generated',imports=[str(S/'LP_Cut_NO_XML')],recipe=str(R.parent/'CeTA/target/LP_NO_Renaming_Export_v133.thy')))
for r in recipes:
 module=r['module'];old=(OLD/'lp-wrappers'/('Indexed_'+module+'.thy')) if module!='LP_Cut_NO_Generated' else Path(r['recipe']);text=old.read_text();ml=text.split('ML \\<open>',1)[1].split('val root =',1)[0];ml=ml.replace('\\<close>','');r['wrapper_source_sha256']=hashlib.sha256(old.read_bytes()).hexdigest()
 for variant in (['Baseline','Performance'] if module=='LP_Cut_NO_Generated' else ['Performance']):
  name=variant+'_'+module;out=O/('lp-'+variant.lower())/module;out.mkdir(parents=True,exist_ok=True);deps=r['imports']+([str(ur),str(perf)] if variant=='Performance' else []);body='theory '+name+'\nimports '+' '.join(json.dumps(d) for d in deps)+'\nbegin\nML \\<open>\n'+ml+'\nval root = Path.explode '+json.dumps(str(out))+';\nval _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;\nval _ = writeln "EXPORTED_'+name+'";\n\\<close>\nend\n';(W/(name+'.thy')).write_text(body)
env=dict(os.environ,USER_HOME=str(OLD/'user'),ISABELLE_IDENTIFIER='usable_membership_20261026',AFP=str(R/'target/consolidation-build/afp-source/thys'));cmd=['/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle','console','-n','-l','Proof_Checker','-d',str(R/'target/equational-production-20261019/source/thys'),'-o','threads=4','-o','parallel_proofs=0','-o','quick_and_dirty=false']
def run(r):
 module=r['module'];variants=['Baseline','Performance'] if module=='LP_Cut_NO_Generated' else ['Performance'];code='; '.join('Thy_Info.use_thy_legacy '+json.dumps(str(W/(v+'_'+module))) for v in variants);marker='LP_PERFORMANCE_VERIFIED_'+module;code='(('+code+'; writeln "'+marker+'"; OS.Process.exit OS.Process.success) handle exn => (Runtime.exn_message exn |> writeln; OS.Process.exit OS.Process.failure));\n';t=time.monotonic();log=O/(module+'.log')
 with log.open('w') as f:p=subprocess.run(cmd,input=code,text=True,env=env,stdout=f,stderr=subprocess.STDOUT)
 record=dict(module=module,command=cmd,seconds=time.monotonic()-t,returncode=p.returncode,verified=p.returncode==0 and marker in log.read_text(),recipe=r)
 if module=='LP_Cut_NO_Generated' and record['verified']:
  actual=hashlib.sha256((O/'lp-baseline'/module/(module+'.hs')).read_bytes()).hexdigest();expected=json.loads((R/'scripts/unified-exports.json').read_text())['lp']['sources'][module+'.hs'];record.update(baseline_sha256=actual,baseline_matches_production=actual==expected);assert actual==expected
 (O/(module+'.json')).write_text(json.dumps(record,indent=2));print(module,record['verified'],record['seconds'],flush=True);return record
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(run,recipes))
assert all(r['verified'] for r in results)
