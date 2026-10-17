#!/usr/bin/env python3
"""Compare a fresh packaged replay against exact frozen roots and coverage.

Structural analysis may be reused only for byte-identical proofs in the durable
baseline matrix. Changed proofs are parsed; unknown nodes remain failures.
"""
import argparse,concurrent.futures,gzip,json,pathlib
from replay import sha,write
from coverage import inspect
from coverage_transition import Transition


def main():
 p=argparse.ArgumentParser()
 for name in ['manifest','replay','compact','baseline-evidence','transition','checker','hpc-checker','output']:p.add_argument('--'+name,type=pathlib.Path,required=True)
 p.add_argument('--jobs',type=int,default=8);a=p.parse_args()
 if a.jobs<1:p.error('Positive job count required')
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 manifest=json.loads(a.manifest.read_text());meta=json.loads((a.replay/'metadata.json').read_text());summary=json.loads((a.replay/'summary.json').read_text())
 if meta['manifest_sha256']!=sha(a.manifest) or meta['checker_sha256']!=sha(a.checker) or meta['hpc_sha256']!=sha(a.hpc_checker):raise ValueError('Replay identity mismatch')
 for name in ['source_revision','oracle_sha256']:
  if meta[name]!=manifest['provenance'][name]:raise ValueError('Replay provenance changed: '+name)
 if summary['failures']:raise ValueError('Resolve fresh replay failures before coverage comparison')
 audit=json.loads((a.replay/'oracle-audit.json').read_text())
 if audit['sha256']!=meta['oracle_sha256'] or audit['forbidden'] or audit['unresolved_aliases']:raise ValueError('Search-only oracle audit failed')
 expected={(r['id'],r['root'],r['answer'],r['input_sha256']) for r in manifest['positives']}
 if len(expected)!=len(manifest['positives']):raise ValueError('Duplicate expected identities')
 roots=sorted(r['root'] for r in manifest['positives'])
 if summary['expected_roots']!=roots or summary['certified_roots']!=roots:raise ValueError('Replay summary lost or added roots')
 rows=[json.loads((a.replay/r['id']/'result.json').read_text()) for r in manifest['positives']]
 actual={(r['id'],r['root'],r['expected_answer'],r['input_sha256']) for r in rows}
 if expected!=actual or len(rows)!=len(actual) or summary['roots']!=len(rows):raise ValueError('Exact root/input/answer set changed')
 denominator_path=a.compact/'coverage-denominator.json';den=json.loads(denominator_path.read_text());transition=Transition(a.transition,denominator_path,a.checker,a.hpc_checker)
 evidence=a.baseline_evidence
 with gzip.open(evidence/'matrix.json.gz','rt') as f:matrix=json.load(f)
 verification=json.loads((evidence/'verification.json').read_text())
 if sha(evidence/'matrix.json.gz')!=verification['matrix_sha256'] or matrix['denominator_sha256']!=sha(denominator_path):raise ValueError('Baseline coverage matrix changed')
 with gzip.open(evidence/'coverage-gaps.json.gz','rt') as f:gaps=json.load(f)
 if gaps['unknown_proof_nodes']:raise ValueError('Baseline contains unknown nodes')
 structural=set(den['structural_features'].values());baseline={r['id']:r|dict(features=set()) for r in matrix['candidates']}
 for pattern in matrix['patterns']:
  features=set(pattern['obligations'])&structural
  if not features:continue
  mask=int(pattern['candidate_bits_hex'],16)
  while mask:
   bit=mask&-mask;i=bit.bit_length()-1;baseline[matrix['candidates'][i]['id']]['features'].update(features);mask-=bit
 registry=json.loads((a.compact/'processor-registry.json').read_text())
 def one(r):
  run=a.replay/r['id'];proof=run/'proof.cpf.xml'
  if not r['passed'] or not r['correspondence'] or len(r['checks'])!=2 or not all(c['certified'] and not c['timed_out'] and c['returncode']==0 for c in r['checks']) or not r['hpc']['certified']:raise ValueError('Invalid acceptance receipt: '+r['root'])
  if sha(proof)!=r['cpf_sha256'] or sha(run/'coverage.tsv.gz')!=r['coverage_sha256']:raise ValueError('Replay artifact changed: '+r['root'])
  observed=set();unknown={};extra=[];previous=baseline.get(r['id']);reused=bool(previous and previous['root']==r['root'] and previous['cpf_sha256']==r['cpf_sha256'])
  if reused:observed.update(previous['features'])
  else:
   analysis=inspect(proof,r['category'],registry);unknown=analysis['unknown_proof_tags']
   for feature in analysis['features']+['root-kind|'+r['category']+'|'+r['expected_answer']]:
    if feature in den['structural_features']:observed.add(den['structural_features'][feature])
    else:extra.append(feature)
  with gzip.open(run/'coverage.tsv.gz','rt') as f:
   for line in f:
    name,digest,count,ticks=line.rstrip('\n').split('\t');observed.update(transition.observe(name,digest,int(count),[int(i) for i in ticks.split(',') if i]))
  return dict(id=r['id'],root=r['root'],cpf_sha256=r['cpf_sha256'],structural_reused_by_exact_proof_hash=reused,unknown_proof_nodes=unknown,new_structural_obligations=extra,observed=observed)
 observed=set();results=[]
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
  for r in pool.map(one,rows):observed.update(r.pop('observed'));results.append(r)
 required=set(den['required_obligations']);missing=sorted(required-observed-transition.retired);unknown=[r['id'] for r in results if r['unknown_proof_nodes']];new=[r for r in results if r['new_structural_obligations']]
 report=dict(ferrum_baseline_binary_sha256=manifest['provenance'].get('ferrum_sha256'),ferrum_rebuilt_binary_sha256=meta['ferrum_sha256'],ferrum_build_identity_note='Both builds use the frozen source revision and archive. Binary identities are recorded separately; the source embeds absolute CARGO_MANIFEST_DIR paths.',exact_root_set_preserved=True,roots=len(rows),losses=[],missing_coverage=missing,retired_coverage=sorted(transition.retired),observed_required_coverage=len(required&observed),frozen_required_coverage=len(required),unknown_node_roots=unknown,new_structural_obligations=new,results=results,manifest_sha256=sha(a.manifest),replay_metadata_sha256=sha(a.replay/'metadata.json'),replay_summary_sha256=sha(a.replay/'summary.json'),transition_sha256=sha(a.transition),baseline_matrix_sha256=sha(evidence/'matrix.json.gz'),scope='Fresh Ferrum replay, original input audits, twice production and HPC acceptance, exact root identities and retained baseline coverage. Runtime observations do not execute Isabelle proofs.',passed=not missing and not unknown and not new)
 write(out/'summary.json',report);print(json.dumps({k:report[k] for k in ['roots','exact_root_set_preserved','observed_required_coverage','frozen_required_coverage','passed']}|dict(missing=len(missing),unknown=len(unknown),new_structural_roots=len(new))))
 raise SystemExit(not report['passed'])

if __name__=='__main__':main()
