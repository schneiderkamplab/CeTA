#!/usr/bin/env python3
"""Connect observed CPF modes with checker/theorem candidates and paired tests.

These are reviewed syntactic contexts plus source candidate links, not inferred
semantic equivalences. Gaps stay explicit for every unresolved criterion.
"""
import argparse,collections,gzip,json,pathlib,xml.etree.ElementTree as ET
from replay import sha
from coverage import inspect
from suite import inside


def main():
 p=argparse.ArgumentParser();p.add_argument('--manifest',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
 base=a.manifest.resolve().parent;m=json.loads(a.manifest.read_text());reg=json.loads((base/'processor-registry.json').read_text());entries={};analyses={};unmapped=[]
 wrappers={'proof','trsTerminationProof','dpProof','dpTerminationProof','trsNonterminationProof','dpNonterminationProof','csrTerminationProof','csrDpTerminationProof','csrDpProof','relativeAdpTerminationProof','csrGuardedTerminationProof','csrImprovedDpProof','csrMutermTypedDpProof'}
 for r in m['positives']:
  path=inside(base,r['certificate'])
  if sha(path)!=r['compressed_sha256']:raise ValueError('Positive changed')
  analysis=inspect(path,r['category'],reg);analyses[r['id']]=(r,analysis)
  if analysis['unknown_proof_tags']:raise ValueError('Unknown proof node')
  for feature in analysis['features']:
   if not feature.startswith('cpf|'):continue
   _,category,container,placement,tag=feature.split('|')
   e=entries.setdefault(feature,dict(processor=tag,mode=dict(category=category,container=container,placement=placement),positive_ids=[],negative_tests=[],checker_parser_theorem_candidates=reg['processor_candidates'][tag],gaps=['Exact semantic P/Pw/Q/R/Rw, minimality, replacement-map and signature state at this node needs criterion-specific reconstruction.','Lexical driver/theorem links are not a checked equivalence or proof-premise mapping. Runtime ticks do not execute soundness proofs.']))
   e['positive_ids'].append(r['id'])
 for r in m['negatives']:
  source,analysis=analyses[r['source_id']]
  with gzip.open(inside(base,source['certificate']),'rb') as f:tree=ET.parse(f)
  target=tree.getroot().find(r['xpath'])
  if target is None:raise ValueError('Mutation target missing in source')
  parents={c:n for n in tree.getroot().iter() for c in n};chain=[target]
  while chain[-1] in parents:chain.append(parents[chain[-1]])
  chain.reverse();processors=[]
  for i,n in enumerate(chain):
   data_only=n.tag=='usableRules' and not any('complexity' in a.tag.lower() for a in chain[:i])
   if n.tag in reg['processor_candidates'] and not data_only:processors.append(i)
  if not processors:
   if [n.tag for n in chain]==['certificationProblem','proof','trsTerminationProof','bounds','treeAutomaton','transitions']:
    r=r|dict(criterion=dict(checker='bounds_tt / check_bounds_generic',theorem='bounds_tt',theory='thys/Termination_and_Complexity/Matchbounds_Impl.thy',parser='thys/Proof_Checker/CPF_Proof_Parser.thy:bounds_info -> Bounds',driver='thys/Proof_Checker_Base/Check_Termination.thy:check_trs_termination_proof (Bounds info)',premises='tp_spec I; isOK bounds_tt; infinite symbol universe. Bounds checks cover strict and weak rules together and establish a stronger empty-Q termination premise.',status='Source-reviewed link; lexical processor-mode registry omits the XMLor xml_change adapter. Recorded separately without changing the frozen denominator.'))
   unmapped.append(dict(id=r['id'],source_id=r['source_id'],kind=r['kind'],source_path=[n.tag for n in chain],criterion=r.get('criterion'),gap='Known proof/data tag without a lexical processor mapping. Positive HPC coverage still records execution; semantic mapping is required before restructuring this path.'))
   continue
  index=processors[-1];tag=chain[index].tag;container=next((n.tag for n in reversed(chain[:index]) if n.tag in wrappers),'proof');placement='nested' if len(processors)>1 else 'root'
  key='|'.join(['cpf',source['category'],container,placement,tag])
  if key not in entries:raise ValueError('Mutation mode absent from positive coverage: '+key)
  entries[key]['negative_tests'].append(dict(id=r['id'],source_id=r['source_id'],kind=r['kind'],xpath=r['xpath'],source_sha256=r['source_sha256'],mutation_sha256=r['mutation_sha256'],expected_diagnostic_regex=r['expected_diagnostic_regex'],criterion=r.get('criterion'),scope='First matching source XPath used by the mutation generator; intended semantic rejection checked twice.'))
 for e in entries.values():
  if not e['negative_tests']:e['gaps'].append('No selected mutation directly targets this processor/mode.')
  e['positive_ids'].sort();e['negative_tests'].sort(key=lambda r:r['id'])
 result=dict(manifest_sha256=sha(a.manifest),registry_sha256=sha(base/'processor-registry.json'),registry_revision=reg['revision'],modes=entries,observed_modes=len(entries),processors=len({e['processor'] for e in entries.values()}),negative_tests=len(m['negatives']),unmapped_negative_tests=unmapped,modes_with_direct_negatives=sum(bool(e['negative_tests']) for e in entries.values()),scope='Machine-readable structural processor/mode -> parser/checker/theorem candidates -> selected real positives and direct semantic rejection tests. Source/HPC function mapping and explicitly reviewed GM04 premises are separate linked evidence; all other semantic gaps constrain restructuring.',supporting_evidence=['coverage-baseline/checker-coverage-mapping.json.gz','gm04-criterion-coverage.json','reconciled-coverage-transition-v2.json.gz'])
 a.output.write_bytes(gzip.compress((json.dumps(result,sort_keys=True)+'\n').encode(),mtime=0));print(json.dumps({k:result[k] for k in ['observed_modes','processors','negative_tests','modes_with_direct_negatives']}))

if __name__=='__main__':main()
