import json,pathlib,tempfile,unittest
from oracle_audit import audit,SCHEMA
from coverage import inspect
from replay import certified
from setcover import select
from root_audit import compare as audit_root
ROOT=pathlib.Path(__file__).resolve().parents[2]
class Harness(unittest.TestCase):
 def setUp(self):
  parent=ROOT/'target/consolidation-build/test-tmp';parent.mkdir(parents=True,exist_ok=True);self.temp=tempfile.TemporaryDirectory(dir=parent);self.p=pathlib.Path(self.temp.name)
 def tearDown(self):self.temp.cleanup()
 def test_oracle_rejects_hidden_witness_and_composite(self):
  for item in [{'candidate':'exact-poly(hex=ab)'},{'candidate':'seq(dp,empty)'},{'candidate':'poly','candidate_ref':'abc'}]:
   p=self.p/'oracle';p.write_text(json.dumps(dict(schema=SCHEMA,problem_key='a'*64,prefer=[item]))+'\n');self.assertTrue(audit(p)['forbidden'])
 def test_oracle_accepts_numeric_search_bounds(self):
  p=self.p/'oracle';p.write_text(json.dumps(dict(schema=SCHEMA,problem_key='a'*64,prefer=[{'candidate':'matrix(dim=2,max-coefficient=3)'}]))+'\n');self.assertFalse(audit(p)['forbidden'])
 def test_oracle_alias_must_resolve(self):
  p=self.p/'oracle';p.write_text(json.dumps(dict(schema=SCHEMA,problem_key='a'*64,canonical_problem_key='b'*64))+'\n');self.assertTrue(audit(p)['unresolved_aliases'])
 def test_coverage_unknown_and_empty_boundary(self):
  p=self.p/'proof.xml';p.write_text('<certificationProblem><proof><trsTerminationProof><step><rules/><trsTerminationProof><alien/></trsTerminationProof></step></trsTerminationProof></proof></certificationProblem>')
  reg=dict(known_xml_tags=['step','rules'],processor_candidates={'step':[]});r=inspect(p,'TRS_Standard',reg)
  self.assertEqual(r['unknown_proof_tags'],{'alien':1});self.assertIn('boundary|TRS_Standard|rules|empty',r['features'])
 def test_acceptance_does_not_confuse_crash_or_timeout(self):
  p=self.p/'check';p.with_suffix('.stdout').write_text('CERTIFIED\n')
  self.assertTrue(certified(dict(returncode=0,timed_out=False),p))
  self.assertFalse(certified(dict(returncode=-9,timed_out=False),p))
  self.assertFalse(certified(dict(returncode=0,timed_out=True),p))
  p.with_suffix('.stdout').write_text('CERTIFIED WITH ASSUMPTIONS\n');self.assertFalse(certified(dict(returncode=0,timed_out=False),p))
 def test_exact_cover_improves_greedy_without_arbitrary_cap(self):
  sets=[{1,2,3,4},{1,2,5},{3,4,6},{5},{6}]
  rows=[dict(id=str(i),features=s,time_us=i+1,bytes=i+1) for i,s in enumerate(sets)]
  r=select(rows,seconds=10);self.assertEqual(r['upper_bound'],2);self.assertTrue(r['minimum_cardinality_proved']);self.assertEqual(set(r['selected']),{1,2})
 def test_unique_obligations_are_never_discarded(self):
  rows=[dict(id=str(i),features={i},time_us=1,bytes=1) for i in range(20)]
  r=select(rows,seconds=10);self.assertEqual(len(r['selected']),20);self.assertTrue(r['minimum_cardinality_proved'])
 def test_relative_partition_cannot_be_flattened(self):
  source='(format TRS)(fun f 1)(fun a 0)(rule (f x) x)(rule a (f a) :cost 0)'
  strict='<rule><funapp><name>f</name><var>x</var></funapp><var>x</var></rule>'
  weak='<rule><funapp><name>a</name></funapp><funapp><name>f</name><funapp><name>a</name></funapp></funapp></rule>'
  def document(s,w):return '<certificationProblem><input><trsInput><trs><rules>'+s+'</rules></trs><relativeRules><rules>'+w+'</rules></relativeRules></trsInput></input><property><termination/></property><answer><yes/></answer></certificationProblem>'
  p=self.p/'relative.xml';p.write_text(document(strict,weak));audit_root(source,p,'yes','TRS_Relative')
  p.write_text(document(strict+weak,''))
  with self.assertRaises(ValueError):audit_root(source,p,'yes','TRS_Relative')
 def test_outermost_strategy_cannot_be_lost(self):
  source='(format TRS)(fun a 0)'
  doc='<certificationProblem><input><trsInput><trs><rules/></trs><strategy><outermost/></strategy></trsInput></input><property><termination/></property><answer><yes/></answer></certificationProblem>'
  p=self.p/'outermost.xml';p.write_text(doc);audit_root(source,p,'yes','TRS_Outermost')
  p.write_text(doc.replace('<strategy><outermost/></strategy>',''))
  with self.assertRaises(ValueError):audit_root(source,p,'yes','TRS_Outermost')
if __name__=='__main__':unittest.main()
