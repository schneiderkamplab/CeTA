#!/usr/bin/env python3
"""Independent lookup expansion audit tests, including invalid references."""
import tempfile,unittest
from pathlib import Path
from audit_cpf_sharing import digest
class AuditTests(unittest.TestCase):
 def parse(self,s):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'proof.xml';p.write_text(s);return digest(p)
 def test_expansion_and_significant_text(self):
  explicit='<certificationProblem><lookupTables/><funapp><name>f</name><var> x </var></funapp></certificationProblem>'
  shared='<certificationProblem><lookupTables><termIndexTable><indexToTerm><index>a</index><var> x </var></indexToTerm><indexToTerm><index>b</index><funapp><name>f</name><termIndex>a</termIndex></funapp></indexToTerm></termIndexTable></lookupTables><termIndex>b</termIndex></certificationProblem>'
  self.assertEqual(self.parse(explicit)['expanded_tree_sha256'],self.parse(shared)['expanded_tree_sha256'])
  self.assertNotEqual(self.parse(explicit)['expanded_tree_sha256'],self.parse(explicit.replace(' x ','x'))['expanded_tree_sha256'])
 def test_unknown_forward_duplicate_and_entities(self):
  for body in ['<termIndex>a</termIndex>','<indexToTerm><index>a</index><termIndex>b</termIndex></indexToTerm>','<indexToTerm><index>a</index><var>x</var></indexToTerm>'*2]:
   with self.assertRaises(ValueError):self.parse('<lookupTables><termIndexTable>'+body+'</termIndexTable></lookupTables>')
  with self.assertRaises(ValueError):self.parse('<!DOCTYPE x [<!ENTITY y "z">]><x>&y;</x>')
if __name__=='__main__':unittest.main()
