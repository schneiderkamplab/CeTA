#!/usr/bin/env python3
"""Exercise the observed empty-weak boundary and a lost-partition rejection."""
import gzip,pathlib,tempfile,unittest
from root_audit import compare
ROOT=pathlib.Path(__file__).resolve().parents[2]

class RelativeInputAudit(unittest.TestCase):
    def test_empty_weak_partition_only(self):
        source=ROOT/'tests/certification/frontier-20261018/6e6ea9f6e2102a8185147376'
        original=(source/'input.ari').read_text()
        with tempfile.TemporaryDirectory(dir=ROOT/'target') as temp:
            proof=pathlib.Path(temp)/'proof.xml'
            proof.write_bytes(gzip.decompress((source/'proof.cpf.xml.gz').read_bytes()))
            audit=compare(original,proof,'yes','SRS_Relative')
            self.assertTrue(audit['omitted_empty_weak_rules'])
            altered=original.replace('(rule (a (c (a x1))) (b (a (c x1))))',
                '(rule (a (c (a x1))) (b (a (c x1))) :cost 0)')
            self.assertNotEqual(original,altered)
            with self.assertRaisesRegex(ValueError,'exactly strict and weak rules'):
                compare(altered,proof,'yes','SRS_Relative')

if __name__=='__main__':unittest.main()
