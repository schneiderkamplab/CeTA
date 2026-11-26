"""Schema tests only: these do not claim checker support or soundness."""
import pathlib
import unittest
from lxml import etree
ROOT = pathlib.Path(__file__).resolve().parents[1]
NS = '{http://www.w3.org/2001/XMLSchema}'

class DivModSchema(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.v4 = etree.XMLSchema(etree.parse(str(ROOT/'xml/cpf4.xsd')))
        cls.v5 = etree.XMLSchema(etree.parse(str(ROOT/'xml/cpf5.xsd')))
        cls.legacy = etree.XMLSchema(etree.parse(str(ROOT/'xml/cpf4-legacy-its.xsd')))
        cls.v3 = etree.XMLSchema(etree.parse(str(ROOT/'xml/cpf3.xsd')))
        cls.fixture = (ROOT/'examples/its-div-mod.cpf4.xml').read_bytes()

    def test_v5_positive_earlier_rejection(self):
        self.assertTrue(self.legacy.validate(etree.fromstring(self.fixture)))
        self.assertFalse(self.v4.validate(etree.fromstring(self.fixture)))
        self.assertTrue(self.v5.validate(etree.fromstring(self.fixture.replace(b"<cpfVersion>4.0", b"<cpfVersion>5.0"))), self.v5.error_log)
        self.assertFalse(self.v3.validate(etree.fromstring(self.fixture.replace(b'<cpfVersion>4.0', b'<cpfVersion>3.0'))))

    def test_invalid_arities(self):
        for op in ['div','mod']:
            for count in [0,1,3]:
                tree=etree.fromstring(self.fixture)
                node=tree.find('.//'+op)
                for child in list(node): node.remove(child)
                for _ in range(count): etree.SubElement(node,'constant').text='2'
                self.assertFalse(self.v5.validate(tree),(op,count))

    def test_v4_inherits_original_lts(self):
        tree=etree.parse(str(ROOT/'xml/cpf4.xsd'))
        self.assertEqual(tree.find(NS+'include').get('schemaLocation'),'lts.xsd')
        self.assertFalse(tree.findall(".//"+NS+"element[@name='ltsNonterminationProof']"))

if __name__ == '__main__': unittest.main()
