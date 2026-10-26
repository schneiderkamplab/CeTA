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
        cls.v3 = etree.XMLSchema(etree.parse(str(ROOT/'xml/cpf3.xsd')))
        cls.fixture = (ROOT/'examples/its-div-mod.cpf4.xml').read_bytes()

    def test_v4_positive_v3_rejection(self):
        self.assertTrue(self.v4.validate(etree.fromstring(self.fixture)), self.v4.error_log)
        self.assertFalse(self.v3.validate(etree.fromstring(self.fixture.replace(b'<cpfVersion>4.0', b'<cpfVersion>3.0'))))

    def test_invalid_arities(self):
        for op in ['div','mod']:
            for count in [0,1,3]:
                tree=etree.fromstring(self.fixture)
                node=tree.find('.//'+op)
                for child in list(node): node.remove(child)
                for _ in range(count): etree.SubElement(node,'constant').text='2'
                self.assertFalse(self.v4.validate(tree),(op,count))

    def test_no_other_lts_grammar_changes(self):
        parser=etree.XMLParser(remove_comments=True,remove_blank_text=True)
        old=etree.parse(str(ROOT/'xml/lts.xsd'),parser)
        new=etree.parse(str(ROOT/'xml/lts4.xsd'),parser)
        group=new.getroot().find(f"{NS}group[@name='expression']/{NS}choice")
        for op in ['div','mod']: group.remove(group.find(f"{NS}element[@name='{op}']"))
        self.assertEqual(etree.tostring(old),etree.tostring(new))

if __name__ == '__main__': unittest.main()
