import tempfile
from pathlib import Path
import unittest
from check_okf import check

class BundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write('index.md', '---\nokf_version: "0.2"\n---\n# Docs\n\n- [A](a.md)\n- [Log](log.md)\n')
        self.write('log.md', '# Log\n\n## 2026-10-28\n\n- Created.\n')
        self.write('a.md', '---\ntype: Specification\n---\n# A\n')
    def write(self, name, text):
        (self.root/name).write_text(text)
    def test_valid(self):
        self.assertEqual(check(self.root), [])
    def test_missing_type(self):
        self.write('a.md', '# A\n')
        self.assertTrue(check(self.root))
    def test_bad_yaml(self):
        self.write('a.md', '---\ntype: [\n---\n')
        self.assertTrue(check(self.root))
    def test_unlisted_concept(self):
        self.write('b.md', '---\ntype: Report\n---\n')
        self.assertTrue(check(self.root))
    def test_log_order(self):
        self.write('log.md', '# Log\n## 2026-10-27\n- Old\n## 2026-10-28\n- New\n')
        self.assertTrue(check(self.root))
    def test_missing_bundle(self):
        self.assertTrue(check(self.root/'absent'))
    def test_root_version_required(self):
        self.write('index.md', '# Index\n')
        self.assertTrue(check(self.root))

if __name__ == '__main__':
    unittest.main()
