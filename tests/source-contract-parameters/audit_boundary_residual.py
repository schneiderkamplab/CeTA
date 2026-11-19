"""Audit local residual heads; does not certify the retained global residual."""
from pathlib import Path
import hashlib
import json
import xml.etree.ElementTree as ET
root = Path(__file__).resolve().parents[3]
records = []
artifacts = {}
for variant in ('original', 'renamed'):
    directory = root / 'ferrum-prolog-release/target/source-contract-development' / variant
    residuals = {}
    for module in (0, 19, 28, 35, 47):
        path = directory / f'subject-{module}.xml'
        residuals[module] = ET.parse(path).getroot().find('residual')
        artifacts[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    heads = {cl.find('head/funapp/user').text for q in residuals.values() for cl in q}
    for module in (0, 47):
        path = directory / f'states-{module}.xml'
        nodes = ET.parse(path).getroot().find('nodes')
        boundary = nodes[19].find('symbol/user').text
        predecessor = nodes[15].find('symbol/user').text
        assert boundary not in heads
        assert predecessor in heads  # Positive control: real arithmetic head is found.
        incoming = [cl for cl in residuals[module]
                    if cl.find('head/funapp/user').text == predecessor
                    and any(x.text == boundary for x in cl.findall('body/funapp/user'))]
        assert len(incoming) == 1
        artifacts[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        records.append(dict(variant=variant, module=module, row=19, predicate=boundary,
                            absent_from_all_five_local_residual_heads=True,
                            arithmetic_predecessor_found=True, incoming_arithmetic_clause_count=1))
print(json.dumps(dict(scope='Five retained local residuals and their union only; not the certified global residual',
                      records=records, artifacts=artifacts), indent=2))
