"""Retained coordinate inventory; not a source-family certificate."""
from pathlib import Path
import hashlib
import json
import xml.etree.ElementTree as ET
root = Path(__file__).resolve().parents[3]
records = []
for variant in ('original', 'renamed'):
    directory = root / 'ferrum-prolog-release/target/source-contract-development' / variant
    for module, row, kind, index in ((0,22,'copy',2),(35,2,'copy',2),
                                    (0,15,'arithmetic',2),(47,15,'arithmetic',2),
                                    (0,19,'equality',2),(47,19,'equality',2),(19,0,'equality',0)):
        path = directory / f'states-{module}.xml'
        frame = ET.parse(path).getroot().find('returnStates')[row].find('frame')
        payload = frame.find('outputs')
        if kind == 'copy':
            active = frame.find('clauseChoice/goals/atom/funapp')[3]
        elif kind == 'arithmetic':
            active = frame.find('goals/atom/funapp')[1]
        else:
            active = frame.find('goals/unify')[0]
        same = lambda a,b: ET.tostring(a)==ET.tostring(b)
        assert index < len(payload) and same(payload[index],active)
        wrong = (index + 1) % len(payload)
        assert not same(payload[wrong],active)
        records.append(dict(variant=variant,module=module,row=row,kind=kind,
                            output_payload_index=index,wrong_index_rejected=wrong,
                            sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
print(json.dumps(dict(scope='structural coordinates only; dynamic aliases require initialization and transport',
                      records=records),indent=2))
