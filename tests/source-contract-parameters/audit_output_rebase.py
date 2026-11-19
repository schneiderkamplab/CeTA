"""Inventory the retained equality boundary; no dynamic link certification."""
from pathlib import Path
import hashlib
import json
import xml.etree.ElementTree as ET
root = Path(__file__).resolve().parents[3]
records = []
for variant in ('original','renamed'):
    directory = root / 'ferrum-prolog-release/target/source-contract-development' / variant
    target_path = directory / 'states-19.xml'
    target = ET.parse(target_path).getroot().find('returnStates')[0]
    assert len(target) == 1
    target_frame = target.find('frame')
    new_payload = target_frame.find('outputs')
    encode = lambda e: ET.tostring(e)
    for module in (0,47):
        source_path = directory / f'states-{module}.xml'
        source = ET.parse(source_path).getroot().find('returnStates')[19]
        assert len(source) == 1
        source_frame = source.find('frame')
        old_payload = source_frame.find('outputs')
        assert encode(source_frame.find('goals')) == encode(target_frame.find('goals'))
        equality = source_frame.find('goals/unify')
        assert len(old_payload) == 3 and len(new_payload) == 2
        assert encode(old_payload[2]) == encode(new_payload[0]) == encode(equality[0])
        assert encode(new_payload[1]) == encode(equality[1])
        assert all(encode(new_payload[1]) != encode(old) for old in old_payload)
        assert encode(new_payload[1]) != encode(old_payload[2])
        records.append(dict(variant=variant,source_module=module,source_row=19,target_module=19,
                            target_row=0,old_output_index=2,new_output_index=0,
                            scalar_not_a_projection=True,wrong_output_index_rejected=1,
                            artifacts={str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                                       for p in (source_path,target_path)}))
print(json.dumps(dict(scope='structural correspondence only; runtime representation and checked link remain premises',records=records),indent=2))
