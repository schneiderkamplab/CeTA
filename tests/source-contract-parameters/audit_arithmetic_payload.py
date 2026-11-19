"""Structural inventory only; does not authenticate observer boundaries."""
from pathlib import Path
import hashlib
import json
import xml.etree.ElementTree as ET
root = Path(__file__).resolve().parents[3]
records = []
for variant in ('original', 'renamed'):
    directory = root / 'ferrum-prolog-release/target/source-contract-development' / variant
    for module in (0, 47):
        ap = directory / f'actions-{module}.xml'
        sp = directory / f'states-{module}.xml'
        action = ET.parse(ap).getroot()[15]
        assert action.tag == 'observedIs'
        target = int(action.findtext('link/target'))
        state = ET.parse(sp).getroot().find('returnStates')[target]
        eq = state.find('frame/goals/unify')
        assert eq is not None and len(eq) == 2 and all(x.tag == 'var' for x in eq)
        output_slot, scalar_slot = (x.text for x in eq)
        bindings = {b[0].text: b[1].text for b in action.findall('link/bindings/binding') if b[1].tag == 'var'}
        assert bindings[scalar_slot] == action.findtext('resultVariable')
        assert bindings[output_slot] != action.findtext('resultVariable')
        payload = state.find('frame/outputs')
        assert payload is not None and len(payload) > 1 and payload[1].tag == 'var'
        parameter_slot = payload[1].text
        assert parameter_slot not in (output_slot, scalar_slot)
        records.append(dict(variant=variant, module=module, row=15, target=target,
                            output_slot=output_slot, scalar_slot=scalar_slot, parameter_slot=parameter_slot, parameter_payload_index=1,
                            authenticated=False, artifacts=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in (ap,sp)]))
print(json.dumps(dict(kind='structural inventory only', records=records), indent=2))
