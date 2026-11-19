"""Audit simple cons successor payload/context against the checked theorem interface."""
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import runpy
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):
    coordinates = runpy.run_path(str(HERE / 'audit_cons_five_coordinates.py'))
ROOT = coordinates['ROOT']

def tree(e):
    return e.tag, (e.text or '').strip(), tuple(tree(c) for c in e)

def verify(states, actions, subject):
    target, slots = coordinates['verify'](states, actions, subject, 3)
    assert target == 7
    h, p, fresh, tail, out = slots
    cons = f'<funapp><user>2:prolog_data_2e</user><var>{h}</var><var>{tail}</var></funapp>'
    payload = f'<outputs>{cons}<var>{p}</var><var>{out}</var></outputs>'
    frames = states.find('returnStates')[target].findall('frame')
    assert len(frames) == 1
    assert tree(frames[0].find('outputs')) == tree(ET.fromstring(payload))
    context = f'''<sourceContext><facts/><guards><opaqueGuard><var>{p}</var></opaqueGuard></guards>
    <observations><groundGuard><var>{p}</var></groundGuard><returnShape><grammar><shapeNode>
    <production><symbol><user>0:prolog_data_5b5d</user></symbol><arguments/></production>
    <production><symbol><user>2:prolog_data_2e</user></symbol><arguments><any/><node>0</node></arguments></production>
    </shapeNode></grammar><shape><node>0</node></shape><term>{cons}</term></returnShape></observations></sourceContext>'''
    assert tree(states.find('contexts')[target]) == tree(ET.fromstring(context))
    assert tree(states.find('freeContexts')[target]) == tree(ET.fromstring(f'<free><var>{fresh}</var></free>'))
    assert tree(states.find('functorContexts')[target]) == tree(ET.fromstring('<functors/>'))
    assert tree(states.find('separationContexts')[target]) == tree(ET.fromstring('<separation/>'))

records = []
for variant in ['original', 'renamed']:
    paths = [ROOT / variant / f'{kind}-35.xml' for kind in ['states', 'actions', 'subject']]
    roots = [ET.parse(p).getroot() for p in paths]
    verify(*roots)
    mutations = {
        'wrong_payload_head': 'returnStates/returnState[8]/frame/outputs/funapp/var',
        'wrong_payload_parameter': 'returnStates/returnState[8]/frame/outputs/var',
        'wrong_payload_output': 'returnStates/returnState[8]/frame/outputs/var[2]',
        'wrong_ground_coordinate': 'contexts/sourceContext[8]/observations/groundGuard/var',
        'wrong_shape_coordinate': 'contexts/sourceContext[8]/observations/returnShape/term/funapp/var',
        'growing_spine_grammar': 'contexts/sourceContext[8]/observations/returnShape/grammar/shapeNode/production[2]/arguments/node',
        'wrong_free_coordinate': 'freeContexts/free[8]/var',
    }
    rejected = []
    for name, path in mutations.items():
        altered = copy.deepcopy(roots)
        element = altered[0].find(path)
        assert element is not None, path
        element.text = 'wrong'
        try:
            verify(*altered)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(name)
    altered = copy.deepcopy(roots)
    outputs = altered[0].find('returnStates')[7].find('frame/outputs')
    outputs.remove(outputs[-1])
    try:
        verify(*altered)
    except AssertionError:
        rejected.append('missing_output')
    else:
        raise AssertionError('missing_output')
    records.append(dict(variant=variant, region=35, source=3, target=7, rejected=rejected,
                        artifacts={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}))
print(json.dumps(dict(scope='Simple cons successor total payload and ordinary contexts; conditional theorem interface only', records=records), indent=2))
