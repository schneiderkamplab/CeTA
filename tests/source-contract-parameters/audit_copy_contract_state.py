"""Check the singleton copy-choice shape used by the six-to-two contract."""
import copy
import hashlib
import json
from pathlib import Path
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[3] / 'ferrum-prolog-release/target/source-contract-development'


def key(e):
    return e.tag, (e.text or '').strip(), tuple(key(c) for c in e)


def verify(states, actions, subject):
    action = actions[2].find('resolve')
    state = states.find('returnStates')[2]
    assert len(state) == 1
    frame = state[0]
    choice = frame.find('clauseChoice')
    goals = choice.find('goals')
    assert len(goals) == 1 and goals[0].tag == 'atom'
    call = goals[0][0]
    assert key(call) == key(action.find('funapp'))
    assert len(call) == 4
    assert all(t.tag == 'var' for t in list(call)[1:])
    assert [key(t) for t in frame.find('outputs')] == [key(t) for t in list(call)[1:]]
    assert choice.findtext('index') == action.findtext('index')
    assert choice.findtext('scope') == action.findtext('scope')
    assert len(action.find('goals')) == len(action.find('returnState')) == 0
    clause = subject.find('program')[int(action.findtext('index'))]
    head = clause.find('head/funapp')
    assert key(head[0]) == key(call[0])
    assert len(head) == 4 and head[2].tag == 'var' and key(head[2]) == key(head[3])
    assert key(head[1]) == ('funapp', '', (('user', '0:prolog_data_5b5d', ()),))
    assert key(clause.find('body')) == ('body', '', (('cut', '0', ()),))
    success, failure = action.findall('link')
    assert len(states.find('returnStates')[int(failure.findtext('target'))]) == 0
    target = states.find('returnStates')[int(success.findtext('target'))]
    assert len(target) == 1
    assert key(target[0].find('goals')) == ('goals', '', (('cut', choice.findtext('scope'), ()),))


records = []
for variant in ['original', 'renamed']:
    paths = [ROOT / variant / f'{kind}-35.xml' for kind in ['states', 'actions', 'subject']]
    roots = [ET.parse(p).getroot() for p in paths]
    verify(*roots)
    negatives = []
    for mutation in ['saved_alternative', 'pending_goal', 'different_parameter_head', 'missing_cut', 'nonempty_failure']:
        states, actions, subject = copy.deepcopy(roots)
        if mutation == 'saved_alternative': states.find('returnStates')[2].append(copy.deepcopy(states.find('returnStates')[2][0]))
        elif mutation == 'pending_goal': ET.SubElement(states.find('returnStates')[2][0].find('clauseChoice/goals'), 'cut').text = '0'
        elif mutation == 'different_parameter_head': subject.find('program')[int(actions[2].findtext('resolve/index'))].find('head/funapp')[3].text = 'Other'
        elif mutation == 'missing_cut': subject.find('program')[int(actions[2].findtext('resolve/index'))].find('body').clear()
        else:
            failure = int(actions[2].find('resolve').findall('link')[1].findtext('target'))
            states.find('returnStates')[failure].append(copy.deepcopy(states.find('returnStates')[2][0]))
        try: verify(states, actions, subject)
        except (AssertionError, IndexError, AttributeError): negatives.append(mutation)
        else: raise AssertionError(f'accepted {mutation}')
    records.append(dict(variant=variant, region=35, row=2, rejected_mutations=negatives,
                        artifacts={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}))
print(json.dumps(dict(scope='Singleton state and clause audit; continuation contract remains an explicit premise', records=records), indent=2))
