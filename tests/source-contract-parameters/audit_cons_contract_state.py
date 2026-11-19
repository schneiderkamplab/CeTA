"""Check the singleton cons-choice shape used by the six-to-ten contract."""
import copy
import hashlib
import json
from pathlib import Path
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[3] / 'ferrum-prolog-release/target/source-contract-development'


def key(e):
    return e.tag, (e.text or '').strip(), tuple(key(c) for c in e)


def verify(states, actions, subject):
    action = actions[3].find('resolve')
    state = states.find('returnStates')[3]
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
    assert len(head) == 4
    cons = head[1]
    assert cons.tag == 'funapp' and cons.findtext('user') == '2:prolog_data_2e'
    assert len(cons) == 3
    assert all(t.tag == 'var' for t in [cons[1], cons[2], head[2], head[3]])
    x, y, n, out = [t.text for t in [cons[1], cons[2], head[2], head[3]]]
    assert len({x, y, n, out}) == 4
    body = clause.find('body')
    assert len(body) == 2 and all(t.tag == 'atom' for t in body)
    first, second = [t.find('funapp') for t in body]
    assert len(first) == len(second) == 4
    assert all(t.tag == 'var' for t in [*list(first)[1:], *list(second)[1:]])
    fresh = first[3].text
    assert fresh not in {x, y, n, out}
    assert [t.text for t in list(first)[1:]] == [x, n, fresh]
    assert [t.text for t in list(second)[1:]] == [y, fresh, out]
    assert key(second[0]) == key(head[0])
    success, failure = action.findall('link')
    assert len(states.find('returnStates')[int(failure.findtext('target'))]) == 0
    target = states.find('returnStates')[int(success.findtext('target'))]
    assert len(target) == 1
    target_goals = target[0].find('goals')
    assert len(target_goals) == 2 and all(t.tag == 'atom' for t in target_goals)



records = []
for variant in ['original', 'renamed']:
    paths = [ROOT / variant / f'{kind}-35.xml' for kind in ['states', 'actions', 'subject']]
    roots = [ET.parse(p).getroot() for p in paths]
    verify(*roots)
    negatives = []
    for mutation in ['saved_alternative', 'pending_goal', 'repeated_head_parameter', 'missing_recursive_call', 'nonempty_failure']:
        states, actions, subject = copy.deepcopy(roots)
        if mutation == 'saved_alternative': states.find('returnStates')[3].append(copy.deepcopy(states.find('returnStates')[3][0]))
        elif mutation == 'pending_goal': ET.SubElement(states.find('returnStates')[3][0].find('clauseChoice/goals'), 'cut').text = '0'
        elif mutation == 'repeated_head_parameter': subject.find('program')[int(actions[3].findtext('resolve/index'))].find('head/funapp')[3].text = subject.find('program')[int(actions[3].findtext('resolve/index'))].find('head/funapp')[2].text
        elif mutation == 'missing_recursive_call': subject.find('program')[int(actions[3].findtext('resolve/index'))].find('body').clear()
        else:
            failure = int(actions[3].find('resolve').findall('link')[1].findtext('target'))
            states.find('returnStates')[failure].append(copy.deepcopy(states.find('returnStates')[3][0]))
        try: verify(states, actions, subject)
        except (AssertionError, IndexError, AttributeError): negatives.append(mutation)
        else: raise AssertionError(f'accepted {mutation}')
    records.append(dict(variant=variant, region=35, row=3, rejected_mutations=negatives,
                        artifacts={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}))
print(json.dumps(dict(scope='Singleton cons choice, two-call body and empty failure; continuation contract remains an explicit premise', records=records), indent=2))
