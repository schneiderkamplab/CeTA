"""Audit source copy successor coordinates, payloads and functor facts."""
from pathlib import Path
import copy
import hashlib
import json
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[3] / 'ferrum-prolog-release/target/source-contract-development'


def term(e):
    return (e.tag, e.text or '', tuple(term(c) for c in e))


def variable(e):
    assert e.tag == 'var' and not list(e)
    return e.text


def substituted(e, bindings):
    if e.tag == 'var':
        return term(bindings.get(e.text, e))
    return (e.tag, e.text or '', tuple(substituted(c, bindings) for c in e))


def prefixed(prefix, e):
    return ('var', '$' * prefix + variable(e), ())


def verify(states, action, subject, row, with_functor):
    resolve = action.find('resolve')
    clause = subject.find('program')[int(resolve.findtext('index'))]
    head = clause.find('head/funapp')
    head_args = list(head)[1:]
    call_args = list(resolve.find('funapp'))[1:]
    assert len(head_args) == len(call_args) == 3
    assert term(head_args[1]) == term(head_args[2])
    link = resolve.findall('link')[0]
    target = int(link.findtext('target'))
    source_payload = list(states.find('returnStates')[row].find('frame/outputs'))
    target_payload = list(states.find('returnStates')[target].find('frame/outputs'))
    assert len(source_payload) == len(target_payload) == 3
    assert [term(t) for t in source_payload] == [term(t) for t in resolve.find('active')]
    k, l = int(resolve.findtext('activePrefix')), int(resolve.findtext('clausePrefix'))
    assert 2*k <= l
    bindings = {variable(list(b)[0]): list(b)[1] for b in link.find('bindings')}
    assert len(bindings) == len(link.find('bindings'))
    assert substituted(target_payload[1], bindings) == prefixed(l, head_args[1])
    assert term(target_payload[2]) == term(target_payload[1])
    assert [term(t) for t in source_payload[1:]] == [term(t) for t in call_args[1:]]
    assert states.find('returnStates')[target].find('frame/goals/cut') is not None
    if with_functor:
        source_facts = states.find('functorContexts')[row]
        target_facts = states.find('functorContexts')[target]
        assert len(source_facts) == len(target_facts) == 1
        source_terms, target_terms = list(source_facts[0]), list(target_facts[0])
        assert len(source_terms) == len(target_terms) == 3
        assert term(source_terms[0]) == term(source_payload[0])
        assert term(source_terms[2]) == term(call_args[0])
        assert term(target_terms[0]) == term(target_payload[0])
        assert term(target_terms[2]) == term(head_args[0])
        assert len(variable(source_terms[0])) < k and len(variable(source_terms[1])) < k
        assert substituted(target_terms[0], bindings) == prefixed(k, source_terms[0])
        assert substituted(target_terms[1], bindings) == term(source_terms[1])
    else:
        assert term(source_payload[0]) == term(call_args[0])
        assert term(target_payload[0]) == term(head_args[0])
    return target, k, l


def rejects(states, action, subject, row, with_functor):
    try:
        verify(states, action, subject, row, with_functor)
    except (AssertionError, IndexError, AttributeError, KeyError):
        return True
    return False


records = []
for variant in ['original', 'renamed']:
    for region, row, with_functor in [('0', 22, True), ('35', 2, False)]:
        paths = [ROOT/variant/f'{kind}-{region}.xml' for kind in ['states', 'actions', 'subject']]
        states, actions, subject = [ET.parse(p).getroot() for p in paths]
        action = actions[row]
        target, k, l = verify(states, action, subject, row, with_functor)
        negatives = []
        broken = copy.deepcopy(action)
        bindings = broken.find('resolve/link/bindings')
        bindings.remove(bindings[0])
        assert rejects(states, broken, subject, row, with_functor)
        negatives.append('missing_parameter_binding')
        broken = copy.deepcopy(states)
        payload = broken.find('returnStates')[target].find('frame/outputs')
        payload[2].text = 'forged_output'
        assert rejects(broken, action, subject, row, with_functor)
        negatives.append('wrong_output_payload')
        broken = copy.deepcopy(action)
        broken.find('resolve/clausePrefix').text = str(l+1)
        assert rejects(states, broken, subject, row, with_functor)
        negatives.append('wrong_clause_prefix')
        if with_functor:
            broken = copy.deepcopy(states)
            broken.find('functorContexts')[target].clear()
            assert rejects(broken, action, subject, row, True)
            negatives.append('missing_functor_fact')
            broken = copy.deepcopy(action)
            b = broken.find('resolve/link/bindings')[-1]
            b[1].text = b[1].text[k:]
            assert rejects(states, broken, subject, row, True)
            negatives.append('stale_unrefreshed_functor')
        records.append(dict(variant=variant, region=region, row=row, target=target,
            active_prefix=k, clause_prefix=l, complete_payload_checked=True,
            functor_coordinates_checked=with_functor, rejected_mutations=negatives,
            artifacts={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}))
print(json.dumps(dict(scope='Executable source-coordinate audit; kernel theorem handles actual MGU and observations; full row contract remains open', records=records), indent=2))
