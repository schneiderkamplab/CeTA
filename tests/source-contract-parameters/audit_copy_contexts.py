"""Match retained copy-successor contexts to the conditional kernel results.

This audits fixtures; it does not discharge recursive node conditions.
"""
import copy
import hashlib
import json
from pathlib import Path
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[3] / 'ferrum-prolog-release/target/source-contract-development'


def key(e):
    return e.tag, (e.text or '').strip(), tuple(key(c) for c in e)


def verify(root, row, functor):
    payload = list(root.find('returnStates')[row].find('frame/outputs'))
    node = root.find('nodes')[row]
    ctx = root.find('contexts')[row]
    assert len(ctx.find('facts')) == 0
    assert all(g.tag == 'opaqueGuard' for g in ctx.find('guards'))
    assert len(node.find('guards')) == 0
    for tag in ['freeContexts', 'separationContexts']:
        assert len(root.find(tag)[row]) == 0
    obs = list(ctx.find('observations'))
    assert len(obs) == 2
    shape = obs[1]
    assert shape.tag == 'returnShape'
    assert shape.findtext('shape/node') == '0'
    grammar = shape.find('grammar')
    assert len(grammar) == 1
    productions = list(grammar[0])
    assert len(productions) == 2
    nil = productions[0].findtext('symbol/user')
    cons = productions[1].findtext('symbol/user')
    assert nil == '0:prolog_data_5b5d' and cons == '2:prolog_data_2e'
    assert len(productions[0].find('arguments')) == 0
    assert key(productions[1].find('arguments')) == ('arguments', '', (('any', '', ()), ('node', '0', ())))
    empty = ET.fromstring('<funapp><user>0:prolog_data_5b5d</user></funapp>')
    assert key(shape.find('term')[0]) == key(empty)
    if functor:
        assert obs[0].tag == 'sourceEquation'
        assert [key(t) for t in obs[0]] == [key(payload[0])]*2
        fact = root.find('functorContexts')[row][0]
        assert len(root.find('functorContexts')[row]) == 1
        assert [key(t) for t in fact] == [key(payload[0]), key(node.find('ground')[1]), key(empty)]
        assert [key(t) for t in node.find('ground')] == [key(payload[1]), key(fact[1])]
    else:
        assert obs[0].tag == 'groundGuard' and key(obs[0][0]) == key(payload[1])
        assert len(node.find('ground')) == len(root.find('functorContexts')[row]) == 0
        assert key(payload[0]) == key(empty)
        assert [key(g[0]) for g in ctx.find('guards')] == [key(payload[1])]


records = []
for variant in ['original', 'renamed']:
    for region, row, functor in [('0', 25, True), ('35', 5, False)]:
        path = ROOT / variant / f'states-{region}.xml'
        root = ET.parse(path).getroot()
        verify(root, row, functor)
        mutations = []
        for kind in ['missing_observation', 'wrong_shape_node', 'nonempty_nil', 'extra_separation', 'wrong_observed_coordinate']:
            bad = copy.deepcopy(root)
            observations = bad.find('contexts')[row].find('observations')
            if kind == 'missing_observation': observations.remove(observations[0])
            elif kind == 'wrong_shape_node': observations[1].find('shape/node').text = '1'
            elif kind == 'nonempty_nil': ET.SubElement(observations[1].find('term/funapp'), 'var').text = 'X'
            elif kind == 'extra_separation': ET.SubElement(bad.find('separationContexts')[row], 'separation')
            else: observations[0][0].text = 'wrong_coordinate'
            try: verify(bad, row, functor)
            except (AssertionError, IndexError, AttributeError): mutations.append(kind)
            else: raise AssertionError(f'accepted {kind}')
        records.append(dict(variant=variant, region=region, row=row, rejected=mutations,
                            artifact=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
print(json.dumps(dict(scope='Retained target contexts only; full row assembly remains open', records=records), indent=2))
