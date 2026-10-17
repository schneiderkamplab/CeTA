"""Original-input audits, preserving relative partitions and outermost strategy."""
import copy
import pathlib
import sys
import xml.etree.ElementTree as ET

sys.path.insert(0, str(pathlib.Path(__file__).parent / 'vendor'))
import audit_trs_root_correspondence as trs
import audit_csr_root_correspondence as csr


def sexp(form):
    return '(' + ' '.join(sexp(x) if isinstance(x, list) else x for x in form) + ')'


def compare(source, proof, answer, category):
    if category == 'TRS_Contextsensitive':
        return csr.compare(source, proof.read_text(), answer)
    root = trs.root_metadata(proof)
    if category in trs.CATEGORIES:
        return trs.compare(source, root, answer, category)
    if category == 'TRS_Outermost':
        inp = root.find('./input/trsInput')
        if inp is None or [n.tag for n in inp] != ['trs', 'strategy']:
            raise ValueError('Outermost root context differs')
        strategy = inp.find('strategy')
        if len(strategy) != 1 or strategy[0].tag != 'outermost' or len(strategy[0]):
            raise ValueError('Outermost strategy missing or ambiguous')
        inp.remove(strategy)
        result = trs.compare(source, root, answer, 'TRS_Standard')
        return result | dict(strategy='outermost', strategy_equal=True)
    if category not in {'TRS_Relative', 'SRS_Relative'}:
        raise ValueError('Unsupported input category: ' + category)
    # Keep each partition distinct. A third combined audit checks symbol
    # spelling injectivity across the strict/weak boundary as well.
    declarations, strict, weak = [], [], []
    for command in csr.forms(source):
        if command[0] != 'rule':
            declarations.append(command)
        elif len(command) == 3:
            strict.append(command)
        elif len(command) == 5 and command[3] == ':cost' and command[4] in {'0', '1'}:
            (weak if command[4] == '0' else strict).append(command[:3])
        else:
            raise ValueError('Unsupported relative rule annotation')
    inp = root.find('./input/trsInput')
    if inp is None or [n.tag for n in inp] != ['trs', 'relativeRules']:
        raise ValueError('Relative root must contain exactly strict and weak rules')
    if [n.tag for n in inp[0]] != ['rules'] or [n.tag for n in inp[1]] != ['rules']:
        raise ValueError('Unexpected relative rule context')
    result = {}
    for label, commands, nodes in [('strict', strict, list(inp[0][0])),
                                   ('weak', weak, list(inp[1][0])),
                                   ('combined', strict + weak, list(inp[0][0]) + list(inp[1][0]))]:
        partition = copy.deepcopy(root)
        target = partition.find('./input/trsInput')
        target.clear()
        rules = ET.SubElement(ET.SubElement(target, 'trs'), 'rules')
        rules.extend(copy.deepcopy(nodes))
        text = '\n'.join(sexp(c) for c in declarations + commands)
        result[label] = trs.compare(text, partition, answer, 'TRS_Standard')
    return dict(strategy='relative-full', strategy_equal=True, strict_and_weak_multisets_equal=True,
                answer=answer, partitions=result)
