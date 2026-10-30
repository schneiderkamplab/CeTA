#!/usr/bin/env python3
"""Exercise the generated contextual source-table parser and rejection paths."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET
from xml.sax.saxutils import escape
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--native-context', type=Path, help='native integer(7) observation fixture')
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
def field(tag, content=''):
    return f'<{tag}>{content}</{tag}>'
def user(s):
    return field('user', escape(s))
def term(s, args=()):
    return field('funapp', user(s) + ''.join(args))
def integer(n):
    return term('0:prolog_data_' + ('\0prolog.integer:' + str(n)).encode().hex())
def node(name, state):
    return field('node', field('state', state) + '<ground/><guards/><variables/>' + field('symbol', user(name)))
def returns(state):
    return field('returnState', field('frame', state + '<outputs/>') if state else '')
def link(index, state):
    return field('link', field('target', str(index)) + '<variables/><terms/>' + field('state', state)
                 + '<ground/><guards/><bindings/><swaps/><lhs/><rhs/>')
def atom(name):
    return term(name)
def clause(before, after):
    return field('clause', field('head', atom(before)) + field('body', atom(after)))
def context(guards='', observations=''):
    return field('sourceContext', '<facts/>' + field('guards', guards) + field('observations', observations))
source = field('goals', field('atom', term('1:integer', [integer(7)])))
success = '<goals/>'
observed = field('integerGuard', integer(7))
fixture = field('prologContextTable', '<program/><fuel>40</fuel><root>0</root>'
    + field('nodes', node('source', source) + node('yes', success) + node('no', ''))
    + field('returnStates', returns(source) + returns(success) + returns(''))
    + field('contexts', context() + context(observed, observed) + context())
    + '<typings><facts/><facts/><facts/></typings>'
    + '<prologSuccessTransferContract><summaries/><successProgram/><proofs/></prologSuccessTransferContract>'
    + field('returnSymbol', user('returned')) + '<returnArity>0</returnArity>'
    + field('actions', field('integerTest', integer(7) + '<goals/><active/><returnState/>' + link(1, success) + link(2, ''))
            + field('cut', field('admin', '<returned/><returnState/>' + link(2, '')))
            + '<cut><terminal/></cut>')
    + field('residual', clause('source', 'yes') + clause('source', 'no') + clause('yes', 'no') + clause('yes', 'returned')))
root = ET.fromstring(fixture)
results = []
def check(name, tree, expected):
    path = a.output / (name + '.xml')
    ET.ElementTree(tree).write(path, encoding='unicode')
    run = subprocess.run([str(a.checker.resolve()), str(path.resolve())], capture_output=True, text=True, timeout=30)
    results.append(dict(name=name, expected=expected, accepted=run.returncode == 0,
                        returncode=run.returncode, stdout=run.stdout, stderr=run.stderr))
check('complete-table', root, True)
if a.native_context:
    changed = copy.deepcopy(root)
    contexts = changed.find('contexts')
    contexts.remove(contexts[1])
    contexts.insert(1, ET.parse(a.native_context).getroot())
    check('native-context-in-complete-table', changed, True)
for tag in ('nodes', 'returnStates', 'contexts', 'typings', 'actions', 'residual'):
    changed = copy.deepcopy(root)
    changed.find(tag).remove(changed.find(tag)[0])
    check('missing-' + tag, changed, False)
changed = copy.deepcopy(root)
changed.find('contexts')[0].find('guards').append(ET.fromstring(observed))
check('unproved-root-fact', changed, False)
changed = copy.deepcopy(root)
changed.find('contexts')[2].find('guards').append(ET.fromstring(observed))
check('integer-fact-on-failure', changed, False)
changed = copy.deepcopy(root)
changed.find('root').text = '3'
check('root-out-of-range', changed, False)
changed = copy.deepcopy(root)
changed.find('actions/integerTest/link/target').text = '2'
check('swapped-success-target', changed, False)
changed = copy.deepcopy(root)
changed.find('contexts')[1].find('observations').append(ET.fromstring(field('integerGuard', integer(8))))
check('unobserved-integer-value', changed, False)
report = dict(source_certified=False, checker_sha256=hashlib.sha256(a.checker.read_bytes()).hexdigest(), results=results)
(a.output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
failed = [r['name'] for r in results if r['accepted'] != r['expected'] or r['returncode'] not in (0, 1)]
if failed:
    raise SystemExit('failed context-table checks: ' + ', '.join(failed))
print(f'{len(results)} source-context XML checks passed; no source verdict')
