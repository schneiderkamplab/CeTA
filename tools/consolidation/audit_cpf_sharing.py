#!/usr/bin/env python3
"""Independently compare CPF trees after resolving sequential lookup terms.

Streaming Expat/Merkle audit: no expanded copy or recursive term traversal.
Table indices must be unique and references must already be defined.
"""
import argparse, hashlib, json
from pathlib import Path
from xml.parsers import expat

def field(h, data):
    data = data.encode() if isinstance(data, str) else data
    h.update(len(data).to_bytes(8, 'big')); h.update(data)

class Node:
    def __init__(self, tag, attrs):
        self.tag, self.attrs = tag, attrs
        self.hash = hashlib.sha256(); field(self.hash, tag)
        for k, v in sorted(attrs.items()): field(self.hash, k); field(self.hash, v)
        self.text = []; self.children = []; self.count = 0
    def flush(self):
        if self.text:
            text = ''.join(self.text); self.text.clear()
            if text: self.hash.update(b'T'); field(self.hash, text)
    def child(self, info):
        self.hash.update(b'C'); field(self.hash, info[1]); self.count += 1
        if self.tag in ('indexToTerm', 'termIndexTable', 'lookupTables'):
            if self.tag != 'termIndexTable': self.children.append(info)

def digest(path):
    parser = expat.ParserCreate(); stack = []; terms = {}; result = None
    counts = dict(table_entries=0, references=0)
    def start(tag, attrs):
        if stack: stack[-1].flush()
        stack.append(Node(tag, attrs))
    def end(tag):
        nonlocal result
        node = stack.pop(); assert tag == node.tag
        text = ''.join(node.text); node.flush()
        info = (tag, node.hash.digest(), text)
        if tag == 'termIndex':
            if node.attrs or node.count or text not in terms: raise ValueError('Invalid or forward termIndex: '+text)
            info = terms[text]; counts['references'] += 1
        elif tag == 'indexToTerm':
            if node.attrs or len(node.children) != 2 or node.children[0][0] != 'index' or node.children[1][0] not in ('var','funapp'):
                raise ValueError('Malformed term table entry')
            index = node.children[0][2]
            if index in terms: raise ValueError('Duplicate term index: '+index)
            terms[index] = node.children[1]; counts['table_entries'] += 1
        elif tag == 'lookupTables':
            if node.attrs or any(c[0] != 'termIndexTable' for c in node.children): raise ValueError('Unsupported lookup-table form')
            empty = Node('lookupTables', {}); info = ('lookupTables', empty.hash.digest(), '')
        if stack: stack[-1].child(info)
        else: result = info[1].hex()
    def text(s):
        if stack: stack[-1].text.append(s)
    def forbid(*args): raise ValueError('DTD/entities are unsupported')
    parser.StartElementHandler = start; parser.EndElementHandler = end
    parser.CharacterDataHandler = text; parser.StartDoctypeDeclHandler = forbid
    parser.EntityDeclHandler = forbid
    with Path(path).open('rb') as stream:
        while data := stream.read(1024*1024): parser.Parse(data, False)
    parser.Parse(b'', True)
    assert result is not None and not stack
    return dict(expanded_tree_sha256=result, **counts)

def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('original', type=Path); p.add_argument('shared', type=Path); p.add_argument('--output', type=Path)
    a = p.parse_args(); before, after = digest(a.original), digest(a.shared)
    if before['expanded_tree_sha256'] != after['expanded_tree_sha256']: raise ValueError('Expanded CPF tree differs')
    report = dict(equal=True, original=before, shared=after)
    if a.output: a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))
if __name__ == '__main__': main()
