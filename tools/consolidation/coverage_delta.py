#!/usr/bin/env python3
"""Map unchanged HPC expressions; expose every required unmapped counter.

This is evidence for review, not permission to retire an executable obligation.
Changed expressions and their encompassing boxes remain explicit gaps.
"""
import argparse, ast, collections, difflib, json, pathlib, re
from replay import sha, write
from suite import inside

TOKEN = r'''"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'|\S'''


def read_mix(path):
    modules = collections.defaultdict(list)
    for line in path.read_text().splitlines():
        module, digest, tick, source, position, label = line.split('\t')
        modules[module].append(dict(hash=digest, tick=int(tick), source=source,
                                   position=ast.literal_eval(position), label=label))
    return modules


def excerpt(lines, span):
    start, col, end, last = span
    if start == end:
        return lines[start-1][col-1:last]
    return '\n'.join([lines[start-1][col-1:], *lines[start:end-1], lines[end-1][:last]])


def token_spans(lines):
    # Keep quoted literals intact: whitespace inside strings is semantic.
    source = '\n'.join(lines)
    tokens = list(re.finditer(TOKEN, source))
    starts, ends, line_starts = {}, {}, [0]
    line_starts.extend(m.end() for m in re.finditer('\n', source))
    for i, token in enumerate(tokens):
        starts[token.start()] = i
        ends[token.end()] = i
    def span(position):
        first, col, last, end = position
        left = starts.get(line_starts[first-1]+col-1)
        right = ends.get(line_starts[last-1]+end)
        return (left,right) if left is not None and right is not None else None
    return [t.group() for t in tokens], span


def main():
    p = argparse.ArgumentParser()
    for flag in ['old-mix', 'new-mix', 'old-source', 'new-source', 'denominator', 'output']:
        p.add_argument('--'+flag, type=pathlib.Path, required=True)
    a = p.parse_args()
    old, new = read_mix(a.old_mix), read_mix(a.new_mix)
    denominator = json.loads(a.denominator.read_text())
    required = set(denominator['required_obligations'])
    mappings, gaps, reports = [], [], []
    for module, meta in denominator['modules'].items():
        entries = old.get(module, [])
        if len(entries) != meta['count'] or any(e['hash'] != meta['hash'] for e in entries):
            raise ValueError('Old Mix does not match frozen denominator: '+module)
        if not entries:
            continue
        old_path = inside(a.old_source.resolve(), entries[0]['source'])
        old_lines = old_path.read_text().splitlines()
        current = new.get(module, [])
        new_path = inside(a.new_source.resolve(), current[0]['source']) if current else None
        new_lines = new_path.read_text().splitlines() if new_path else []
        alignment = {i:i for i in range(1,len(old_lines)+1)} if old_lines == new_lines else {}
        if old_lines != new_lines:
            for block in difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False).get_matching_blocks():
                for i in range(block.size):
                    alignment[block.a+i+1] = block.b+i+1
        lookup = collections.defaultdict(list)
        for e in current:
            lookup[(tuple(e['position']), e['label'])].append(e)
        # Generated pretty-printing can reindent unchanged expressions. Align
        # literal-preserving tokens globally, never by an expression name alone.
        token_alignment, token_lookup = {}, collections.defaultdict(list)
        old_tokens, old_span = token_spans(old_lines)
        new_tokens, new_span = token_spans(new_lines)
        if old_lines != new_lines:
            for block in difflib.SequenceMatcher(None, old_tokens, new_tokens, autojunk=False).get_matching_blocks():
                for i in range(block.size):
                    token_alignment[block.a+i] = block.b+i
            for n in current:
                token_lookup[(new_span(n['position']),n['label'])].append(n)
        unique_old, unique_new = collections.Counter(), collections.defaultdict(list)
        def normalized(e, lines):
            return tuple(re.findall(TOKEN, excerpt(lines,e['position']))),e['label']
        if old_lines != new_lines:
            for e in entries:unique_old[normalized(e,old_lines)] += 1
            for n in current:unique_new[normalized(n,new_lines)].append(n)
        mapped = 0
        for e in entries:
            obligation = meta['offset']+e['tick']
            if obligation not in required:
                continue
            first, col, last, end = e['position']
            lines = [alignment.get(n) for n in range(first,last+1)]
            candidates = []
            if all(n is not None for n in lines) and lines == list(range(lines[0],lines[0]+len(lines))):
                pos = (lines[0],col,lines[-1],end)
                candidates = lookup.get((pos,e['label']),[])
                candidates = [n for n in candidates if excerpt(old_lines,e['position']) == excerpt(new_lines,n['position'])]
            method = 'identical source span'
            if not candidates and old_lines != new_lines:
                span = old_span(e['position'])
                if span:
                    first_token,last_token = span
                    mapped_tokens = [token_alignment.get(i) for i in range(first_token,last_token+1)]
                    if all(i is not None for i in mapped_tokens) and mapped_tokens == list(range(mapped_tokens[0],mapped_tokens[0]+len(mapped_tokens))):
                        candidates = token_lookup.get(((mapped_tokens[0],mapped_tokens[-1]),e['label']),[])
                        method = 'identical literal-preserving tokens in monotone source alignment'
            if not candidates and old_lines != new_lines:
                key = normalized(e,old_lines)
                if unique_old[key] == 1 and len(unique_new[key]) == 1:
                    candidates = unique_new[key]
                    method = 'identical literal-preserving expression and label, unique in both module versions'
            if len(candidates) == 1:
                n = candidates[0]
                mappings.append(dict(old_obligation=obligation,module=module,old_tick=e['tick'],new_tick=n['tick'],new_hash=n['hash'],method=method))
                mapped += 1
            else:
                gaps.append(dict(old_obligation=obligation,module=module,old_tick=e['tick'],label=e['label'],position=e['position'],source_excerpt=excerpt(old_lines,e['position']),reason='No unique unchanged expression/span with identical HPC label; semantic review required.'))
        reports.append(dict(module=module,old_source_sha256=sha(old_path),new_source_sha256=sha(new_path) if new_path else None,old_hash=meta['hash'],new_hash=current[0]['hash'] if current else None,mapped_required_counters=mapped))
    result = dict(old_mix_sha256=sha(a.old_mix),new_mix_sha256=sha(a.new_mix),denominator_sha256=sha(a.denominator),modules=reports,mappings=mappings,unmapped_required_counters=gaps,scope='Mappings require identical HPC labels and unchanged source spans, monotone literal-preserving token alignment, or literal-preserving expressions unique in both module versions. This report never silently retires a counter or establishes theorem equivalence.')
    write(a.output,result)
    print(json.dumps(dict(mapped=len(mappings),unmapped=len(gaps))))


if __name__ == '__main__':
    main()
