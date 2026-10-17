#!/usr/bin/env python3
"""Link changed checker declarations to HPC functions, retaining every gap."""
import argparse, ast, collections, gzip, json, pathlib, re, subprocess
from replay import ROOT, sha, write


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--stage', type=pathlib.Path, required=True)
    p.add_argument('--mix', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    a = p.parse_args()
    metadata = json.loads((a.stage / 'metadata.json').read_text())
    revision = metadata['hpc_source_revision']
    inventory = json.loads((ROOT / 'docs/consolidation/source-inventory.json').read_text())
    variants = []
    for v in inventory['variants']:
        r = subprocess.run(['git', 'rev-parse', revision + ':' + v['path']], cwd=ROOT, text=True, capture_output=True)
        if r.returncode == 0 and r.stdout.strip() == v['blob']:
            variants.append(v)
    modules = collections.defaultdict(list)
    hashes = {}
    for line in a.mix.read_text().splitlines():
        module, digest, tick, source, position, label = line.split('\t')
        hashes[module] = digest
        modules[module].append(dict(tick=int(tick), position=ast.literal_eval(position), label=label))
    observed = collections.defaultdict(set)
    roots_by_function = collections.defaultdict(set)
    functions = {}
    module_functions = collections.defaultdict(list)
    for module, entries in modules.items():
        for e in entries:
            m = re.fullmatch(r'TopLevelBox \["([^"\]]+)"\]', e['label'])
            if m:
                functions[(module, m[1])] = e
                module_functions[module].append((m[1], e))
    records = [json.loads(s) for s in (a.stage / 'results.jsonl').read_text().splitlines()]
    eligible = [r for r in records if r['eligible']]
    for r in eligible:
        with gzip.open(a.stage / r['id'] / 'coverage.tsv.gz', 'rt') as f:
            for line in f:
                module, digest, count, ticks = line.rstrip('\n').split('\t')
                # ExportMix emits one row per counter; a module with zero
                # counters has no source positions and cannot contribute ticks.
                if int(count)==0 and not ticks and module not in modules:
                    continue
                if hashes.get(module) != digest or len(modules[module]) != int(count):
                    raise ValueError('Mix/Tix identity mismatch for ' + module)
                hit = {int(i) for i in ticks.split(',') if i}
                observed[module].update(hit)
                for name, e in module_functions[module]:
                    if e['tick'] in hit:
                        roots_by_function[(module, name)].add(r['root'])
    mappings = []
    for v in variants:
        module = pathlib.Path(v['generated_module']).stem
        for checker in v['checker_candidates']:
            name = checker['name']
            entry = functions.get((module, name))
            soundness = [d for d in v['soundness_candidates'] if d['name'].startswith(name)]
            row = dict(theory=v['path'], source_blob=v['blob'], declaration=checker, generated_module=module,
                       soundness_candidates=soundness, supporting_roots=sorted(roots_by_function[(module, name)]),
                       theorem_mapping='Declaration-name candidates only; assumptions and criterion call chain require semantic review.')
            if entry is None:
                row['gap'] = 'No matching instrumented top-level function; may be absent from this export or renamed.'
            else:
                pos = entry['position']
                contained = [e for e in modules[module]
                             if (pos[0], pos[1]) <= (e['position'][0], e['position'][1])
                             and (e['position'][2], e['position'][3]) <= (pos[2], pos[3])]
                row['hpc'] = dict(module_hash=hashes[module], top_level_tick=entry['tick'], position=pos,
                                 ticks=len(contained), observed_ticks=sum(e['tick'] in observed[module] for e in contained),
                                 boolean_branches=[e | dict(observed=e['tick'] in observed[module])
                                                   for e in contained if e['label'].startswith('BinBox')])
                row['gap'] = 'Exact criterion/context/negative mapping pending.' if row['supporting_roots'] else 'No eligible positive reaches this function.'
            mappings.append(row)
    summary_path=a.stage/'summary.json'
    complete=summary_path.exists() and not json.loads(summary_path.read_text())['losses'] and len(eligible)==len(metadata['roots'])
    report = dict(source_revision=revision, hpc_sha256=metadata['hpc_sha256'], mix_sha256=sha(a.mix),
                  scope='Completed eligible roots only; executable coverage does not execute Isabelle proofs.',
                  eligible_roots=len(eligible), expected_roots=len(metadata['roots']), complete=complete,
                  changed_declarations=len(mappings), observed_functions=sum(bool(r['supporting_roots']) for r in mappings),
                  mappings=mappings)
    write(a.output, report)
    print(json.dumps({k: v for k, v in report.items() if k != 'mappings'}))


if __name__ == '__main__':
    main()
