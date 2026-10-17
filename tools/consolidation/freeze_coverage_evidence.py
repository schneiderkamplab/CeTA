#!/usr/bin/env python3
"""Freeze a grouped coverage matrix and independently recheck its cardinality bound."""
import argparse, collections, gzip, hashlib, json, pathlib, shutil, subprocess, time
from replay import sha, write
from run_logged import memory_used


def compressed(path, value):
    path.write_bytes(gzip.compress(json.dumps(value,sort_keys=True).encode(),mtime=0))


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--stage',type=pathlib.Path,required=True)
    p.add_argument('--output',type=pathlib.Path,required=True)
    a=p.parse_args()
    if memory_used()>2*1024**4:raise SystemExit('Memory launch ceiling exceeded')
    stage=a.stage.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    denominator=json.loads((stage/'coverage-denominator.json').read_text())
    selection=json.loads((stage/'selection.json').read_text())
    records=sorted(map(json.loads,(stage/'results.jsonl').read_text().splitlines()),key=lambda r:r['root'])
    metadata=json.loads((stage/'metadata.json').read_text())
    expected={(r['root'],r['answer'],r['input_sha256']) for r in metadata['roots']}
    actual={(r['root'],r['expected_answer'],r['input_sha256']) for r in records}
    if actual!=expected or len(records)!=len(expected) or json.loads((stage/'summary.json').read_text())['losses'] or not all(r['eligible'] for r in records):raise ValueError('Incomplete eligible baseline')
    analyses={r['id']:r for r in json.loads((stage/'candidate-costs.json').read_text())}
    owners={};rows=[]
    for i,r in enumerate(records):
        coverage=stage/r['id']/'coverage.tsv.gz'
        if sha(coverage)!=r['coverage_sha256']:raise ValueError('Frozen coverage changed')
        features={denominator['structural_features'][f] for f in analyses[r['id']]['structural_features']}
        features.add(denominator['structural_features']['root-kind|'+r['category']+'|'+r['expected_answer']])
        with gzip.open(coverage,'rt') as f:
            for line in f:
                name,digest,count,ticks=line.rstrip('\n').split('\t');m=denominator['modules'][name]
                if digest!=m['hash'] or int(count)!=m['count']:raise ValueError('Mixed instrumentation')
                features.update(m['offset']+int(t) for t in ticks.split(',') if t)
        for feature in features:owners[feature]=owners.get(feature,0)|(1<<i)
        rows.append(dict(id=r['id'],root=r['root'],cpf_sha256=r['cpf_sha256'],coverage_sha256=r['coverage_sha256'],time_us=round(sum(c['elapsed_seconds'] for c in r['checks'])*1e6),compressed_bytes=analyses[r['id']]['compressed_bytes']))
    if set(owners)!=set(denominator['required_obligations']):raise ValueError('Coverage denominator changed')
    groups=collections.defaultdict(list)
    for feature,mask in sorted(owners.items()):groups[mask].append(feature)
    patterns=sorted(groups,key=lambda m:(m.bit_count(),m))
    selected=set(selection['selected_ids']);mask=sum(1<<i for i,r in enumerate(rows) if r['id'] in selected)
    assert len(selected)==mask.bit_count() and all(mask&m for m in patterns)
    matrix=dict(candidates=rows,patterns=[dict(candidate_bits_hex=hex(m),obligations=groups[m]) for m in patterns],selected_ids=sorted(selected),denominator_sha256=sha(stage/'coverage-denominator.json'),candidate_results_sha256=sha(stage/'results.jsonl'),interpretation='Bit i denotes candidates[i]. Every original obligation remains in exactly one grouped constraint.')
    compressed(out/'matrix.json.gz',matrix)
    def indices(m):
        while m:
            bit=m&-m;yield bit.bit_length()-1;m-=bit
    base='\n'.join(f'(declare-const x{i} Bool)' for i in range(len(rows)))+'\n'
    base+='\n'.join('(assert (or '+' '.join(f'x{i}' for i in indices(m))+'))' for m in patterns)+'\n'
    count='(+ '+' '.join(f'(ite x{i} 1 0)' for i in range(len(rows)))+')'
    script='(set-option :timeout 60000)\n'+base+f'(assert (<= {count} {len(selected)-1}))\n(check-sat)\n'
    (out/'minimum-bound.smt2.gz').write_bytes(gzip.compress(script.encode(),mtime=0))
    if memory_used()>2*1024**4:raise SystemExit('Memory launch ceiling exceeded')
    solver=shutil.which('z3');start=time.monotonic()
    r=subprocess.run([solver,'-in','-smt2'],input=script,text=True,capture_output=True,timeout=65)
    verified=r.returncode==0 and r.stdout.strip()=='unsat'
    result=dict(candidates=len(rows),observed_obligations=len(owners),distinct_constraints=len(patterns),selected_roots=len(selected),selected_covers_every_obligation=True,excluded_bound=len(selected)-1,solver_sha256=sha(pathlib.Path(solver)),solver_version=subprocess.check_output([solver,'--version'],text=True).strip(),solver_status=r.stdout.strip(),solver_stderr=r.stderr,elapsed_seconds=time.monotonic()-start,minimum_cardinality_reverified=verified,secondary_cost_optimality='Not claimed',matrix_sha256=sha(out/'matrix.json.gz'),smt2_sha256=sha(out/'minimum-bound.smt2.gz'))
    write(out/'verification.json',result);print(json.dumps(result));raise SystemExit(not verified)


if __name__=='__main__':main()
