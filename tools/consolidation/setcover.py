#!/usr/bin/env python3
"""Deterministic greedy bound plus bounded exact cardinality search using Z3.
Costs are lexicographic: roots, measured microseconds, compressed bytes.
Only an UNSAT cardinality bound (or matching proved lower bound) proves minimum.
"""
import re,shutil,subprocess,time

def covers(rows,chosen,universe):return set().union(*(rows[i]['features'] for i in chosen))>=universe if chosen else not universe

def greedy(rows):
    universe=set().union(*(r['features'] for r in rows));remaining=set(universe);chosen=[]
    while remaining:
        i=min(range(len(rows)),key=lambda j:(-len(rows[j]['features']&remaining),rows[j]['time_us'],rows[j]['bytes'],rows[j]['id']))
        if not rows[i]['features']&remaining:raise ValueError('Uncoverable denominator')
        chosen.append(i);remaining-=rows[i]['features']
    for i in sorted(chosen,key=lambda j:(rows[j]['time_us'],rows[j]['bytes'],rows[j]['id']),reverse=True):
        rest=[j for j in chosen if j!=i]
        if covers(rows,rest,universe):chosen=rest
    return sorted(chosen),universe

def select(rows,seconds=300):
    if not rows:return dict(selected=[],minimum_cardinality_proved=True,lower_bound=0,upper_bound=0,solver_trials=[])
    best,universe=greedy(rows);start=time.monotonic();owners={}
    for i,row in enumerate(rows):
        bit=1<<i
        for f in row['features']:owners[f]=owners.get(f,0)|bit
    patterns=sorted(set(owners.values()),key=lambda m:(m.bit_count(),m));used=0;lower=0
    for m in patterns:
        if not m&used:lower+=1;used|=m
    def indices(m):
        while m:
            bit=m&-m;yield bit.bit_length()-1;m-=bit
    declarations='\n'.join(f'(declare-const x{i} Bool)' for i in range(len(rows)))
    constraints='\n'.join('(assert (or '+' '.join(f'x{i}' for i in indices(m))+'))' for m in patterns)
    count='(+ '+' '.join(f'(ite x{i} 1 0)' for i in range(len(rows)))+')'
    base=declarations+'\n'+constraints+'\n';trials=[];solver=shutil.which('z3')
    def solve(bound,optimize=False):
        remaining=seconds-(time.monotonic()-start)
        if remaining<0.05 or solver is None:return 'unknown',None
        limit=min(60,remaining);script=f'(set-option :timeout {int(limit*1000)})\n'+base+f'(assert (<= {count} {bound}))\n'
        if optimize:
            script+='(minimize (+ '+' '.join(f'(ite x{i} {r["time_us"]} 0)' for i,r in enumerate(rows))+'))\n'
            script+='(minimize (+ '+' '.join(f'(ite x{i} {r["bytes"]} 0)' for i,r in enumerate(rows))+'))\n'
        script+='(check-sat)\n(get-value ('+' '.join(f'x{i}' for i in range(len(rows)))+'))\n'
        began=time.monotonic()
        try:
            r=subprocess.run([solver,'-in','-smt2'],input=script,text=True,capture_output=True,timeout=limit+3)
            status=next((line for line in r.stdout.splitlines() if line in ('sat','unsat','unknown')),'unknown')
            chosen=sorted(int(i) for i,v in re.findall(r'\(x(\d+)\s+(true|false)\)',r.stdout) if v=='true')
            if status=='sat' and (len(chosen)>bound or not covers(rows,chosen,universe)):raise ValueError('Solver returned invalid cover')
            trials.append(dict(bound=bound,status=status,optimize_cost=optimize,seconds=time.monotonic()-began))
            return status,chosen if status=='sat' else None
        except subprocess.TimeoutExpired:
            trials.append(dict(bound=bound,status='timeout',optimize_cost=optimize,seconds=time.monotonic()-began));return 'unknown',None
    while lower<len(best) and time.monotonic()-start<seconds:
        bound=(lower+len(best)-1)//2;status,chosen=solve(bound)
        if status=='sat':best=chosen
        elif status=='unsat':lower=bound+1
        else:break
    cardinality_proved=lower==len(best)
    status,cost_choice=solve(len(best),True)
    if status=='sat':
        cost=lambda choice:(len(choice),sum(rows[i]['time_us'] for i in choice),sum(rows[i]['bytes'] for i in choice))
        if cost(cost_choice)<cost(best):best=cost_choice
    assert covers(rows,best,universe)
    return dict(selected=best,minimum_cardinality_proved=cardinality_proved and lower==len(best),lower_bound=lower,upper_bound=len(best),observed_obligations=len(universe),distinct_cover_constraints=len(patterns),solver_trials=trials,secondary_cost_optimality='best validated candidate; no separate secondary optimality certificate',elapsed_seconds=time.monotonic()-start)
