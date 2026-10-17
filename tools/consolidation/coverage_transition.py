"""Validate and apply an explicitly reviewed executable coverage transition.

Retired counters remain reported separately; they never count as executed.
"""
import gzip,json
from replay import sha

class Transition:
    def __init__(self,path,denpath,checker,hpc):
        opener=gzip.open if path.suffix=='.gz' else open
        with opener(path,'rt') as f:self.data=json.load(f)
        d=self.data
        if d['denominator_sha256']!=sha(denpath) or d['checker_sha256']!=sha(checker) or d['hpc_checker_sha256']!=sha(hpc):
            raise ValueError('Coverage transition identities differ from this run')
        denominator=json.loads(denpath.read_text())
        required=set(denominator['required_obligations'])-set(denominator['structural_features'].values())
        mapped=[r['old_obligation'] for r in d['mappings']]
        retired=[r['old_obligation'] for r in d['retired']]
        if len(set(mapped+retired))!=len(mapped+retired) or set(mapped+retired)!=required:
            raise ValueError('Transition must account for each frozen executable obligation exactly once')
        if not all(r.get('reason') for r in d['retired']):raise ValueError('Unexplained retirement')
        self.retired=set(retired);self.lookup={}
        for r in d['mappings']:
            m=d['new_modules'][r['module']]
            if r['new_hash']!=m['hash'] or not 0<=r['new_tick']<m['count']:raise ValueError('Invalid mapped counter')
            self.lookup.setdefault((r['module'],r['new_tick']),set()).add(r['old_obligation'])
    def observe(self,name,digest,count,ticks):
        m=self.data['new_modules'].get(name)
        if m is None or m['hash']!=digest or m['count']!=count:
            raise ValueError('Unreviewed instrumentation: '+name)
        observed=set()
        for tick in ticks:
            if not 0<=tick<count:raise ValueError('Counter outside module')
            observed.update(self.lookup.get((name,tick),set()))
        return observed
