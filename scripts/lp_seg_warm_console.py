#!/usr/bin/env python3
"""Resume an isolated, already verified LP heap chain; no proof/search shortcuts."""
import argparse
import json
import os
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--environment-pid', type=int, required=True)
p.add_argument('--root', type=Path, required=True)
p.add_argument('--log', type=Path, required=True)
p.add_argument('--leaf', action='append', default=[])
a = p.parse_args()
env = dict(x.split('=', 1) for x in Path(f'/proc/{a.environment_pid}/environ').read_text().split('\0') if '=' in x)
base = a.root / 'user/.isabelle/lp_check/heaps/polyml-5.9.2_x86_64-linux'
parents = 'Pure HOL HOL-Library HOL-Lib HOL-AFP IsaFoR_1 IsaFoR_2 Proof_Checker_Base CSR_Checker_Base CSR_Checker_Core CSR_Checker_Extensions CSR_Muterm_Ext CSR_Muterm_Typed_General_Redpair CSR_Muterm_Typed_Recursive_Redpair CSR_Guarded_List_Measure_Check Proof_Checker'.split()
children = 'mgu-dependencies mgu-verified-v15 mgu-head-verified-v16 answer-split-verified-20261023 answer-executable-v17-20261023 answer-executable-v18-20261023 return-contracts-verified-v21-20261023 seg-connection-verified-v42 seg-region-verified-v43 seg-split-certificate-verified-v44 seg-code-verified-v46 seg-free-certificate-verified-v55'.split()
heaps = [str(base / n) for n in parents] + [str(a.root / (n + '.heap')) for n in children + a.leaf]
assert all(Path(h).is_file() for h in heaps), 'missing verified heap'
fd = os.open(a.log, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
os.dup2(fd, 1)
os.dup2(fd, 2)
print(json.dumps({'pid': os.getpid(), 'heaps': heaps}), flush=True)
poly = str(Path(env['POLYML_HOME']) / 'x86_64-linux/poly')
os.execve(poly, [poly, '-q', '--minheap', '1000', '--gcthreads', '4', '--eval',
                '(PolyML.SaveState.loadHierarchy ' + json.dumps(heaps) + '; PolyML.print_depth 0)', '-i'], env)
