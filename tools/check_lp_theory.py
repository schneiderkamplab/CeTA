#!/usr/bin/env python3
"""Check LP theories against a cloned warm heap, without rebuilding parents."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time


def process_tree(pid):
    """Snapshot owned descendants, including Isabelle's separate ML session."""
    result = []
    try:
        for child in (Path('/proc')/str(pid)/'task'/str(pid)/'children').read_text().split():
            result.extend(process_tree(int(child)))
        stat = (Path('/proc')/str(pid)/'stat').read_text().rsplit(')', 1)[1].split()
        result.append((pid, stat[19]))  # Linux process start time, not PID alone.
    except (FileNotFoundError, ProcessLookupError):
        pass
    return result


def signal_owned(processes, sig):
    for pid, started in processes:
        try:
            stat = (Path('/proc')/str(pid)/'stat').read_text().rsplit(')', 1)[1].split()
            if stat[19] == started:
                os.kill(pid, sig)
        except (FileNotFoundError, ProcessLookupError):
            pass


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for key in ('isabelle', 'warm-home', 'base-sessions', 'afp', 'out'):
        p.add_argument('--'+key, type=Path, required=True)
    p.add_argument('--theory', nargs='+', required=True)
    p.add_argument('--timeout', type=int, default=300)
    a = p.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    private = out/'user/.isabelle/lp_check'
    private.parent.mkdir(parents=True)
    subprocess.run(['cp', '-a', '--reflink=auto', str(a.warm_home.resolve()), str(private)], check=True)
    source = out/'source'
    source.mkdir()
    for f in (root/'thys/Logic_Programming').glob('*.thy'):
        shutil.copyfile(f, source/f.name)
    for name in a.theory:
        if Path(name).name != name or not (source/(name+'.thy')).is_file():
            raise ValueError('invalid theory name: '+name)
    code = '; '.join('Thy_Info.use_thy_legacy '+json.dumps(str(source/name)) for name in a.theory)
    code = '(('+code+'; writeln "LP_THEORIES_VERIFIED"; OS.Process.exit OS.Process.success) handle exn => '
    code += '(Runtime.exn_message exn |> writeln; OS.Process.exit OS.Process.failure));\n'
    env = dict(os.environ, USER_HOME=str(out/'user'), ISABELLE_IDENTIFIER='lp_check', AFP=str(a.afp.resolve()))
    started = time.monotonic()
    timed_out = False
    with (out/'check.log').open('w') as log:
        proc = subprocess.Popen([str(a.isabelle), 'console', '-n', '-l', 'Proof_Checker',
            '-d', str(a.base_sessions.resolve()), '-o', 'threads=4', '-o', 'parallel_proofs=0',
            '-o', 'quick_and_dirty=false'], stdin=subprocess.PIPE,
            text=True, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            proc.communicate(input=code, timeout=a.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            owned = process_tree(proc.pid)
            signal_owned(owned, signal.SIGTERM)
            try:
                proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            # ML starts a separate process group; killing Java's group alone
            # can leave it running. Never touch another check or a reused PID.
            signal_owned(owned, signal.SIGKILL)
            proc.communicate()
    verified = not timed_out and proc.returncode == 0 and 'LP_THEORIES_VERIFIED' in (out/'check.log').read_text()
    identity = dict(verified=verified, seconds=time.monotonic()-started, theories=a.theory,
        timed_out=timed_out, returncode=proc.returncode,
        parent=str(a.warm_home.resolve()),
        source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
        hashes={f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(source.glob('*.thy'))})
    (out/'identity.json').write_text(json.dumps(identity, indent=2)+'\n')
    print(json.dumps({k:v for k,v in identity.items() if k!='hashes'}))
    if not verified:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
