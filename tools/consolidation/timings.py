#!/usr/bin/env python3
"""Extract reported theory timings without confusing CPU totals with wall time."""
import argparse, collections, json, pathlib, re
from replay import sha, write


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--log', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    a = p.parse_args()
    theories = []
    sessions = []
    diagnostics = []
    for line in a.log.read_text(errors='replace').splitlines():
        m = re.fullmatch(r'([^:]+): theory (\S+) 100% \(([0-9.]+)s cumulated time\)', line)
        if m:
            theories.append(dict(session=m[1], theory=m[2], reported_cumulated_seconds=float(m[3])))
        elif line.startswith(('Finished ', 'Timing ', 'Elapsed time:')):
            sessions.append(line)
        elif line.startswith('***'):
            diagnostics.append(line)
    totals = collections.defaultdict(float)
    for t in theories:
        totals[t['session']] += t['reported_cumulated_seconds']
    result = dict(log_sha256=sha(a.log), theory_reports=theories,
                  reported_cumulated_seconds_by_session=dict(totals), session_reports=sessions,
                  diagnostics=diagnostics,
                  interpretation='Isabelle-reported cumulated theory times; sums are not elapsed build wall time. Use the build receipt for wall time and exit status.')
    write(a.output, result)
    print(json.dumps(dict(theories=len(theories), sessions=len(totals), diagnostics=len(diagnostics))))


if __name__ == '__main__':
    main()
