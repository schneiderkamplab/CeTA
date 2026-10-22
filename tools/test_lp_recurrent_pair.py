#!/usr/bin/env python3
"""Exercise the exported recurrent-pair parser/checker, never synthesize proofs."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import xml.etree.ElementTree as ET


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ceta", type=Path, required=True)
    args = parser.parse_args()
    checker = args.ceta.resolve()
    fixture = Path(__file__).parent / "fixtures/lp-recurrent-pair.xml"
    original = ET.parse(fixture).getroot()
    cases = [("positive-first", copy.deepcopy(original), True),
             ("positive-second", copy.deepcopy(original), True)]
    for name, path, value in [
        ("wrong-query", "query/name", "other"),
        ("wrong-arity", "query/arity", "3"),
        ("invalid-mode-position", "query/ground/index", "2"),
        ("aliased-holes", "secondHole/var", "X"),
        ("extra-context-variable", "termContext/funapp/var", "Z"),
        ("phase-bound", "pumpBase", "1"),
        ("wrong-stride", "stride", "2"),
        ("wrong-growth", "pumpGrowth", "2"),
        ("wrong-reset", "resetOffset", "0"),
        ("wrong-keep", "keepFirst", "true"),
        ("wrong-clause", "steps/step/clauseIndex", "99"),
    ]:
        tree = copy.deepcopy(original)
        tree.find(path).text = value
        cases.append((name, tree, False))
    tree = copy.deepcopy(original)
    tree.find("steps").clear()
    cases.append(("empty-phase", tree, False))
    tree = copy.deepcopy(original)
    seed = tree.find("seed")
    seed.clear()
    ET.SubElement(seed, "var").text = "Z"
    cases.append(("nonground-seed", tree, False))
    tree = copy.deepcopy(original)
    body = tree.find("program/clause/body")
    guard = ET.Element("funapp")
    ET.SubElement(guard, "name").text = "unproved_guard"
    body.insert(0, guard)
    cases.append(("cannot-skip-prefix", tree, False))
    results = []
    with tempfile.TemporaryDirectory(prefix="lp-recurrent-check-") as directory:
        for name, tree, accepted in cases:
            path = Path(directory) / (name + ".xml")
            ET.ElementTree(tree).write(path, encoding="unicode")
            run = subprocess.run([str(checker), str(path)], text=True,
                                 capture_output=True, timeout=30)
            actual = run.returncode == 0 and "CERTIFIED TOCL09 LP NO" in run.stdout
            if actual != accepted or (not accepted and "REJECTED" not in run.stdout):
                raise RuntimeError(f"{name}: {run.returncode}: {run.stdout} {run.stderr}")
            results.append({"case": name, "accepted": actual})
    print(json.dumps({"checker": str(checker),
                      "sha256": hashlib.sha256(checker.read_bytes()).hexdigest(),
                      "fixture_sha256": hashlib.sha256(fixture.read_bytes()).hexdigest(),
                      "results": results}, indent=2))


if __name__ == "__main__":
    main()
