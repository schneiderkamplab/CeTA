#!/usr/bin/env python3
"""Check the published finite-LP artifact through the single unified executable."""
import argparse
import json
import subprocess
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('binary', type=Path)
args = parser.parse_args()
binary = str(args.binary.resolve())
fixture = Path(__file__).with_name('lp-finite.xml')
results = []

def check(path, expected):
    result = subprocess.run([binary, '--category', 'lp', str(path)],
                            capture_output=True, text=True, timeout=30)
    accepted = result.returncode == 0 and result.stdout.startswith('CERTIFIED ')
    assert accepted == expected, (path, result.stdout, result.stderr)
    results.append(dict(artifact=path.name, expected=expected, accepted=accepted,
                        returncode=result.returncode, stdout=result.stdout))

for _ in range(2):
    check(fixture, True)
with tempfile.TemporaryDirectory() as directory:
    directory = Path(directory)
    root = ET.parse(fixture).getroot()
    program = root.find('program')
    # Replace the source with a direct self-loop, retaining its old termination proof.
    head = ET.tostring(program.find('clause/head'), encoding='unicode')
    program.clear()
    clause = ET.SubElement(program, 'clause')
    clause.append(ET.fromstring(head))
    body = ET.SubElement(clause, 'body')
    body.append(ET.fromstring(head)[0])
    mutation = directory / 'source-loop.xml'
    ET.ElementTree(root).write(mutation, encoding='unicode')
    check(mutation, False)
    root = ET.parse(fixture).getroot()
    root.remove(root.find('trsTerminationProof'))
    mutation = directory / 'missing-child-proof.xml'
    ET.ElementTree(root).write(mutation, encoding='unicode')
    check(mutation, False)
print(json.dumps(results, indent=2))
