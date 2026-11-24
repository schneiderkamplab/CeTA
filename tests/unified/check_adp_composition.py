"""Exercise closed ADP obligations through the unified certificate-file entry point."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


EMPTY = "<rules/>"
LOOP = "<rules><rule><funapp><name>f</name><var>x</var></funapp><funapp><name>f</name><var>x</var></funapp></rule></rules>"


def subject(strict=EMPTY, weak=EMPTY, strategy=""):
    return f"<trsInput><trs>{strict}</trs>{strategy}<relativeRules>{weak}</relativeRules></trsInput>"


def assumption(inp):
    return f"<trsTerminationProof><terminationAssumption>{inp}</terminationAssumption></trsTerminationProof>"


def discharge(strict=EMPTY, weak=EMPTY):
    return (f"<relativeAdpDischarge><strictRules>{strict}</strictRules>"
            f"<weakRules>{weak}</weakRules><relativeAdpTerminationProof>"
            "<relativeAdpEmpty/></relativeAdpTerminationProof></relativeAdpDischarge>")


def certificate(inp, ordinary, discharges):
    return ("<certificationProblem><cpfVersion>4.0</cpfVersion><lookupTables/>"
            f"<input>{inp}</input><property><termination/></property><answer><yes/></answer>"
            f"<proof><relativeAdpComposition><proof>{ordinary}</proof>"
            f"<discharges>{discharges}</discharges></relativeAdpComposition></proof>"
            "</certificationProblem>")


def cases():
    empty = subject()
    child = assumption(empty)
    split = f"<trsTerminationProof><split><trs>{EMPTY}</trs>{child}{child}</split></trsTerminationProof>"
    yield "split-two-children", certificate(empty, split, discharge()), True
    dp_input = f"<dpInput><trs>{EMPTY}</trs><dps>{EMPTY}</dps><minimal>false</minimal></dpInput>"
    dp = f"<dpProof><switchToTRS>{child}</switchToTRS></dpProof>"
    yield "dp-to-trs-child", certificate(dp_input, dp, discharge()), True
    # Empty uncurrying is useful here because all computed child rules are known
    # independently of Ferrum's serializer; nonempty search fixtures are separate.
    uncurry = ("<trsTerminationProof><uncurry><uncurryInformation><name>app</name>"
               "<uncurriedSymbols/><uncurryRules><rules/></uncurryRules>"
               "<etaRules><rules/></etaRules></uncurryInformation><trs><rules/></trs>"
               f"{child}</uncurry></trsTerminationProof>")
    yield "uncurry-child", certificate(empty, uncurry, discharge()), True
    yield "missing-discharge", certificate(empty, split, ""), False
    yield "wrong-strict-subject", certificate(subject(LOOP), child, discharge()), False
    yield "wrong-weak-subject", certificate(subject(weak=LOOP), assumption(subject(weak=LOOP)), discharge()), False
    yield "false-adp-proof", certificate(subject(LOOP), assumption(subject(LOOP)), discharge(LOOP)), False
    innermost = subject(strategy="<strategy><innermost><nfs>true</nfs></innermost></strategy>")
    yield "incompatible-strategy", certificate(empty, assumption(innermost), discharge()), False
    yield "unchecked-extra-discharge", certificate(empty, child, discharge() + discharge(LOOP)), False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checker = args.checker.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    records = []
    for name, xml, expected in cases():
        path = output / (name + ".xml")
        path.write_text(xml + "\n")
        started = time.monotonic()
        try:
            result = subprocess.run([str(checker), str(path)], capture_output=True, text=True, timeout=120)
            accepted = result.returncode == 0 and result.stdout.strip() == "CERTIFIED"
            # Crashes and unsupported formats do not count as semantic rejection.
            passed = accepted if expected else result.returncode == 1 and result.stdout.strip() == "REJECTED"
            record = dict(returncode=result.returncode, stdout=result.stdout, stderr=result.stderr,
                          accepted=accepted, passed=passed)
        except subprocess.TimeoutExpired:
            record = dict(passed=False, timeout=True)
        records.append(dict(name=name, expected_acceptance=expected, seconds=time.monotonic()-started,
                            certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(), **record))
        print(name, record, flush=True)
        (output / "validation.json").write_text(json.dumps(dict(
            checker=str(checker), checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),
            checks=records, passed=all(r["passed"] for r in records)), indent=2) + "\n")
    return 0 if all(r["passed"] for r in records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
