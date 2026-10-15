#!/usr/bin/env python3
"""Build, audit proof dependencies, run the checker, and test the audit itself."""

from __future__ import annotations

import argparse
import re
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(*command: str) -> str:
    print("\n$ " + " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    print(result.stdout, end="", flush=True)
    print(result.stderr, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def test_audit_rejects_invalid_proofs() -> None:
    audit = (ROOT / "Audit.lean").read_text()
    marker = "open Lean Elab Command in"
    imports, body = audit.split(marker, 1)
    probes = [
        ("unfinished proof", "theorem Descent.auditProbe : False := by sorry\n",
         "Unexpected proof dependency"),
        ("unfinished proof in definition", "def Descent.auditProbe : False := by sorry\n",
         "Unexpected proof dependency"),
        ("extra axiom", "axiom Descent.auditProbe : False\n",
         "Project-defined axiom rejected"),
    ]
    with tempfile.TemporaryDirectory(prefix="multiset-descent-audit-") as scratch:
        for label, declaration, expected_error in probes:
            path = Path(scratch) / "NegativeAudit.lean"
            path.write_text(imports + declaration + marker + body)
            result = subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=ROOT,
                text=True, capture_output=True,
            )
            output = result.stdout + result.stderr
            if result.returncode == 0 or expected_error not in output:
                print(output)
                raise SystemExit(f"Audit regression: did not reject {label} correctly")
            print(f"PASS: audit rejected {label}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true", help="For CI after lean-action")
    args = parser.parse_args()
    if not args.skip_build:
        run("lake", "build")
    output = run("lake", "env", "lean", "Audit.lean")
    if "AUDIT PASS:" not in output:
        raise SystemExit("Audit did not report success")
    source_theorems = []
    for path in sorted((ROOT / "Descent").glob("*.lean")):
        source = path.read_text()
        namespace = re.search(r"^namespace ([\w.]+)$", source, re.M).group(1)
        names = re.findall(r"^(?:@\[[^\n]+\] )?theorem ([\w.]+)", source, re.M)
        source_theorems.extend(namespace + "." + name for name in names)
    for name in source_theorems:
        if "THEOREM " + name + "\n" not in output:
            raise SystemExit(f"Source theorem missing from imported audit: {name}")
    index = (ROOT / "docs" / "THEOREMS.md").read_text()
    if any("`" + name + "`" not in index for name in source_theorems):
        raise SystemExit("Theorem index does not cover all source theorems")
    print(f"PASS: {len(source_theorems)} explicit source theorems audited and indexed")
    demo = run("lake", "exe", "descent-demo")
    if "PASS: 340 configurations" not in demo:
        raise SystemExit("Exhaustive regression sweep did not complete")
    test_audit_rejects_invalid_proofs()
    print("\nAll verification stages passed.", flush=True)


if __name__ == "__main__":
    main()
