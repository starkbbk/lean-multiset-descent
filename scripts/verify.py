#!/usr/bin/env python3
"""Build, audit proof dependencies, run the checker, and test the audit itself."""

from __future__ import annotations

import argparse
import re
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "docs" / "THEOREMS.md"
THEOREM = re.compile(r"^(?:@\[[^\]]*\]\s+)?(?:protected\s+)?theorem\s+([\w.']+)")
BATTLE = re.compile(r"^KP hydra=(\S+) moves=(\d+)$", re.M)
MIN_BATTLES = 10


def run(*command: str) -> str:
    print("\n$ " + " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    print(result.stdout, end="", flush=True)
    print(result.stderr, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def source_theorems() -> dict[str, list[str]]:
    """Explicit theorem names per module, with nested namespaces resolved."""
    modules: dict[str, list[str]] = {}
    for path in sorted((ROOT / "Descent").glob("*.lean")):
        namespaces: list[str] = []
        names: list[str] = []
        for line in path.read_text().splitlines():
            if match := re.match(r"^namespace ([\w.]+)$", line):
                namespaces.append(match.group(1))
            elif re.match(r"^end [\w.]+$", line):
                namespaces.pop()
            elif match := THEOREM.match(line):
                names.append(".".join(namespaces + [match.group(1)]))
        modules[path.relative_to(ROOT).as_posix()] = names
    return modules


def render_index(modules: dict[str, list[str]]) -> str:
    total = sum(len(names) for names in modules.values())
    lines = [
        "# Theorem index",
        "",
        f"**{total} explicit theorems across {len(modules)} modules.** Every explicit project "
        "theorem is listed below. Compiler-generated recursion and induction helpers are "
        "excluded from this inventory. `scripts/verify.py` checks that each entry is present in "
        "the proof audit; `python3 scripts/verify.py --write-index` regenerates this file.",
        "",
    ]
    for module, names in modules.items():
        lines += [f"## {module}", ""] + [f"- `{name}`" for name in names] + [""]
    return "\n".join(lines)


# An independent Python model of Hercules' strategy in Descent/Battle.lean. A hydra is the
# tuple of its children, so a head is the empty tuple.

def parse_hydra(text: str) -> tuple:
    stack: list[list[tuple]] = [[]]
    for symbol in text:
        if symbol == "(":
            stack.append([])
        elif symbol == ")" and len(stack) > 1:
            node = tuple(stack.pop())
            stack[-1].append(node)
        else:
            raise SystemExit(f"Malformed hydra notation: {text}")
    if len(stack) != 1 or len(stack[0]) != 1:
        raise SystemExit(f"Malformed hydra notation: {text}")
    return stack[0][0]


def chop_first(children: tuple) -> tuple | None:
    for index, child in enumerate(children):
        if child == ():
            return children[:index] + children[index + 1:]
    return None


def regrow_first(copies: int, children: tuple) -> tuple | None:
    for index, child in enumerate(children):
        damaged = chop_first(child)
        if damaged is not None:
            return children[:index] + (damaged,) * (copies + 1) + children[index + 1:]
        inner = regrow_first(copies, child)
        if inner is not None:
            return children[:index] + (inner,) + children[index + 1:]
    return None


def kirby_paris_length(hydra: tuple, limit: int = 1_000_000) -> int:
    stage, moves = 1, 0
    while True:
        after = chop_first(hydra)
        if after is None:
            after = regrow_first(stage, hydra)
        if after is None:
            return moves
        hydra, stage, moves = after, stage + 1, moves + 1
        if moves > limit:
            raise SystemExit("Python battle oracle exceeded its step limit")


def check_battles(demo: str) -> None:
    battles = BATTLE.findall(demo)
    if len(battles) < MIN_BATTLES or f"PASS: {len(battles)} battles" not in demo:
        raise SystemExit("Hydra battle demonstration did not complete")
    for notation, moves in battles:
        expected = kirby_paris_length(parse_hydra(notation))
        if int(moves) != expected:
            raise SystemExit(f"Battle mismatch for {notation}: Lean {moves}, Python {expected}")
    print(f"PASS: {len(battles)} Kirby–Paris battles match an independent Python simulation",
          flush=True)


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
    parser.add_argument("--write-index", action="store_true",
                        help="Regenerate docs/THEOREMS.md from the sources and exit")
    args = parser.parse_args()
    modules = source_theorems()
    if args.write_index:
        INDEX.write_text(render_index(modules))
        print(f"Wrote {INDEX.relative_to(ROOT)}")
        return
    if not args.skip_build:
        run("lake", "build")
    output = run("lake", "env", "lean", "Audit.lean")
    if "AUDIT PASS:" not in output:
        raise SystemExit("Audit did not report success")
    theorems = [name for names in modules.values() for name in names]
    for name in theorems:
        if "THEOREM " + name + "\n" not in output:
            raise SystemExit(f"Source theorem missing from imported audit: {name}")
    if INDEX.read_text() != render_index(modules):
        raise SystemExit("docs/THEOREMS.md is stale; run scripts/verify.py --write-index")
    print(f"PASS: {len(theorems)} explicit source theorems in {len(modules)} modules "
          "audited and indexed")
    demo = run("lake", "exe", "descent-demo")
    if "PASS: 340 configurations" not in demo:
        raise SystemExit("Exhaustive regression sweep did not complete")
    check_battles(demo)
    if run("lake", "exe", "descent-demo") != demo:
        raise SystemExit("Demonstration output differs between runs")
    print("PASS: demonstration output is identical across two runs", flush=True)
    test_audit_rejects_invalid_proofs()
    print("\nAll verification stages passed.", flush=True)


if __name__ == "__main__":
    main()
