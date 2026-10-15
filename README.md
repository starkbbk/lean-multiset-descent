# Multiset Descent

[![Lean verification](https://github.com/starkbbk/lean-multiset-descent/actions/workflows/ci.yml/badge.svg)](https://github.com/starkbbk/lean-multiset-descent/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.33.0--rc1-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-pinned-purple)

**A Lean 4 / Mathlib development connecting multiset termination to total executable normalization and sharp complexity certificates.**

A work item of rank `n + 1` can spawn any finite number of rank-`n` children. An unordered scheduler can pick any item. The worklist can grow, its rank sum can increase, and its maximum rank can stay unchanged. Nevertheless, every schedule terminates by Dershowitz–Manna multiset descent.

The quantitative part distinguishes three different claims:

| Branching model | What is proved |
| --- | --- |
| Arbitrary finite offspring at each step | No infinite schedule; complete runs from the fixed state `{1}` can still be arbitrarily long |
| A fixed rank-dependent offspring policy | Every complete schedule has exactly the same number of transitions |
| An adversary choosing up to a rank-dependent cap | A universal worst-case upper bound, together with a complete run attaining it exactly |

**60 explicit theorems · 8 proof modules · total native executor · 340 regression configurations · dependency audit with negative controls.**

## The main result

For a cap `b : ℕ → ℕ`, define a task budget and multiset potential:

```text
C(0)     = 1
C(n + 1) = 1 + b(n) · C(n)
P(M)     = sum of C(rank) over every occurrence in M
```

The theorem [`sharp_worst_case`](Descent/Bounded.lean) proves both:

1. Every legal bounded-branching execution from `M`, including an incomplete prefix, has length at most `P(M)`.
2. There exists a legal complete execution from `M` to the empty worklist with length exactly `P(M)`.

For fixed branching, [`run_exact_cost`](Descent/Potential.lean) establishes the stronger identity `P(source) = length + P(target)`. The binary policy gives `C(n) + 1 = 2^(n+1)`, proved for all natural ranks.

## Why a multiset proof is needed

```text
{2}      → {1, 1, 1}    size: 1 → 3; rank sum: 2 → 3
{2, 2}   → {2, 1, 1}    maximum rank: 2 → 2
{1}      → k copies of 0 → ... → {}    exactly k + 1 steps
```

The last family has no uniform finite bound when `k` is unrestricted, despite termination of every individual schedule. These examples and the unbounded-length claim are proved in Lean. Additional countermodels show why strict child ranks and a well-founded base order are essential.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/starkbbk/lean-multiset-descent.git
cd lean-multiset-descent
lake exe cache get
python3 scripts/verify.py
```

The committed `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin Lean and all dependencies. A first build needs network access and disk space for Mathlib.

Useful individual commands:

```sh
lake build
lake exe descent-demo
lake env lean Audit.lean
```

The demo runs the verified depth-first executor against an independent fuel-bounded FIFO simulator, reversed task order, the potential formula, and the final normal form on all 340 configurations (offspring 0–3; list length 0–3; ranks 0–3). Fuel exists only in the regression oracle. The verified normalizer and counter use checked well-founded recursion with no fuel parameter or partial function.

## Review the proofs

| Module | Role |
| --- | --- |
| [Replacement](Descent/Replacement.lean) | Generic contextual replacement, Mathlib bridge, well-foundedness and absence of cycles |
| [Normalization](Descent/Normalization.lean) | Strategy-parametric total normalizer, terminality, actual strategy reachability, idempotence, invariant preservation |
| [Runs](Descent/Runs.lean) | Length-indexed executions, composition, relation inclusion |
| [Branching](Descent/Branching.lean) | Unbounded nondeterministic rewriting, no infinite schedules, arbitrarily long complete runs, unique normal form |
| [Potential](Descent/Potential.lean) | Exact per-step accounting, schedule-independent complete length, unary and binary closed forms |
| [Executor](Descent/Executor.lean) | Executable list scheduler justified by multiset descent; legal run witness and exact transition count |
| [Bounded](Descent/Bounded.lean) | Adversarial branching, universal budget, attaining execution, sharp worst-case theorem |
| [Countermodels](Descent/Countermodels.lean) | Failed scalar measures, non-strict self-loop, infinite descent over integers |

Start with the [reviewer guide](docs/REVIEWER_GUIDE.md), [mathematical model](docs/MODEL.md), [complete theorem index](docs/THEOREMS.md), and [verification details](docs/VERIFICATION.md).

## Foundations, attribution, and scope

The foundational Dershowitz–Manna theorem is **Mathlib's existing work**, imported from [`Mathlib.Data.Multiset.DershowitzManna`](https://github.com/leanprover-community/mathlib4/blob/9944fe2973b8dc0b86949101ed98232c07cd54a0/Mathlib/Data/Multiset/DershowitzManna.lean), whose listed authors are Haitian Wang and Malvin Gattinger. [Mathlib PR #14411](https://github.com/leanprover-community/mathlib4/pull/14411) is prior work and inspiration. This repository does not claim authorship of that theorem or an upstream Mathlib contribution.

This repository's development is the replacement interface, normalization framework, three branching models, exact and attained cost bounds, executable refinement, and hypothesis countermodels. It is an applied formalization, not a claim that these mathematical ideas are novel research. Development was AI-assisted; the public source, Lean kernel checks, dependency audit, and CI make the result independently inspectable. Hosting this repository alone does not establish unaided Lean expertise.

Proof dependencies are restricted to `propext`, `Classical.choice`, and `Quot.sound`. The audit rejects project axioms, unfinished proofs, and other proof axioms, including native decision axioms. See [verification](docs/VERIFICATION.md) for the precise trust boundary.

Original project files are MIT licensed. Mathlib and its dependencies retain their own licenses; they are fetched as dependencies, not vendored here.
