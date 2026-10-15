# Multiset Descent

[![Lean verification](https://github.com/starkbbk/lean-multiset-descent/actions/workflows/ci.yml/badge.svg)](https://github.com/starkbbk/lean-multiset-descent/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.33.0--rc1-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-pinned-purple)

**A Lean 4 / Mathlib development built on Mathlib's Dershowitz–Manna theorem: a public characterization of the order, well-founded nested multisets of every depth, termination of the Kirby–Paris hydra game, and sharp complexity certificates for branching worklists, each with a total executable counterpart.**

| Result | Lean statement | Module |
| --- | --- | --- |
| The Dershowitz–Manna order is the transitive closure of single-element replacement | [`transGen_replacement_eq_dm`](Descent/Ordering.lean) | Ordering |
| It is irreflexive over every preorder, hence a partial order on the synonym `DM α` | [`dm_irrefl`](Descent/Ordering.lean) | Ordering |
| Multisets nested to any finite depth are well founded | [`nested_wellFounded`](Descent/Ordering.lean) | Ordering |
| Every hydra battle ends, whichever heads are cut and however many copies regrow | [`move_wellFounded`](Descent/Hydra.lean), [`no_infinite_battle`](Descent/Hydra.lean) | Hydra |
| Termination gives no uniform bound: one fixed hydra has arbitrarily long battles, so no natural-number measure works | [`arbitrarily_long_battles`](Descent/Hydra.lean), [`no_nat_measure`](Descent/Hydra.lean) | Hydra |
| A total executable battle whose computed length is witnessed by a legal battle that kills the hydra | [`battle_run`](Descent/Battle.lean), [`normalize_battle`](Descent/Battle.lean) | Battle |
| Bounded adversarial branching: a universal budget and a complete run attaining it exactly | [`sharp_worst_case`](Descent/Bounded.lean) | Bounded |
| Fixed branching: every complete schedule has the same, exactly computed length | [`complete_schedules_equal_length`](Descent/Potential.lean) | Potential |

**100 explicit theorems · 11 proof modules · two verified total executors · 340 scheduler configurations · 10 hydra battles cross-checked against an independent Python simulation · dependency audit with negative controls.**

## Hydra battles

A hydra is a finite rooted tree; its heads are the nodes without children. Hercules cuts one head per move. A head on the root simply disappears. Otherwise its damaged parent, with that head removed, is replaced under the grandparent by `k + 1` copies of itself, where `k` is chosen freely at every move. Hydras can grow without limit, and [`no_nat_measure`](Descent/Hydra.lean) proves that no natural-number measure decreases along every move.

[`move_wellFounded`](Descent/Hydra.lean) proves that every battle ends. A hydra of height at most `d` is read as an element of `Nested d`, the multisets nested to depth `d`. Each level orders multisets of the level below by the Dershowitz–Manna order, so its well-foundedness is Mathlib's theorem applied `d` times. Every move strictly lowers the measure and never raises the height. Kirby and Paris (1982) proved that termination of this game, already for the classical schedule regrowing `n` copies at stage `n`, cannot be proved in Peano arithmetic.

[`battleLength`](Descent/Battle.lean) runs a deterministic left-to-right strategy for Hercules under any regrowth schedule. It is a total function whose termination argument is `move_wellFounded`, with no fuel, size bound, or height bound. [`battle_run`](Descent/Battle.lean) proves that the computed number of moves is witnessed by a legal battle ending at the bare root. [`normalize_battle`](Descent/Battle.lean) proves that the generic strategy normalizer from `Descent/Normalization.lean` runs the same battle. Under the classical schedule:

| Hydra (bracket notation) | `(())` | `((()))` | `(((())))` | `((())(()()))` | `((())(()())())` |
| --- | --- | --- | --- | --- | --- |
| Moves | 1 | 3 | 37 | 221 | 1149 |

The path with four edges, `((((()))))`, also has a total battle, but it is far too long to run.

## Sharp complexity for branching worklists

A work item of rank `n + 1` can spawn any finite number of rank-`n` children. An unordered scheduler can pick any item. The worklist can grow, its rank sum can increase, and its maximum rank can stay unchanged. Nevertheless, every schedule terminates by Dershowitz–Manna multiset descent. The quantitative part distinguishes three different claims:

| Branching model | What is proved |
| --- | --- |
| Arbitrary finite offspring at each step | No infinite schedule; complete runs from the fixed state `{1}` can still be arbitrarily long |
| A fixed rank-dependent offspring policy | Every complete schedule has exactly the same number of transitions |
| An adversary choosing up to a rank-dependent cap | A universal worst-case upper bound, together with a complete run attaining it exactly |

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
((()))   → (()()())     nodes: 3 → 4
((())(()))  → (()(()))  height: 2 → 2
```

The third family has no uniform finite bound when `k` is unrestricted, despite termination of every individual schedule. These examples and the unbounded-length claims are proved in Lean. Additional countermodels show why strict child ranks and a well-founded base order are essential.

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
python3 scripts/verify.py --write-index
```

The demo runs the verified depth-first executor against an independent fuel-bounded FIFO simulator, reversed task order, the potential formula, and the final normal form on all 340 configurations (offspring 0–3; list length 0–3; ranks 0–3). It then runs ten Kirby–Paris battles, checking that the move counter and the generic normalizer agree and that every hydra dies. `scripts/verify.py` recomputes each battle length with an independent Python simulation and checks that two demo runs print identical output. Fuel exists only in the FIFO regression oracle. The verified normalizers and counters use checked well-founded recursion with no fuel parameter or partial function.

## Review the proofs

| Module | Role |
| --- | --- |
| [Replacement](Descent/Replacement.lean) | Generic contextual replacement, Mathlib bridge, well-foundedness and absence of cycles |
| [Ordering](Descent/Ordering.lean) | Dershowitz–Manna order as the transitive closure of replacement, irreflexivity over preorders, the `DM` partial order, nested multisets of every depth |
| [Normalization](Descent/Normalization.lean) | Strategy-parametric total normalizer, terminality, actual strategy reachability, idempotence, invariant preservation |
| [Runs](Descent/Runs.lean) | Length-indexed executions, composition, relation inclusion |
| [Branching](Descent/Branching.lean) | Unbounded nondeterministic rewriting, no infinite schedules, arbitrarily long complete runs, unique normal form |
| [Potential](Descent/Potential.lean) | Exact per-step accounting, schedule-independent complete length, unary and binary closed forms |
| [Executor](Descent/Executor.lean) | Executable list scheduler justified by multiset descent; legal run witness and exact transition count |
| [Bounded](Descent/Bounded.lean) | Adversarial branching, universal budget, attaining execution, sharp worst-case theorem |
| [Countermodels](Descent/Countermodels.lean) | Failed scalar measures, non-strict self-loop, infinite descent over integers |
| [Hydra](Descent/Hydra.lean) | Kirby–Paris moves, nested-multiset measure, height monotonicity, termination, arbitrarily long battles, failed size measures |
| [Battle](Descent/Battle.lean) | Hercules' executable strategy, soundness of each strike, the bare root as the only terminal hydra, total battle length, agreement with the generic normalizer |

Start with the [reviewer guide](docs/REVIEWER_GUIDE.md), [mathematical model](docs/MODEL.md), [complete theorem index](docs/THEOREMS.md), and [verification details](docs/VERIFICATION.md).

## Foundations, attribution, and scope

The foundational Dershowitz–Manna theorem is **Mathlib's existing work**, imported from [`Mathlib.Data.Multiset.DershowitzManna`](https://github.com/leanprover-community/mathlib4/blob/9944fe2973b8dc0b86949101ed98232c07cd54a0/Mathlib/Data/Multiset/DershowitzManna.lean), whose listed authors are Haitian Wang and Malvin Gattinger. [Mathlib PR #14411](https://github.com/leanprover-community/mathlib4/pull/14411) is prior work and inspiration. Mathlib also proves the transitive-closure characterization internally, through a private relation; `transGen_replacement_eq_dm` is a separate public proof for this repository's `Replacement`. This repository does not claim authorship of the Dershowitz–Manna theorem or an upstream Mathlib contribution.

The mathematics is classical: multiset and nested multiset orderings are due to Dershowitz and Manna, *Proving termination with multiset orderings* (Communications of the ACM, 1979), and the hydra game to Kirby and Paris, *Accessible independence results for Peano arithmetic* (Bulletin of the London Mathematical Society, 1982). This repository's development is the public characterization, the nested-multiset construction, the hydra and battle formalization, the replacement interface, normalization framework, three branching models, exact and attained cost bounds, executable refinements, and hypothesis countermodels. It is an applied formalization, not a claim that these mathematical ideas are novel research. Development was AI-assisted; the public source, Lean kernel checks, dependency audit, and CI make the result independently inspectable. Hosting this repository alone does not establish unaided Lean expertise.

Proof dependencies are restricted to `propext`, `Classical.choice`, and `Quot.sound`. The audit rejects project axioms, unfinished proofs, and other proof axioms, including native decision axioms. See [verification](docs/VERIFICATION.md) for the precise trust boundary.

Original project files are MIT licensed. Mathlib and its dependencies retain their own licenses; they are fetched as dependencies, not vendored here.
