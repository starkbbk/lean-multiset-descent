# Mathematical model

## Orientation

`Replacement target source`, `BranchStep target source`, `FixedStep b target source`, and `BoundedStep b target source` all put the smaller state first, matching a well-founded relation. In contrast, `Run step length source target` follows chronological execution order. Run statements therefore use `fun source target => BranchStep target source` (or the corresponding fixed/bounded relation).

## Generic replacement

`Replacement M N` means there exist a common context `X`, finite children `Y`, and one parent `a` with `M = X + Y`, `N = X + {a}`, and `y < a` for every `y ∈ Y`. Repetitions matter: these are multisets, not finite sets. The empty child multiset permits deletion. `replacement_dm` embeds this relation in Mathlib's general Dershowitz–Manna order. Its well-foundedness is inherited under `[Preorder α] [WellFoundedLT α]`.

The generic normalizer accepts an executable `next : State → Option State` and a proof that every returned successor is smaller in a supplied well-founded relation. Its result is reached through the *same* `next` function and is terminal for that strategy. This does not assert that every arbitrary rewrite system has a unique normal form. Uniqueness is proved separately for the natural-rank branching model, where only the empty worklist is terminal.

## Three natural-rank systems

A zero rank is deleted. A positive rank `n+1` is replaced by copies of `n`; a context retains every unselected task. `BranchStep` allows any natural offspring count at each step. `FixedStep b` requires exactly `b(n)` children. `BoundedStep b` allows any count `k ≤ b(n)`. These relations range over all task selections; the executable scheduler is one particular strategy.

Well-foundedness of `BranchStep` rules out infinite executions under arbitrary task selection and offspring choice. It imposes no uniform finite length bound from a state: for every budget, `{1}` has a longer complete run by choosing sufficiently many rank-zero children in its first step.

For a fixed policy, define `C(0)=1` and `C(n+1)=1+b(n)C(n)`. Each task includes its own processing step, including deletion of a zero task. The additive multiset potential `P` counts occurrences. Exact-step accounting telescopes over any finite execution. Thus every complete fixed-policy run has length exactly `P(source)`, independent of selection order.

For bounded branching, nonnegativity gives `1+P(target) ≤ P(source)` at every step. Telescoping gives `length+P(target) ≤ P(source)`, even for an incomplete prefix. Choosing the cap at every expansion is legal and yields a complete execution of length `P(source)` via the fixed-policy executor. This proves an attained maximum, not just a big-O estimate.

## Executability and cost interpretation

The list scheduler prepends the produced children and recursively processes the resulting worklist. Its termination relation is the inverse image of generic multiset replacement under the list-to-multiset quotient. No bound on list size, sum, maximum rank, or runtime is assumed. `steps_run` proves that its computed counter witnesses a legal complete multiset execution. `steps_exact` then derives equality with the independently defined potential.

Cost counts rewrite transitions, not CPU instructions, memory use, Lean reduction steps, or wall-clock time. Large branching policies may produce enormous finite runs. The theorem allows a rank-dependent cap; the finite regression sweep uses only constant policies 0–3.

## Hypotheses cannot simply be dropped

`Countermodels.lean` proves that size and rank sum can increase, maximum rank can stay unchanged, non-strict child comparison permits a one-state cycle, and integer ranks admit an infinite strict descent. The integer example deliberately lacks the well-founded base-order hypothesis. It does not contradict the natural-rank theorem.
