# Mathematical model

## Orientation

`Replacement target source`, `BranchStep target source`, `FixedStep b target source`, and `BoundedStep b target source` all put the smaller state first, matching a well-founded relation. In contrast, `Run step length source target` follows chronological execution order. Run statements therefore use `fun source target => BranchStep target source` (or the corresponding fixed/bounded relation).

Hydra moves are stated chronologically: `Move before after`. Their well-founded relation is the flipped `fun after before => Move before after`, and runs use `Run Move length before after` directly. Goodstein sequences are indexed by stage: `goodstein n k` is the value at stage `k`, written in base `k + 2`.

## Generic replacement

`Replacement M N` means there exist a common context `X`, finite children `Y`, and one parent `a` with `M = X + Y`, `N = X + {a}`, and `y < a` for every `y ∈ Y`. Repetitions matter: these are multisets, not finite sets. The empty child multiset permits deletion. `replacement_dm` embeds this relation in Mathlib's general Dershowitz–Manna order. Its well-foundedness is inherited under `[Preorder α] [WellFoundedLT α]`.

## The Dershowitz–Manna order and nested multisets

Mathlib's `IsDershowitzMannaLT M N` lets a nonempty part `Z` of `N` be replaced by any finite `Y` whose elements are each below some element of `Z`. `transGen_replacement_eq_dm` proves that this is exactly the transitive closure of `Replacement`. One direction uses Mathlib's transitivity lemma. For the other, elements of `Y` below the first replaced element are produced in one replacement, and the rest are handled by induction on `Z`.

`dm_irrefl` holds over every preorder, without well-foundedness: if `M = X + Y = X + Z`, then `Y = Z`, and a maximal element of the finite multiset `Z` has nothing in `Z` above it. With Mathlib's transitivity this makes `DM α`, a structure wrapping `Multiset α`, a partial order whose `<` is the Dershowitz–Manna order. Wrapping avoids a clash with Mathlib's inclusion order on `Multiset α`. `DM α` is well founded whenever `α` is.

`Nested 0 = PUnit` and `Nested (d + 1) = DM (Nested d)`. The order instances are defined by recursion on `d`, so `Nested d` is well founded for every `d` by `d` applications of Mathlib's theorem. `Nested.ofMultiset_lt_ofMultiset` holds by `Iff.rfl`: the order at level `d + 1` is literally the Dershowitz–Manna order over level `d`.

`dm_trichotomous` shows that the Dershowitz–Manna order is trichotomous over any trichotomous order. Remove the common part `M ∩ N`; the two remainders share no element, and the one containing the largest remaining element is the larger multiset. By induction on `d`, any two elements of `Nested d` are comparable (`Nested.lt_trichotomy`), so every level is a well-order (`Nested.instIsWellOrder`) and has an ordinal as its order type. `dm_add_left` adds a common context to both sides of a descent.

## Hydras

`Hydra` is the nested inductive type `node : List Hydra → Hydra`; a head is `node []`. `Move.chop` deletes a head attached to the root. `Regrow.here` cuts a head from a child `p` of the current node and replaces `p` by `k + 1` copies of `p` without that head, for any `k`. `Regrow.inside` performs a regrowing move inside one child. Positions are arbitrary list splits `left ++ x :: right`, so Hercules may cut any head.

`measure d` reads a hydra as an element of `Nested d`: a node becomes the multiset of its children's level-`d - 1` measures. Structure below depth `d` is truncated, so the decrease lemma assumes `before.height ≤ d`. All three move shapes are instances of one lemma, `measure_replace`: replacing one child by finitely many children of smaller measure is a single `Replacement` one level up. For `Regrow.here`, the damaged parent is smaller because it lost one child, which is a deletion one level further down.

`Move.height_le` shows that moves never increase height, so a battle from a hydra of height `d` stays at height at most `d`. Well-founded induction on `Nested d` then gives accessibility of every hydra, which is `move_wellFounded`. `no_infinite_battle` restates it as the absence of infinite move sequences.

Termination is not a uniform bound. From `neck = ((()))`, cutting the head with regrowth `k` leaves `k + 1` heads on the root, giving a complete battle of length `k + 2`. `arbitrarily_long_battles` records this, and `no_nat_measure` concludes that no natural-number measure decreases along every move. `size_can_increase` and `height_need_not_drop` show concrete failures of node count and height.

## The executable battle

`strike copies` implements one deterministic strategy. It cuts the first head on the root if there is one. Otherwise `regrowFirst` tries the children from left to right. A child with a head loses its first head and is replaced by `copies + 1` damaged copies. A child without heads is searched recursively, and the search moves past it only if that fails. `strike_move` proves that every strike is a legal `Move`. `strike_eq_none` proves that the strategy stops exactly at the bare root, so it never gets stuck early. Together with `move_not_from_dead`, this gives `terminal_iff_dead`: the bare root is the only hydra without a legal move.

`battleLength schedule stage hydra` counts the moves when stage `n` regrows `schedule n` new copies. It is defined by well-founded recursion along `move_wellFounded`. `battle_run` turns the computed count into a `Run Move` ending at `node []`. `kirbyParisLength` uses the classical schedule `n ↦ n` from stage one. `normalize_battle` shows that the generic normalizer, run on states `(hydra, stage)` ordered by their hydra, ends at `(node [], stage + battleLength schedule stage hydra)`.

## Goodstein sequences

Fix a base `B = b + 2`; writing bases this way removes every `2 ≤ B` side condition. For `n ≠ 0`, `exponent b n = log B n`, `digit b n = n / B ^ exponent`, and `remainder b n = n % B ^ exponent`. `digit_lt` and `remainder_lt_pow` show that these are genuine base-`B` digits and remainders. `terms b n` lists the leading exponent's notation `digit` times, followed by the terms of the remainder. Both recursive calls are on smaller numbers, since `exponent b n < n` and `remainder b n < n`. `rep b n = node (terms b n)` reuses the `Hydra` type, and `value B t` evaluates a tree, each child `c` contributing `B ^ value B c`. `value_rep` proves `value B (rep b n) = n`.

`bump b n = value (B + 1) (rep b n)` rewrites the notation in the next base, and `goodstein n (k + 1) = bump k (goodstein n k) - 1` follows the standard definition with base `k + 2` at stage `k`. The proof needs three facts about `bump`:

1. `bump_lt_bump`: base change is strictly monotone. For `x` with leading exponent `e`, induction and `bump_pow` map its remainder below `(B + 1) ^ bump b e`, so `bump b x < (B + 1) ^ (bump b e + 1)`. When the leading exponents differ, that bound is at most the leading term of `bump b y`. When they agree, compare leading digits, and then remainders by induction.
2. `rep_bump`: the base-`B + 1` notation of `bump b n` is literally `rep b n`. The leading exponent, digit, and remainder of `bump b n` are the images of those of `n`. The key bound is `bump_lt_pow`: a remainder below `B ^ e` maps below `(B + 1) ^ bump b e`.
3. `measure_rep_lt`: for a fixed base, `x < y` implies `measure d (rep b x) < measure d (rep b y)` in `Nested d`, assuming only that `rep b y` has height at most `d`. The case split is the same: a smaller leading exponent puts every child of `x` below the leading child of `y`; a smaller leading digit leaves one leading child of `y` to dominate the remainder of `x`; equal leading terms reduce to the remainders, with `dm_add_left` restoring the common part.

`height_rep_mono` shows that larger numbers have notations at least as tall. Along the sequence, the bump keeps the tree and subtracting one does not raise the height, so every notation fits in depth `d = (rep 0 n).height`. At each stage before zero, the measure in `Nested d` strictly drops: `rep_bump` rewrites the bumped value's notation as the previous tree, and `measure_rep_lt` compares it with the notation after subtracting one. An infinite sequence of nonzero values would be an infinite descent in a well-founded order, which proves `goodstein_terminates`.

`goodsteinLength n = Nat.find (goodstein_terminates n)` is the first stage with value zero. `Nat.find` is an executable upward search; its termination is exactly Goodstein's theorem. `goodstein_ne_zero_of_lt` and `goodstein_eq_zero_of_le` show that the value is nonzero before that stage and zero from then on.

## Normalization

The generic normalizer accepts an executable `next : State → Option State` and a proof that every returned successor is smaller in a supplied well-founded relation. Its result is reached through the *same* `next` function and is terminal for that strategy. This does not assert that every arbitrary rewrite system has a unique normal form. Uniqueness is proved separately for the natural-rank branching model, where only the empty worklist is terminal, and for battles, where only the bare root is terminal.

## Three natural-rank systems

A zero rank is deleted. A positive rank `n+1` is replaced by copies of `n`; a context retains every unselected task. `BranchStep` allows any natural offspring count at each step. `FixedStep b` requires exactly `b(n)` children. `BoundedStep b` allows any count `k ≤ b(n)`. These relations range over all task selections; the executable scheduler is one particular strategy.

Well-foundedness of `BranchStep` rules out infinite executions under arbitrary task selection and offspring choice. It imposes no uniform finite length bound from a state: for every budget, `{1}` has a longer complete run by choosing sufficiently many rank-zero children in its first step.

For a fixed policy, define `C(0)=1` and `C(n+1)=1+b(n)C(n)`. Each task includes its own processing step, including deletion of a zero task. The additive multiset potential `P` counts occurrences. Exact-step accounting telescopes over any finite execution. Thus every complete fixed-policy run has length exactly `P(source)`, independent of selection order.

For bounded branching, nonnegativity gives `1+P(target) ≤ P(source)` at every step. Telescoping gives `length+P(target) ≤ P(source)`, even for an incomplete prefix. Choosing the cap at every expansion is legal and yields a complete execution of length `P(source)` via the fixed-policy executor. This proves an attained maximum, not just a big-O estimate.

## Executability and cost interpretation

The list scheduler prepends the produced children and recursively processes the resulting worklist. Its termination relation is the inverse image of generic multiset replacement under the list-to-multiset quotient. No bound on list size, sum, maximum rank, or runtime is assumed. `steps_run` proves that its computed counter witnesses a legal complete multiset execution. `steps_exact` then derives equality with the independently defined potential.

Cost counts rewrite transitions or battle moves, not CPU instructions, memory use, Lean reduction steps, or wall-clock time. Large branching policies may produce enormous finite runs, and hydra battles and Goodstein sequences grow far faster. The theorem allows a rank-dependent cap; the finite regression sweep uses only constant policies 0–3. The executable battle samples and Goodstein starts are chosen to finish quickly.

## Hypotheses cannot simply be dropped

`Countermodels.lean` proves that size and rank sum can increase, maximum rank can stay unchanged, non-strict child comparison permits a one-state cycle, and integer ranks admit an infinite strict descent. The integer example deliberately lacks the well-founded base-order hypothesis. It does not contradict the natural-rank theorem.
