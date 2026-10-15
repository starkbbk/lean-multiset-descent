# A focused proof review

1. Inspect `replacement_dm` and `replacement_wellFounded` in `Descent/Replacement.lean`. This isolates the exact imported Mathlib foundation and its assumptions. The foundational ordering theorem is credited upstream.
2. Read `transGen_replacement_of_dm`, `dm_irrefl`, and the `Nested` instances in `Descent/Ordering.lean`. Check that irreflexivity needs only a preorder, and that `Nested.ofMultiset_lt_ofMultiset` is `Iff.rfl`, so each nesting level really is the Dershowitz–Manna order over the previous level.
3. In `Descent/Hydra.lean`, compare `Regrow` and `Move` with the Kirby–Paris rules, then read `measure_replace`, `Regrow.measure_lt`, `Move.height_le`, and `move_wellFounded`. Note where the hypothesis `before.height ≤ d` is used, and why height monotonicity lets one fixed depth serve a whole battle.
4. Compare `move_wellFounded` with `arbitrarily_long_battles` and `no_nat_measure`. As with branching worklists, every battle ends but there is no uniform bound, so no natural-number measure can replace nested multisets.
5. In `Descent/Battle.lean`, check `strike_move` (soundness), `strike_eq_none` (the strategy stops only at the bare root), `terminal_iff_dead`, `battle_run`, and `normalize_battle`. The battle length is a total function for every regrowth schedule.
6. Compare `no_infinite_schedule` with `arbitrarily_long_complete_runs` in `Descent/Branching.lean`. Check the same quantifier distinction for worklists from `{1}`.
7. Read `step_exact_cost`, `run_exact_cost`, and `complete_schedules_equal_length` in `Descent/Potential.lean`. Cost is derived for all legal task selections, not just the implemented scheduler.
8. Inspect `next_fixed_step`, `steps_run`, and `steps_exact` in `Descent/Executor.lean`. These connect executable list operations to the abstract multiset semantics. Read `normalize_terminal` and `normalize_reachable` for the general strategy API.
9. Review `bounded_step_cost`, `budget_attained`, and `sharp_worst_case` in `Descent/Bounded.lean`. Verify both halves: every bounded schedule fits the budget, and one legal complete schedule reaches the bound exactly.
10. Read the countermodels to see which assumptions matter, then run `python3 scripts/verify.py`.

The formal library contains 100 explicit source theorems across eleven modules. The dependency audit includes all project declarations (definitions, instances, and generated helpers as well as theorems). The larger compiler theorem count is not presented as the authored theorem count.

This is an AI-assisted, standalone Mathlib-based project. It is not an accepted Mathlib PR, a thesis, or evidence of historical human-only authorship. Applicants should be prepared to explain the statements, orientation conventions, the nested-multiset termination argument, executable refinements, and the exact-cost proof themselves.
