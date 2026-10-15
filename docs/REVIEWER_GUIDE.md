# A focused proof review

1. Inspect `replacement_dm` and `replacement_wellFounded` in `Descent/Replacement.lean`. This isolates the exact imported Mathlib foundation and its assumptions. The foundational ordering theorem is credited upstream.
2. Compare `no_infinite_schedule` with `arbitrarily_long_complete_runs` in `Descent/Branching.lean`. Check the quantifier distinction: each execution terminates, but the unbounded branching model has no uniform finite execution-length bound from `{1}`.
3. Read `step_exact_cost`, `run_exact_cost`, and `complete_schedules_equal_length` in `Descent/Potential.lean`. Cost is derived for all legal task selections, not just the implemented scheduler.
4. Inspect `next_fixed_step`, `steps_run`, and `steps_exact` in `Descent/Executor.lean`. These connect executable list operations to the abstract multiset semantics. Read `normalize_terminal` and `normalize_reachable` for the general strategy API.
5. Review `bounded_step_cost`, `budget_attained`, and `sharp_worst_case` in `Descent/Bounded.lean`. Verify both halves: every bounded schedule fits the budget, and one legal complete schedule reaches the bound exactly.
6. Read the countermodels to see which assumptions matter, then run `python3 scripts/verify.py`.

The formal library contains 60 explicit source theorems across eight modules. The dependency audit includes all project declarations (definitions and generated helpers as well as theorems). The larger compiler theorem count is not presented as the authored theorem count.

This is an AI-assisted, standalone Mathlib-based project. It is not an accepted Mathlib PR, a thesis, or evidence of historical human-only authorship. Applicants should be prepared to explain the statements, orientation conventions, termination argument, executable refinement, and exact-cost proof themselves.
