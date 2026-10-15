# Theorem index

**60 explicit theorems across eight modules.** Every explicit project theorem is listed below. Compiler-generated recursion and induction helpers are excluded from this inventory. `scripts/verify.py` checks that each entry is present in the proof audit.

## Descent/Bounded.lean

- `Descent.bounded_branch`
- `Descent.bounded_wellFounded`
- `Descent.fixed_bounded`
- `Descent.bounded_step_cost`
- `Descent.bounded_run_cost`
- `Descent.bounded_run_length`
- `Descent.budget_attained`
- `Descent.sharp_worst_case`

## Descent/Branching.lean

- `Descent.branch_replacement`
- `Descent.branching_wellFounded`
- `Descent.no_infinite_schedule`
- `Descent.branch_source_nonempty`
- `Descent.branch_delete`
- `Descent.branch_terminal_iff_empty`
- `Descent.consume_zeros`
- `Descent.arbitrarily_long_complete_runs`
- `Descent.branch_normal_form_unique`

## Descent/Countermodels.lean

- `Descent.Countermodels.size_and_sum_can_increase`
- `Descent.Countermodels.maximum_need_not_drop`
- `Descent.Countermodels.nonstrict_self_loop`
- `Descent.Countermodels.nonstrict_not_wellFounded`
- `Descent.Countermodels.integer_infinite_schedule`
- `Descent.Countermodels.integer_replacement_not_wellFounded`

## Descent/Executor.lean

- `Descent.Executor.next_none_iff_empty`
- `Descent.Executor.next_fixed_step`
- `Descent.Executor.next_descends`
- `Descent.Executor.finish_eq_empty`
- `Descent.Executor.finish_reachable`
- `Descent.Executor.steps_run`
- `Descent.Executor.steps_exact`
- `Descent.Executor.schedule_order_independent`

## Descent/Normalization.lean

- `Descent.normalize_terminal`
- `Descent.normalize_reachable`
- `Descent.normalize_of_terminal`
- `Descent.normalize_idempotent`
- `Descent.normalize_preserves`

## Descent/Potential.lean

- `Descent.potential_zero`
- `Descent.potential_add`
- `Descent.potential_singleton`
- `Descent.potential_replicate`
- `Descent.taskCost_positive`
- `Descent.fixed_branch`
- `Descent.fixed_wellFounded`
- `Descent.step_exact_cost`
- `Descent.run_exact_cost`
- `Descent.run_length_bound`
- `Descent.complete_run_length`
- `Descent.complete_schedules_equal_length`
- `Descent.unary_task_cost`
- `Descent.binary_task_cost`

## Descent/Replacement.lean

- `Descent.replacement_intro`
- `Descent.replacement_dm`
- `Descent.replacement_add_context`
- `Descent.replacement_delete`
- `Descent.replacement_wellFounded`
- `Descent.replacement_irrefl`
- `Descent.replacement_no_cycle`

## Descent/Runs.lean

- `Descent.Run.reachable`
- `Descent.Run.append`
- `Descent.Run.mono`
