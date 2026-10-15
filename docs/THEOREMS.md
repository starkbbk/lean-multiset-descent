# Theorem index

**135 explicit theorems across 12 modules.** Every explicit project theorem is listed below. Compiler-generated recursion and induction helpers are excluded from this inventory. `scripts/verify.py` checks that each entry is present in the proof audit; `python3 scripts/verify.py --write-index` regenerates this file.

## Descent/Battle.lean

- `Descent.Hydra.chopFirst_some`
- `Descent.Hydra.chopFirst_eq_none`
- `Descent.Hydra.Regrow.cons`
- `Descent.Hydra.regrowFirst_regrow`
- `Descent.Hydra.regrowFirst_eq_none`
- `Descent.Hydra.strike_move`
- `Descent.Hydra.strike_eq_none`
- `Descent.Hydra.terminal_iff_dead`
- `Descent.Hydra.battle_run`
- `Descent.Hydra.kirbyParis_run`
- `Descent.Hydra.battleNext_sound`
- `Descent.Hydra.normalize_battle`
- `Descent.Hydra.finalState_eq`

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

## Descent/Goodstein.lean

- `Descent.Goodstein.value_node`
- `Descent.Goodstein.valueList_append`
- `Descent.Goodstein.valueList_replicate`
- `Descent.Goodstein.pow_exponent_pos`
- `Descent.Goodstein.pow_exponent_le`
- `Descent.Goodstein.exponent_lt`
- `Descent.Goodstein.remainder_lt_pow`
- `Descent.Goodstein.remainder_lt`
- `Descent.Goodstein.digit_pos`
- `Descent.Goodstein.digit_lt`
- `Descent.Goodstein.pow_mul_digit_add_remainder`
- `Descent.Goodstein.terms_zero`
- `Descent.Goodstein.terms_of_ne_zero`
- `Descent.Goodstein.rep_zero`
- `Descent.Goodstein.value_rep`
- `Descent.Goodstein.rep_exponent_mem`
- `Descent.Goodstein.mem_terms`
- `Descent.Goodstein.le_exponent_of_pow_le`
- `Descent.Goodstein.bump_zero`
- `Descent.Goodstein.bump_of_ne_zero`
- `Descent.Goodstein.bump_pow`
- `Descent.Goodstein.bump_lt_bump`
- `Descent.Goodstein.bump_lt_pow`
- `Descent.Goodstein.bump_pos`
- `Descent.Goodstein.rep_bump`
- `Descent.Goodstein.height_rep_mono`
- `Descent.Goodstein.measure_rep_lt`
- `Descent.Goodstein.goodstein_terminates`
- `Descent.Goodstein.goodstein_succ_eq_zero`
- `Descent.Goodstein.goodstein_goodsteinLength`
- `Descent.Goodstein.goodstein_ne_zero_of_lt`
- `Descent.Goodstein.goodstein_eq_zero_of_le`

## Descent/Hydra.lean

- `Descent.Hydra.heightList_le_iff`
- `Descent.Hydra.height_le_iff`
- `Descent.Hydra.height_lt_of_mem`
- `Descent.Hydra.height_le_of_subset`
- `Descent.Hydra.Regrow.height_le`
- `Descent.Hydra.Move.height_le`
- `Descent.Hydra.measure_replace`
- `Descent.Hydra.Regrow.measure_lt`
- `Descent.Hydra.Move.measure_lt`
- `Descent.Hydra.move_wellFounded`
- `Descent.Hydra.no_infinite_battle`
- `Descent.Hydra.move_not_from_dead`
- `Descent.Hydra.chop_all_heads`
- `Descent.Hydra.arbitrarily_long_battles`
- `Descent.Hydra.no_nat_measure`
- `Descent.Hydra.size_can_increase`
- `Descent.Hydra.height_need_not_drop`

## Descent/Normalization.lean

- `Descent.normalize_terminal`
- `Descent.normalize_reachable`
- `Descent.normalize_of_terminal`
- `Descent.normalize_idempotent`
- `Descent.normalize_preserves`

## Descent/Ordering.lean

- `Descent.dm_of_transGen_replacement`
- `Descent.transGen_replacement_of_dm`
- `Descent.transGen_replacement_iff`
- `Descent.transGen_replacement_eq_dm`
- `Descent.exists_maximal_mem`
- `Descent.dm_irrefl`
- `Descent.dm_asymm`
- `Descent.dm_trichotomous`
- `Descent.dm_add_left`
- `Descent.DM.lt_iff`
- `Descent.Nested.ofMultiset_lt_ofMultiset`
- `Descent.nested_wellFounded`
- `Descent.Nested.lt_trichotomy`

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
