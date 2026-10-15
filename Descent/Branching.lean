import Descent.Replacement
import Descent.Runs
import Mathlib.Data.Multiset.Replicate
import Lean.Elab.Tactic.Omega

/-!
# Unbounded finite branching still terminates

A zero-ranked task disappears. A task of rank `n + 1` may be replaced by any
finite number of tasks of rank `n`. There is no fixed branching bound, and the
multiset is unordered: any task may be selected at each step.
-/

namespace Descent

inductive BranchStep : Multiset ℕ → Multiset ℕ → Prop
  | zero (context : Multiset ℕ) : BranchStep context (context + {0})
  | grow (context : Multiset ℕ) (rank offspring : ℕ) :
      BranchStep (context + Multiset.replicate offspring rank) (context + {rank + 1})

theorem branch_replacement {target source : Multiset ℕ}
    (h : BranchStep target source) : Replacement target source := by
  cases h with
  | zero => exact replacement_delete _ 0
  | grow context rank offspring =>
    apply replacement_intro
    intro child hc
    have heq := Multiset.eq_of_mem_replicate hc
    omega

theorem branching_wellFounded : WellFounded BranchStep :=
  replacement_wellFounded.mono fun _ _ h => branch_replacement h

/-- Termination holds even when an adversary chooses task and offspring count. -/
theorem no_infinite_schedule :
    ¬ ∃ states : ℕ → Multiset ℕ, ∀ n, BranchStep (states (n + 1)) (states n) := by
  rintro ⟨states, hsteps⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp branching_wellFounded).false
    ⟨states, hsteps⟩

theorem branch_source_nonempty {target source : Multiset ℕ}
    (h : BranchStep target source) : source ≠ 0 := by
  rcases branch_replacement h with ⟨context, children, parent, _, hs, _⟩
  intro hz
  have hc := congrArg Multiset.card hs
  simp [hz] at hc

theorem branch_delete (context : Multiset ℕ) (rank : ℕ) :
    BranchStep context (context + {rank}) := by
  cases rank with
  | zero => exact .zero context
  | succ n => simpa using BranchStep.grow context n 0

theorem branch_terminal_iff_empty (state : Multiset ℕ) :
    (¬ ∃ target, BranchStep target state) ↔ state = 0 := by
  constructor
  · intro h
    induction state using Multiset.induction_on with
    | empty => rfl
    | cons rank rest _ =>
      exact False.elim (h ⟨rest, by
        rw [← Multiset.singleton_add, Multiset.add_comm]
        exact branch_delete rest rank⟩)
  · rintro rfl ⟨target, h⟩
    exact branch_source_nonempty h rfl

/-- A zero-only worklist has an execution of exactly its cardinality. -/
theorem consume_zeros (count : ℕ) :
    Run (fun source target => BranchStep target source) count
      (Multiset.replicate count 0) 0 := by
  induction count with
  | zero => simpa using Run.done (step := fun s t => BranchStep t s) (0 : Multiset ℕ)
  | succ n ih =>
    apply Run.next (middle := Multiset.replicate n 0) ?_ ih
    rw [Multiset.replicate_succ, ← Multiset.singleton_add, Multiset.add_comm]
    exact BranchStep.zero (Multiset.replicate n 0)

/-- A fixed one-task initial state admits arbitrarily long complete executions.
Well-foundedness therefore does not imply a uniform natural-number time bound. -/
theorem arbitrarily_long_complete_runs (budget : ℕ) :
    ∃ length, budget < length ∧
      Run (fun source target => BranchStep target source) length ({1} : Multiset ℕ) 0 := by
  refine ⟨budget + 2, by omega, ?_⟩
  apply Run.next (middle := Multiset.replicate (budget + 1) 0)
    (by simpa using BranchStep.grow 0 0 (budget + 1))
    (consume_zeros (budget + 1))

theorem branch_normal_form_unique {left right : Multiset ℕ}
    (hl : ¬ ∃ target, BranchStep target left) (hr : ¬ ∃ target, BranchStep target right) :
    left = right := by
  rw [(branch_terminal_iff_empty left).1 hl, (branch_terminal_iff_empty right).1 hr]

end Descent
