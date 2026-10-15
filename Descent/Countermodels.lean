import Descent.Bounded
import Mathlib.Data.Int.Basic
import Mathlib.Data.Multiset.Lattice
import Mathlib.Order.Lattice.Nat

/-!
# Why the hypotheses and the multiset measure matter

These are proved countermodels, not failed proof attempts. Unbounded branching
can increase both worklist size and rank sum. Maximum rank need not decrease.
Allowing non-strict child ranks introduces a self-loop; allowing a non-well-founded
rank order permits a genuinely infinite descending schedule.
-/

namespace Descent.Countermodels

theorem size_and_sum_can_increase :
    BranchStep ({1, 1, 1} : Multiset ℕ) {2} ∧
    ({2} : Multiset ℕ).card < ({1, 1, 1} : Multiset ℕ).card ∧
    ({2} : Multiset ℕ).sum < ({1, 1, 1} : Multiset ℕ).sum := by
  constructor
  · simpa using BranchStep.grow 0 1 3
  · decide

/-- A rank-2 task remains while a different rank-2 task expands. -/
theorem maximum_need_not_drop :
    BranchStep ({2, 1, 1} : Multiset ℕ) {2, 2} ∧
    ({2, 1, 1} : Multiset ℕ).sup = ({2, 2} : Multiset ℕ).sup := by
  constructor
  · simpa [Multiset.cons_swap] using BranchStep.grow {2} 1 2
  · decide

def NonStrictReplacement (smaller larger : Multiset ℕ) : Prop :=
  ∃ (context children : Multiset ℕ) (parent : ℕ),
    smaller = context + children ∧ larger = context + {parent} ∧
    ∀ child ∈ children, child ≤ parent

theorem nonstrict_self_loop (rank : ℕ) : NonStrictReplacement {rank} {rank} := by
  exact ⟨0, {rank}, rank, by simp, by simp, by simp⟩

theorem nonstrict_not_wellFounded : ¬ WellFounded NonStrictReplacement := by
  intro wf
  exact wf.irrefl.irrefl {0} (nonstrict_self_loop 0)

/-- Strictness alone is insufficient when the rank order itself is not well founded. -/
theorem integer_infinite_schedule :
    ∃ states : ℕ → Multiset ℤ, ∀ n, Replacement (states (n + 1)) (states n) := by
  refine ⟨fun n => {-(n : ℤ)}, ?_⟩
  intro n
  refine ⟨0, {-((n + 1 : ℕ) : ℤ)}, -(n : ℤ), by simp, by simp, ?_⟩
  intro child hchild
  have he : child = -((n + 1 : ℕ) : ℤ) := by simpa using hchild
  subst child
  omega

theorem integer_replacement_not_wellFounded :
    ¬ WellFounded (Replacement (α := ℤ)) := by
  intro wf
  obtain ⟨states, hs⟩ := integer_infinite_schedule
  exact (wellFounded_iff_isEmpty_descending_chain.mp wf).false ⟨states, hs⟩

end Descent.Countermodels
