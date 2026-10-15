import Descent.Branching
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Exact work for a fixed branching policy

Fix the number of children produced at each rank. A recursively defined task
cost then gives an exact potential: every legal step consumes exactly one unit.
Unlike the unbounded system, this supplies a uniform bound on every schedule
and proves equal lengths for all complete executions from the same state.
-/

namespace Descent

def taskCost (offspring : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | rank + 1 => 1 + offspring rank * taskCost offspring rank

def potential (offspring : ℕ → ℕ) (state : Multiset ℕ) : ℕ :=
  (state.map (taskCost offspring)).sum

@[simp] theorem potential_zero (offspring : ℕ → ℕ) : potential offspring 0 = 0 := by
  simp [potential]

@[simp] theorem potential_add (offspring : ℕ → ℕ) (left right : Multiset ℕ) :
    potential offspring (left + right) = potential offspring left + potential offspring right := by
  simp [potential]

@[simp] theorem potential_singleton (offspring : ℕ → ℕ) (rank : ℕ) :
    potential offspring {rank} = taskCost offspring rank := by simp [potential]

@[simp] theorem potential_replicate (offspring : ℕ → ℕ) (count rank : ℕ) :
    potential offspring (Multiset.replicate count rank) = count * taskCost offspring rank := by
  simp [potential]

theorem taskCost_positive (offspring : ℕ → ℕ) (rank : ℕ) : 0 < taskCost offspring rank := by
  cases rank <;> simp only [taskCost] <;> omega

inductive FixedStep (offspring : ℕ → ℕ) : Multiset ℕ → Multiset ℕ → Prop
  | zero (context : Multiset ℕ) : FixedStep offspring context (context + {0})
  | grow (context : Multiset ℕ) (rank : ℕ) :
      FixedStep offspring (context + Multiset.replicate (offspring rank) rank)
        (context + {rank + 1})

theorem fixed_branch {offspring : ℕ → ℕ} {target source : Multiset ℕ}
    (h : FixedStep offspring target source) : BranchStep target source := by
  cases h with
  | zero => exact .zero _
  | grow context rank => exact .grow context rank (offspring rank)

theorem fixed_wellFounded (offspring : ℕ → ℕ) : WellFounded (FixedStep offspring) :=
  branching_wellFounded.mono fun _ _ h => fixed_branch h

/-- This identity is stronger than merely proving that potential decreases. -/
theorem step_exact_cost {offspring : ℕ → ℕ} {target source : Multiset ℕ}
    (h : FixedStep offspring target source) :
    potential offspring source = potential offspring target + 1 := by
  cases h with
  | zero context => simp [taskCost]
  | grow context rank => simp [taskCost, Nat.add_assoc, Nat.add_comm]

/-- Telescoping over a length-indexed execution gives its exact work identity. -/
theorem run_exact_cost {offspring : ℕ → ℕ} {length : ℕ} {source target : Multiset ℕ}
    (run : Run (fun s t => FixedStep offspring t s) length source target) :
    potential offspring source = length + potential offspring target := by
  induction run with
  | done => simp
  | next hstep _ ih =>
    have hc := step_exact_cost hstep
    omega

theorem run_length_bound {offspring : ℕ → ℕ} {length : ℕ} {source target : Multiset ℕ}
    (run : Run (fun s t => FixedStep offspring t s) length source target) :
    length ≤ potential offspring source := by
  have h := run_exact_cost run
  omega

theorem complete_run_length {offspring : ℕ → ℕ} {length : ℕ} {source : Multiset ℕ}
    (run : Run (fun s t => FixedStep offspring t s) length source 0) :
    length = potential offspring source := by
  simpa using (run_exact_cost run).symm

/-- Equal total work does not assume the same task-selection order. -/
theorem complete_schedules_equal_length {offspring : ℕ → ℕ} {n m : ℕ}
    {source : Multiset ℕ}
    (left : Run (fun s t => FixedStep offspring t s) n source 0)
    (right : Run (fun s t => FixedStep offspring t s) m source 0) : n = m :=
  (complete_run_length left).trans (complete_run_length right).symm

theorem unary_task_cost (rank : ℕ) : taskCost (fun _ => 1) rank = rank + 1 := by
  induction rank with
  | zero => rfl
  | succ rank ih => simp [taskCost, ih, Nat.add_comm]

/-- A binary-branching task has exponentially many transitions, including
deletion of the zero-ranked leaves. The addition avoids truncated subtraction. -/
theorem binary_task_cost (rank : ℕ) : taskCost (fun _ => 2) rank + 1 = 2 ^ (rank + 1) := by
  induction rank with
  | zero => rfl
  | succ rank ih =>
    simp only [taskCost]
    rw [pow_succ]
    omega

end Descent
