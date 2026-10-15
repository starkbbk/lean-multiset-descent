import Descent.Executor

/-!
# An attained worst-case bound for nondeterministic branching

The adversary may choose both the next task and any child count below a
rank-dependent cap. The fixed-policy potential is a sharp upper bound: every
admissible execution fits the budget, and a legal complete execution attains it.
-/

namespace Descent

inductive BoundedStep (cap : ℕ → ℕ) : Multiset ℕ → Multiset ℕ → Prop
  | zero (context : Multiset ℕ) : BoundedStep cap context (context + {0})
  | grow (context : Multiset ℕ) (rank count : ℕ) (allowed : count ≤ cap rank) :
      BoundedStep cap (context + Multiset.replicate count rank) (context + {rank + 1})

theorem bounded_branch {cap : ℕ → ℕ} {target source : Multiset ℕ}
    (h : BoundedStep cap target source) : BranchStep target source := by
  cases h with
  | zero => exact .zero _
  | grow context rank count => exact .grow context rank count

theorem bounded_wellFounded (cap : ℕ → ℕ) : WellFounded (BoundedStep cap) :=
  branching_wellFounded.mono fun _ _ h => bounded_branch h

theorem fixed_bounded {cap : ℕ → ℕ} {target source : Multiset ℕ}
    (h : FixedStep cap target source) : BoundedStep cap target source := by
  cases h with
  | zero => exact .zero _
  | grow context rank => exact .grow context rank (cap rank) (Nat.le_refl _)

theorem bounded_step_cost {cap : ℕ → ℕ} {target source : Multiset ℕ}
    (h : BoundedStep cap target source) :
    potential cap target + 1 ≤ potential cap source := by
  cases h with
  | zero context => simp [taskCost]
  | grow context rank count allowed =>
    have hm := Nat.mul_le_mul_right (taskCost cap rank) allowed
    simp only [potential_add, potential_replicate, potential_singleton, taskCost]
    omega

theorem bounded_run_cost {cap : ℕ → ℕ} {length : ℕ} {source target : Multiset ℕ}
    (run : Run (fun s t => BoundedStep cap t s) length source target) :
    length + potential cap target ≤ potential cap source := by
  induction run with
  | done => simp
  | next hstep _ ih =>
    have hc := bounded_step_cost hstep
    omega

theorem bounded_run_length {cap : ℕ → ℕ} {length : ℕ} {source target : Multiset ℕ}
    (run : Run (fun s t => BoundedStep cap t s) length source target) :
    length ≤ potential cap source := by
  have hc := bounded_run_cost run
  omega

/-- The upper bound is achieved, rather than merely asymptotically tight. -/
theorem budget_attained (cap : ℕ → ℕ) (source : Multiset ℕ) :
    Run (fun s t => BoundedStep cap t s) (potential cap source) source 0 := by
  induction source using Quot.inductionOn with
  | h tasks =>
    have run := (Executor.steps_run cap tasks).mono (fun h => fixed_bounded h)
    rwa [Executor.steps_exact] at run

/-- A quantitative certificate covering every schedule and exhibiting an optimal one. -/
theorem sharp_worst_case (cap : ℕ → ℕ) (source : Multiset ℕ) :
    (∀ length target, Run (fun s t => BoundedStep cap t s) length source target →
      length ≤ potential cap source) ∧
    Run (fun s t => BoundedStep cap t s) (potential cap source) source 0 :=
  ⟨fun _ _ run => bounded_run_length run, budget_attained cap source⟩

end Descent
