import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Basic

/-! # Length-indexed executions, with explicit source-to-target orientation -/

namespace Descent

inductive Run {State : Type*} (step : State → State → Prop) :
    ℕ → State → State → Prop
  | done (state) : Run step 0 state state
  | next {source middle target n} : step source middle → Run step n middle target →
      Run step (n + 1) source target

theorem Run.reachable {State : Type*} {step : State → State → Prop}
    {n : ℕ} {source target : State} (h : Run step n source target) :
    Relation.ReflTransGen step source target := by
  induction h with
  | done => exact .refl
  | next hstep _ ih => exact .head hstep ih

theorem Run.append {State : Type*} {step : State → State → Prop}
    {n m : ℕ} {source middle target : State}
    (first : Run step n source middle) (second : Run step m middle target) :
    Run step (n + m) source target := by
  induction first with
  | done => simpa using second
  | next hstep _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.next hstep (ih second)

/-- Transport an execution along an inclusion of step relations. -/
theorem Run.mono {State : Type*} {first second : State → State → Prop}
    (includeStep : ∀ {source target}, first source target → second source target)
    {n : ℕ} {source target : State} (run : Run first n source target) :
    Run second n source target := by
  induction run with
  | done => exact .done _
  | next hstep _ ih => exact .next (includeStep hstep) ih

end Descent
