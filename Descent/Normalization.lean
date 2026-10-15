import Descent.Replacement

/-!
# Strategy-parametric well-founded normalization

The result follows the actual supplied `next` function. Its reachability theorem
uses that exact strategy's transition relation, not merely an unrelated order.
Termination follows from a caller-supplied soundness proof into a well-founded
relation. The implementation uses Lean's checked well-founded recursion.
-/

namespace Descent

variable {State : Type*} [order : WellFoundedRelation State]

def StrategyStep (next : State → Option State) (source target : State) : Prop :=
  next source = some target

def normalize (next : State → Option State)
    (sound : ∀ source target, next source = some target →
      order.rel target source) (state : State) : State :=
  match _h : next state with
  | none => state
  | some target => normalize next sound target
termination_by state
decreasing_by exact sound _ _ _h

/-- The returned state is terminal for the supplied executable strategy. -/
theorem normalize_terminal (next : State → Option State)
    (sound : ∀ source target, next source = some target →
      order.rel target source) (state : State) :
    next (normalize next sound state) = none := by
  induction state using order.wf.induction with
  | h state ih =>
    rw [normalize]
    split
    next hnone => exact hnone
    next target hsome => exact ih target (sound state target hsome)

/-- The returned state is reached through actual strategy transitions. -/
theorem normalize_reachable (next : State → Option State)
    (sound : ∀ source target, next source = some target →
      order.rel target source) (state : State) :
    Relation.ReflTransGen (StrategyStep next) state (normalize next sound state) := by
  induction state using order.wf.induction with
  | h state ih =>
    rw [normalize]
    split
    next => exact .refl
    next target hsome =>
      exact Relation.ReflTransGen.head hsome (ih target (sound state target hsome))

theorem normalize_of_terminal (next : State → Option State)
    (sound : ∀ source target, next source = some target →
      order.rel target source) {state : State} (h : next state = none) :
    normalize next sound state = state := by
  rw [normalize, h]

theorem normalize_idempotent (next : State → Option State)
    (sound : ∀ source target, next source = some target →
      order.rel target source) (state : State) :
    normalize next sound (normalize next sound state) = normalize next sound state :=
  normalize_of_terminal next sound (normalize_terminal next sound state)

/-- Any invariant preserved by strategy steps is preserved by normalization. -/
theorem normalize_preserves (next : State → Option State)
    (sound : ∀ source target, next source = some target →
      order.rel target source) (P : State → Prop)
    (step_preserves : ∀ source target, next source = some target → P source → P target)
    {state : State} (hP : P state) : P (normalize next sound state) := by
  induction state using order.wf.induction with
  | h state ih =>
    rw [normalize]
    split
    next => exact hP
    next target hsome =>
      exact ih target (sound state target hsome) (step_preserves state target hsome hP)

end Descent
