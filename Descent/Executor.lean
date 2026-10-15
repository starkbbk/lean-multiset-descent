import Descent.Normalization
import Descent.Potential

/-!
# A total executable scheduler, justified by multiset descent

Lists provide a concrete executable representation of worklists. The termination
relation forgets their order and uses contextual multiset replacement. Thus the
implementation is not justified by list length, rank sum, or maximum rank.
-/

namespace Descent.Executor

@[instance_reducible]
def listDescentOrder : WellFoundedRelation (List ℕ) where
  rel target source := Replacement (target : Multiset ℕ) (source : Multiset ℕ)
  wf := InvImage.wf (fun state : List ℕ => (state : Multiset ℕ)) replacement_wellFounded

local instance : WellFoundedRelation (List ℕ) := listDescentOrder

def next (offspring : ℕ → ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | 0 :: rest => some rest
  | (rank + 1) :: rest => some (List.replicate (offspring rank) rank ++ rest)

theorem next_none_iff_empty (offspring : ℕ → ℕ) (state : List ℕ) :
    next offspring state = none ↔ state = [] := by
  cases state with
  | nil => simp [next]
  | cons rank rest => cases rank <;> simp [next]

theorem next_fixed_step {offspring : ℕ → ℕ} {source target : List ℕ}
    (h : next offspring source = some target) :
    FixedStep offspring (target : Multiset ℕ) (source : Multiset ℕ) := by
  cases source with
  | nil => simp [next] at h
  | cons rank rest =>
    cases rank with
    | zero =>
      simp only [next, Option.some.injEq] at h
      subst target
      change FixedStep offspring (rest : Multiset ℕ) (0 ::ₘ (rest : Multiset ℕ))
      rw [← Multiset.singleton_add, Multiset.add_comm]
      exact .zero _
    | succ rank =>
      simp only [next, Option.some.injEq] at h
      subst target
      rw [← Multiset.coe_add, Multiset.coe_replicate]
      change FixedStep offspring
        (Multiset.replicate (offspring rank) rank + (rest : Multiset ℕ))
        ((rank + 1) ::ₘ (rest : Multiset ℕ))
      rw [← Multiset.singleton_add, Multiset.add_comm]
      rw [Multiset.add_comm ({rank + 1} : Multiset ℕ)]
      exact .grow _ _

theorem next_descends {offspring : ℕ → ℕ} {source target : List ℕ}
    (h : next offspring source = some target) : listDescentOrder.rel target source :=
  branch_replacement (fixed_branch (next_fixed_step h))

/-- Total normalization uses the generic strategy implementation and its
multiset termination proof. No fuel limit or partial function is used. -/
def finish (offspring : ℕ → ℕ) (state : List ℕ) : List ℕ :=
  normalize (next offspring) (fun _ _ h => next_descends h) state

theorem finish_eq_empty (offspring : ℕ → ℕ) (state : List ℕ) :
    finish offspring state = [] :=
  (next_none_iff_empty offspring _).1
    (normalize_terminal (next offspring) (fun _ _ h => next_descends h) state)

theorem finish_reachable (offspring : ℕ → ℕ) (state : List ℕ) :
    Relation.ReflTransGen (StrategyStep (next offspring)) state (finish offspring state) :=
  normalize_reachable (next offspring) (fun _ _ h => next_descends h) state

/-- Count the actual scheduler transitions, independently of the cost formula. -/
def steps (offspring : ℕ → ℕ) (state : List ℕ) : ℕ :=
  match _h : next offspring state with
  | none => 0
  | some target => steps offspring target + 1
termination_by state
decreasing_by exact next_descends _h

/-- A checked execution witness connects the counter to legal multiset rewrites. -/
theorem steps_run (offspring : ℕ → ℕ) (state : List ℕ) :
    Run (fun source target => FixedStep offspring target source)
      (steps offspring state) (state : Multiset ℕ) 0 := by
  induction state using listDescentOrder.wf.induction with
  | h state ih =>
    rw [steps]
    split
    next hnone =>
      have he := (next_none_iff_empty offspring state).1 hnone
      subst state
      exact .done 0
    next target hsome =>
      exact .next (next_fixed_step hsome) (ih target (next_descends hsome))

theorem steps_exact (offspring : ℕ → ℕ) (state : List ℕ) :
    steps offspring state = potential offspring (state : Multiset ℕ) :=
  complete_run_length (steps_run offspring state)

theorem schedule_order_independent (offspring : ℕ → ℕ) {left right : List ℕ}
    (h : left.Perm right) : steps offspring left = steps offspring right := by
  rw [steps_exact, steps_exact]
  exact congrArg (potential offspring) (Multiset.coe_eq_coe.mpr h)

end Descent.Executor
