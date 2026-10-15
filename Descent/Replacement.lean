import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.WellFounded

/-!
# Contextual replacement by smaller elements

`Replacement smaller larger` replaces one element by an arbitrary finite
multiset of strictly smaller elements, retaining a common context. The number
of replacement elements is not bounded. Mathlib supplies the foundational
Dershowitz-Manna well-foundedness theorem; this module exposes a public
replacement interface for the normalization and cost developments.
-/

namespace Descent

variable {α : Type*} [Preorder α]

def Replacement (smaller larger : Multiset α) : Prop :=
  ∃ context children parent,
    smaller = context + children ∧ larger = context + {parent} ∧
      ∀ child ∈ children, child < parent

theorem replacement_intro (context children : Multiset α) (parent : α)
    (h : ∀ child ∈ children, child < parent) :
    Replacement (context + children) (context + {parent}) :=
  ⟨context, children, parent, rfl, rfl, h⟩

/-- The bridge to Mathlib's established ordering, with a singleton removed part. -/
theorem replacement_dm {smaller larger : Multiset α}
    (h : Replacement smaller larger) : Multiset.IsDershowitzMannaLT smaller larger := by
  rcases h with ⟨context, children, parent, rfl, rfl, hchildren⟩
  refine ⟨context, children, {parent}, by simp, rfl, rfl, ?_⟩
  intro child hc
  exact ⟨parent, by simp, hchildren child hc⟩

theorem replacement_add_context {smaller larger : Multiset α}
    (h : Replacement smaller larger) (extra : Multiset α) :
    Replacement (extra + smaller) (extra + larger) := by
  rcases h with ⟨context, children, parent, rfl, rfl, hchildren⟩
  exact ⟨extra + context, children, parent, by simp [add_assoc],
    by simp [add_assoc], hchildren⟩

theorem replacement_delete (context : Multiset α) (parent : α) :
    Replacement context (context + {parent}) := by
  simpa using replacement_intro context 0 parent (by simp)

/-- Arbitrary finite offspring is permitted; no cardinality or sum bound is assumed. -/
theorem replacement_wellFounded [WellFoundedLT α] :
    WellFounded (Replacement : Multiset α → Multiset α → Prop) :=
  Multiset.wellFounded_isDershowitzMannaLT.mono fun _ _ h => replacement_dm h

theorem replacement_irrefl [WellFoundedLT α] (state : Multiset α) :
    ¬ Replacement state state :=
  replacement_wellFounded.irrefl.irrefl state

theorem replacement_no_cycle [WellFoundedLT α] (state : Multiset α) :
    ¬ Relation.TransGen Replacement state state :=
  replacement_wellFounded.transGen.irrefl.irrefl state

end Descent
