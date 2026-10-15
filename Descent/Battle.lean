import Descent.Hydra
import Descent.Normalization

/-!
# A total executable Kirby–Paris battle

Hercules cuts a head attached to the root whenever there is one. Otherwise he cuts the first head
found by a left-to-right search, and its damaged parent regrows. A schedule fixes the number of new
copies at each stage; the classical Kirby–Paris schedule regrows `n` new copies at stage `n`.

`battleLength` is total for every schedule. Its termination argument is `move_wellFounded`: no
fuel, size bound, or height bound is involved, and the hydra may grow enormously before it dies.
-/

namespace Descent.Hydra

/-- Remove the first head from a list of children. -/
def chopFirst : List Hydra → Option (List Hydra)
  | [] => none
  | node [] :: rest => some rest
  | node (grandchild :: grandchildren) :: rest =>
    (chopFirst rest).map (node (grandchild :: grandchildren) :: ·)

theorem chopFirst_some {children rest : List Hydra} (h : chopFirst children = some rest) :
    ∃ left right, children = left ++ node [] :: right ∧ rest = left ++ right := by
  induction children generalizing rest with
  | nil => simp [chopFirst] at h
  | cons child children ih =>
    rcases child with ⟨_ | ⟨grandchild, grandchildren⟩⟩
    · simp only [chopFirst, Option.some.injEq] at h
      exact ⟨[], children, rfl, by simp [h]⟩
    · simp only [chopFirst, Option.map_eq_some_iff] at h
      obtain ⟨rest', hrest', rfl⟩ := h
      obtain ⟨left, right, rfl, rfl⟩ := ih hrest'
      exact ⟨node (grandchild :: grandchildren) :: left, right, rfl, rfl⟩

theorem chopFirst_eq_none {children : List Hydra} :
    chopFirst children = none ↔ node [] ∉ children := by
  induction children with
  | nil => simp [chopFirst]
  | cons child children ih =>
    rcases child with ⟨_ | ⟨grandchild, grandchildren⟩⟩
    · simp [chopFirst]
    · simp [chopFirst, ih]

/-- Try the children from left to right. A child with a head loses its first head and is replaced
by `copies + 1` damaged copies. A child without heads is searched recursively, and the search
moves past it only if that fails. -/
def regrowFirst (copies : ℕ) : List Hydra → Option (List Hydra)
  | [] => none
  | node grandchildren :: rest =>
    match chopFirst grandchildren with
    | some damaged => some (List.replicate (copies + 1) (node damaged) ++ rest)
    | none =>
      match regrowFirst copies grandchildren with
      | some grandchildren' => some (node grandchildren' :: rest)
      | none => (regrowFirst copies rest).map (node grandchildren :: ·)

theorem Regrow.cons {children children' : List Hydra} (first : Hydra)
    (move : Regrow (node children) (node children')) :
    Regrow (node (first :: children)) (node (first :: children')) := by
  cases move with
  | here regrowth left right below above => exact .here regrowth (first :: left) right below above
  | inside left right move => exact .inside (first :: left) right move

theorem regrowFirst_regrow {copies : ℕ} {children children' : List Hydra}
    (h : regrowFirst copies children = some children') :
    Regrow (node children) (node children') := by
  induction children using regrowFirst.induct (copies := copies) generalizing children' with
  | case1 => simp [regrowFirst] at h
  | case2 grandchildren rest damaged hchop =>
    simp only [regrowFirst, hchop, Option.some.injEq] at h
    subst h
    obtain ⟨below, above, rfl, rfl⟩ := chopFirst_some hchop
    simpa using Regrow.here copies [] rest below above
  | case3 grandchildren rest hchop grandchildren' hinner ih =>
    simp only [regrowFirst, hchop, hinner, Option.some.injEq] at h
    subst h
    simpa using Regrow.inside [] rest (ih hinner)
  | case4 grandchildren rest hchop hinner _ ih =>
    simp only [regrowFirst, hchop, hinner, Option.map_eq_some_iff] at h
    obtain ⟨rest', hrest', rfl⟩ := h
    exact (ih hrest').cons _

theorem regrowFirst_eq_none {copies : ℕ} {children : List Hydra} :
    regrowFirst copies children = none ↔ ∀ child ∈ children, child = node [] := by
  induction children using regrowFirst.induct (copies := copies) with
  | case1 => simp [regrowFirst]
  | case2 grandchildren rest damaged hchop =>
    simp only [regrowFirst, hchop, reduceCtorEq, false_iff, not_forall]
    refine ⟨node grandchildren, by simp, fun hdead => ?_⟩
    simp only [node.injEq] at hdead
    simp [hdead, chopFirst] at hchop
  | case3 grandchildren rest hchop grandchildren' hinner ih =>
    simp only [regrowFirst, hchop, hinner, reduceCtorEq, false_iff, not_forall]
    refine ⟨node grandchildren, by simp, fun hdead => ?_⟩
    simp only [node.injEq] at hdead
    simp [hdead, regrowFirst] at hinner
  | case4 grandchildren rest hchop hinner ihInner ih =>
    obtain rfl : grandchildren = [] := by
      have hall := ihInner.1 hinner
      cases grandchildren with
      | nil => rfl
      | cons first _ =>
        exact absurd (hall first (by simp) ▸ List.mem_cons_self) (chopFirst_eq_none.1 hchop)
    simp [regrowFirst, chopFirst, ih]

/-- One move of Hercules' strategy, with `copies` new copies if the hydra regrows. -/
def strike (copies : ℕ) : Hydra → Option Hydra
  | node children =>
    match chopFirst children with
    | some rest => some (node rest)
    | none => (regrowFirst copies children).map node

theorem strike_move {copies : ℕ} {before after : Hydra} (h : strike copies before = some after) :
    Move before after := by
  obtain ⟨children⟩ := before
  simp only [strike] at h
  split at h
  next rest hchop =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨left, right, rfl, rfl⟩ := chopFirst_some hchop
    exact .chop left right
  next hchop =>
    obtain ⟨children', hregrow, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .regrow (regrowFirst_regrow hregrow)

/-- Hercules' strategy stops exactly at the bare root, so it never gets stuck early. -/
theorem strike_eq_none {copies : ℕ} {hydra : Hydra} :
    strike copies hydra = none ↔ hydra = node [] := by
  obtain ⟨children⟩ := hydra
  simp only [strike, node.injEq]
  split
  next rest hchop =>
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    simp [chopFirst] at hchop
  next hchop =>
    rw [Option.map_eq_none_iff, regrowFirst_eq_none]
    constructor
    · intro hall
      cases children with
      | nil => rfl
      | cons first _ =>
        exact absurd (hall first (by simp) ▸ List.mem_cons_self) (chopFirst_eq_none.1 hchop)
    · rintro rfl
      simp

/-- The bare root is the only hydra without a legal move, so every battle ends there. -/
theorem terminal_iff_dead {hydra : Hydra} : (¬ ∃ after, Move hydra after) ↔ hydra = node [] := by
  constructor
  · intro h
    cases hs : strike 0 hydra with
    | none => exact strike_eq_none.1 hs
    | some after => exact absurd ⟨after, strike_move hs⟩ h
  · rintro rfl ⟨after, move⟩
    exact move_not_from_dead move

/-- A hydra is below every hydra that can move to it. -/
@[instance_reducible]
def battleOrder : WellFoundedRelation Hydra where
  rel after before := Move before after
  wf := move_wellFounded

local instance : WellFoundedRelation Hydra := battleOrder

/-- The number of moves until the hydra dies, when stage `n` regrows `schedule n` new copies. -/
def battleLength (schedule : ℕ → ℕ) (stage : ℕ) (hydra : Hydra) : ℕ :=
  match h : strike (schedule stage) hydra with
  | none => 0
  | some next => battleLength schedule (stage + 1) next + 1
termination_by hydra
decreasing_by exact strike_move h

/-- The computed length is witnessed by a legal battle that kills the hydra. -/
theorem battle_run (schedule : ℕ → ℕ) (stage : ℕ) (hydra : Hydra) :
    Run Move (battleLength schedule stage hydra) hydra (node []) := by
  induction hydra using move_wellFounded.induction generalizing stage with
  | _ hydra ih =>
    rw [battleLength]
    split
    next hnone =>
      rw [strike_eq_none.1 hnone]
      exact .done _
    next next hsome =>
      exact .next (strike_move hsome) (ih next (strike_move hsome) (stage + 1))

/-- The classical schedule: stage `n`, counted from one, regrows `n` new copies. -/
def kirbyParisLength (hydra : Hydra) : ℕ := battleLength id 1 hydra

theorem kirbyParis_run (hydra : Hydra) : Run Move (kirbyParisLength hydra) hydra (node []) :=
  battle_run id 1 hydra

/-- Battle states are ordered by their hydra alone; the stage only feeds the schedule. -/
@[instance_reducible]
def battleStateOrder : WellFoundedRelation (Hydra × ℕ) := invImage Prod.fst battleOrder

local instance : WellFoundedRelation (Hydra × ℕ) := battleStateOrder

/-- A battle state is the current hydra and the current stage. -/
def battleNext (schedule : ℕ → ℕ) : Hydra × ℕ → Option (Hydra × ℕ)
  | (hydra, stage) => (strike (schedule stage) hydra).map fun next => (next, stage + 1)

theorem battleNext_sound {schedule : ℕ → ℕ} {source target : Hydra × ℕ}
    (h : battleNext schedule source = some target) : battleStateOrder.rel target source := by
  obtain ⟨hydra, stage⟩ := source
  obtain ⟨next, hstrike, rfl⟩ := Option.map_eq_some_iff.1 h
  exact strike_move hstrike

/-- The same battle, run by the generic strategy normalizer of `Descent.Normalization`. -/
def finalState (schedule : ℕ → ℕ) (hydra : Hydra) : Hydra × ℕ :=
  normalize (battleNext schedule) (fun _ _ h => battleNext_sound h) (hydra, 1)

/-- The generic normalizer and the direct counter agree on every battle. -/
theorem normalize_battle (schedule : ℕ → ℕ) (stage : ℕ) (hydra : Hydra) :
    normalize (battleNext schedule) (fun _ _ h => battleNext_sound h) (hydra, stage) =
      (node [], stage + battleLength schedule stage hydra) := by
  induction hydra using move_wellFounded.induction generalizing stage with
  | _ hydra ih =>
    rw [normalize, battleLength]
    split
    next hnext =>
      split
      next hnone =>
        rw [strike_eq_none.1 hnone]
        rfl
      next next hsome => simp [battleNext, hsome] at hnext
    next target hnext =>
      obtain ⟨next, hstrike, rfl⟩ := Option.map_eq_some_iff.1 hnext
      rw [ih next (strike_move hstrike) (stage + 1)]
      split
      next hnone => simp [hnone] at hstrike
      next next' hsome =>
        rw [hstrike, Option.some.injEq] at hsome
        subst hsome
        simp only [Prod.mk.injEq, true_and]
        omega

theorem finalState_eq (schedule : ℕ → ℕ) (hydra : Hydra) :
    finalState schedule hydra = (node [], 1 + battleLength schedule 1 hydra) :=
  normalize_battle schedule 1 hydra

/-- Bracket notation: a node is its children's notations between parentheses. -/
def render : Hydra → String
  | node children => "(" ++ String.join (children.map render) ++ ")"

end Descent.Hydra
