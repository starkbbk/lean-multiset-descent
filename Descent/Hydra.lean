import Descent.Ordering
import Descent.Runs

/-!
# Kirby–Paris hydra battles terminate

A hydra is a finite rooted tree; its heads are the nodes without children. Hercules cuts one
head per move. A head attached to the root simply disappears. Otherwise the damaged parent,
with that head removed, is replaced by `regrowth + 1` copies of itself under the grandparent,
where the hydra may choose `regrowth` freely at every move.

Node count can grow and height need not drop, so neither is a termination measure. The measure
used here maps a hydra of height at most `d` into `Nested d`, the multisets nested to depth `d`,
so the proof applies Mathlib's Dershowitz–Manna theorem once per level. Kirby and Paris (1982)
proved that termination of this game, already for the schedule regrowing `n` copies at stage `n`,
cannot be proved in Peano arithmetic.
-/

namespace Descent

/-- A finite rooted tree. A *head* is a node without children. -/
inductive Hydra where
  | node : List Hydra → Hydra

namespace Hydra

mutual
/-- The number of edges on a longest path from the root to a head. -/
def height : Hydra → ℕ
  | node children => heightList children

/-- The largest value of `child.height + 1`, or zero when there are no children. -/
def heightList : List Hydra → ℕ
  | [] => 0
  | child :: rest => max (height child + 1) (heightList rest)
end

mutual
/-- The number of nodes, including the root. -/
def size : Hydra → ℕ
  | node children => sizeList children + 1

/-- The total number of nodes in a list of subtrees. -/
def sizeList : List Hydra → ℕ
  | [] => 0
  | child :: rest => size child + sizeList rest
end

/-- A regrowing move whose cut head has the current node, or a node below it, as grandparent.
The damaged parent `node (below ++ above)` regrows into `regrowth + 1` copies. -/
inductive Regrow : Hydra → Hydra → Prop
  | here (regrowth : ℕ) (left right below above : List Hydra) :
      Regrow (node (left ++ node (below ++ node [] :: above) :: right))
        (node (left ++ List.replicate (regrowth + 1) (node (below ++ above)) ++ right))
  | inside (left right : List Hydra) {child child' : Hydra} :
      Regrow child child' → Regrow (node (left ++ child :: right)) (node (left ++ child' :: right))

/-- One move of a battle, oriented chronologically from `before` to `after`. -/
inductive Move : Hydra → Hydra → Prop
  | chop (left right : List Hydra) : Move (node (left ++ node [] :: right)) (node (left ++ right))
  | regrow {before after : Hydra} : Regrow before after → Move before after

theorem heightList_le_iff {children : List Hydra} {bound : ℕ} :
    heightList children ≤ bound ↔ ∀ child ∈ children, child.height + 1 ≤ bound := by
  induction children with
  | nil => simp [heightList]
  | cons child rest ih => simp [heightList, ih]

theorem height_le_iff {children : List Hydra} {bound : ℕ} :
    (node children).height ≤ bound ↔ ∀ child ∈ children, child.height + 1 ≤ bound := by
  rw [height]
  exact heightList_le_iff

theorem height_lt_of_mem {children : List Hydra} {child : Hydra} (h : child ∈ children) :
    child.height < (node children).height :=
  height_le_iff.1 le_rfl child h

theorem height_le_of_subset {children children' : List Hydra}
    (h : ∀ child ∈ children', child ∈ children) :
    (node children').height ≤ (node children).height :=
  height_le_iff.2 fun child hchild => height_lt_of_mem (h child hchild)

theorem Regrow.height_le {before after : Hydra} (move : Regrow before after) :
    after.height ≤ before.height := by
  induction move with
  | here regrowth left right below above =>
    refine height_le_iff.2 fun child hchild => ?_
    simp only [List.mem_append, List.mem_replicate] at hchild
    rcases hchild with (hleft | ⟨-, rfl⟩) | hright
    · exact height_lt_of_mem (by simp [hleft])
    · calc (node (below ++ above)).height + 1
          ≤ (node (below ++ node [] :: above)).height + 1 := by
            refine Nat.add_le_add_right (height_le_of_subset fun child hchild => ?_) 1
            simp only [List.mem_append, List.mem_cons] at hchild ⊢
            tauto
        _ ≤ _ := height_lt_of_mem (by simp)
    · exact height_lt_of_mem (by simp [hright])
  | inside left right move ih =>
    refine height_le_iff.2 fun child hchild => ?_
    simp only [List.mem_append, List.mem_cons] at hchild
    rcases hchild with hleft | rfl | hright
    · exact height_lt_of_mem (by simp [hleft])
    · exact lt_of_le_of_lt ih (height_lt_of_mem (by simp))
    · exact height_lt_of_mem (by simp [hright])

/-- Hydras may grow wider without limit, but never taller. -/
theorem Move.height_le {before after : Hydra} (move : Move before after) :
    after.height ≤ before.height := by
  cases move with
  | chop left right =>
    exact height_le_of_subset fun child hchild => by
      simp only [List.mem_append, List.mem_cons] at hchild ⊢
      tauto
  | regrow move => exact move.height_le

/-- Read a hydra as a multiset nested to depth `d`. Structure below depth `d` is truncated, so
the results below assume that the hydra's height is at most `d`. -/
def measure : (d : ℕ) → Hydra → Nested d
  | 0, _ => PUnit.unit
  | d + 1, node children => Nested.ofMultiset (children.map (measure d))

/-- Replacing one child by finitely many children of smaller measure is a single
`Replacement` one level up. -/
theorem measure_replace {d : ℕ} (left right replacement : List Hydra) (old : Hydra)
    (smaller : ∀ new ∈ replacement, measure d new < measure d old) :
    measure (d + 1) (node (left ++ replacement ++ right)) <
      measure (d + 1) (node (left ++ old :: right)) := by
  simp only [measure]
  rw [Nested.ofMultiset_lt_ofMultiset]
  have step := replacement_dm (replacement_intro ((left ++ right).map (measure d) : Multiset _)
    (replacement.map (measure d) : Multiset _) (measure d old) (by simpa using smaller))
  convert step using 1
  · simp only [List.map_append, ← Multiset.coe_add]
    exact add_right_comm _ _ _
  · simp only [List.map_append, List.map_cons, ← Multiset.coe_add, ← Multiset.cons_coe,
      ← Multiset.singleton_add]
    rw [add_comm {measure d old}, add_assoc]

theorem Regrow.measure_lt {before after : Hydra} (move : Regrow before after) :
    ∀ d, before.height ≤ d → measure d after < measure d before := by
  induction move with
  | here regrowth left right below above =>
    intro d hd
    have hparent := height_lt_of_mem (children := left ++ node (below ++ node [] :: above) :: right)
      (child := node (below ++ node [] :: above)) (by simp)
    have hhead := height_lt_of_mem (children := below ++ node [] :: above)
      (child := node []) (by simp)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 + 1 := ⟨d - 2, by omega⟩
    refine measure_replace left right _ _ fun new hnew => ?_
    rw [List.eq_of_mem_replicate hnew]
    simpa using measure_replace (d := e) below above [] (node []) (by simp)
  | @inside left right child child' move ih =>
    intro d hd
    have hchild := height_lt_of_mem (children := left ++ child :: right) (child := child)
      (by simp)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simpa using measure_replace left right [child'] child (by simpa using ih e (by omega))

/-- At any depth bounding the current height, every move strictly lowers the nested measure. -/
theorem Move.measure_lt {before after : Hydra} (move : Move before after) {d : ℕ}
    (hd : before.height ≤ d) : measure d after < measure d before := by
  cases move with
  | chop left right =>
    have hhead := height_lt_of_mem (children := left ++ node [] :: right) (child := node [])
      (by simp)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simpa using measure_replace left right [] (node []) (by simp)
  | regrow move => exact move.measure_lt d hd

/-- Kirby–Paris: every battle ends, whichever heads Hercules cuts and however many copies
regrow at each move. -/
theorem move_wellFounded : WellFounded (fun after before : Hydra => Move before after) := by
  suffices h : ∀ (d : ℕ) (level : Nested d) (hydra : Hydra), measure d hydra = level →
      hydra.height ≤ d → Acc (fun after before : Hydra => Move before after) hydra from
    ⟨fun hydra => h _ _ hydra rfl le_rfl⟩
  intro d level
  induction level using WellFoundedLT.induction with
  | _ level ih =>
    rintro hydra rfl hheight
    exact ⟨_, fun next move => ih _ (move.measure_lt hheight) next rfl
      (move.height_le.trans hheight)⟩

theorem no_infinite_battle :
    ¬ ∃ battle : ℕ → Hydra, ∀ n, Move (battle n) (battle (n + 1)) := by
  rintro ⟨battle, moves⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp move_wellFounded).false ⟨battle, moves⟩

/-- No move leaves the bare root. -/
theorem move_not_from_dead {after : Hydra} : ¬ Move (node []) after := by
  intro move
  have hd := move.measure_lt (d := 1) (by simp [height, heightList])
  have hz : measure 1 (node []) = Nested.ofMultiset 0 := rfl
  rw [hz] at hd
  obtain ⟨X, Y, Z, hZ, -, hN, -⟩ := Nested.ofMultiset_lt_ofMultiset.1 hd
  exact hZ (by simpa [Multiset.empty_eq_zero] using (add_eq_zero.1 hN.symm).2)

/-- The root with one neck and one head. -/
def neck : Hydra := node [node [node []]]

theorem chop_all_heads (count : ℕ) :
    Run Move count (node (List.replicate count (node []))) (node []) := by
  induction count with
  | zero => exact .done _
  | succ count ih =>
    exact .next (by simpa [List.replicate_succ] using Move.chop [] (List.replicate count (node [])))
      ih

/-- Termination gives no uniform bound: one fixed hydra has arbitrarily long complete battles,
because the regrowth at its first move is unrestricted. -/
theorem arbitrarily_long_battles (budget : ℕ) :
    ∃ length, budget < length ∧ Run Move length neck (node []) := by
  refine ⟨budget + 2, by omega, .next ?_ (chop_all_heads (budget + 1))⟩
  simpa [neck] using Move.regrow (Regrow.here budget [] [] [] [])

/-- No natural-number measure decreases along every move, since battles from `neck` alone have
unbounded length. -/
theorem no_nat_measure :
    ¬ ∃ μ : Hydra → ℕ, ∀ before after, Move before after → μ after < μ before := by
  rintro ⟨μ, hμ⟩
  have bound : ∀ {length : ℕ} {source target : Hydra}, Run Move length source target →
      length + μ target ≤ μ source := by
    intro length source target run
    induction run with
    | done => simp
    | next step _ ih =>
      have := hμ _ _ step
      omega
  obtain ⟨length, hlong, run⟩ := arbitrarily_long_battles (μ neck)
  have := bound run
  omega

/-- Node count can grow during a battle. -/
theorem size_can_increase :
    Move neck (node [node [], node [], node []]) ∧
      neck.size < (node [node [], node [], node []]).size := by
  refine ⟨by simpa [neck] using Move.regrow (Regrow.here 2 [] [] [] []), ?_⟩
  decide

/-- Height need not drop: the second neck keeps the hydra at height two. -/
theorem height_need_not_drop :
    Move (node [node [node []], node [node []]]) (node [node [], node [node []]]) ∧
      (node [node [], node [node []]]).height = (node [node [node []], node [node []]]).height := by
  refine ⟨by simpa using Move.regrow (Regrow.here 0 [] [node [node []]] [] []), ?_⟩
  decide

end Hydra

end Descent
