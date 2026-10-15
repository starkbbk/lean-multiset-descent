import Descent.Hydra
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

/-!
# Goodstein's theorem

Write `n` in hereditary base `b + 2`: `n = q * (b + 2) ^ e + r` with leading exponent
`e = log (b + 2) n`, leading digit `q < b + 2`, and `r < (b + 2) ^ e`, where `e` and `r` are
written the same way. Goodstein's sequence rewrites the notation in the next base and subtracts
one, at every stage. It reaches zero from every start (Goodstein, 1944), yet Kirby and Paris
(1982) proved that this cannot be shown in Peano arithmetic.

Hereditary notation is a `Hydra`: a number is the tree whose children are the notations of its
exponents, one child per unit of each digit. Rewriting in the next base leaves the tree unchanged
(`rep_bump`). Hereditary notation is strictly monotone into the nested multisets of
`Descent.Ordering` (`measure_rep_lt`), so subtracting one lowers the same nested-multiset measure
that ends hydra battles, and the whole proof again rests on Mathlib's Dershowitz–Manna theorem.
-/

namespace Descent.Goodstein

open Hydra

mutual
/-- The number a tree denotes in base `base`: each child `c` contributes `base ^ value base c`. -/
def value (base : ℕ) : Hydra → ℕ
  | .node children => valueList base children

/-- The sum of `base ^ value base c` over a list of children. -/
def valueList (base : ℕ) : List Hydra → ℕ
  | [] => 0
  | child :: rest => base ^ value base child + valueList base rest
end

theorem value_node (base : ℕ) (children : List Hydra) :
    value base (.node children) = valueList base children := by
  rw [value]

theorem valueList_append (base : ℕ) (left right : List Hydra) :
    valueList base (left ++ right) = valueList base left + valueList base right := by
  induction left with
  | nil => simp [valueList]
  | cons child rest ih => simp [valueList, ih, Nat.add_assoc]

theorem valueList_replicate (base count : ℕ) (child : Hydra) :
    valueList base (List.replicate count child) = count * base ^ value base child := by
  induction count with
  | zero => simp [valueList]
  | succ count ih => rw [List.replicate_succ, valueList, ih, Nat.succ_mul, Nat.add_comm]

/-- The leading exponent of `n` in base `b + 2`. -/
def exponent (b n : ℕ) : ℕ := Nat.log (b + 2) n

/-- The leading digit of `n` in base `b + 2`. -/
def digit (b n : ℕ) : ℕ := n / (b + 2) ^ exponent b n

/-- What remains of `n` after its leading term in base `b + 2`. -/
def remainder (b n : ℕ) : ℕ := n % (b + 2) ^ exponent b n

theorem pow_exponent_pos (b n : ℕ) : 0 < (b + 2) ^ exponent b n := Nat.pow_pos (by omega)

theorem pow_exponent_le {b n : ℕ} (hn : n ≠ 0) : (b + 2) ^ exponent b n ≤ n :=
  Nat.pow_log_le_self _ hn

theorem exponent_lt {b n : ℕ} (hn : n ≠ 0) : exponent b n < n := Nat.log_lt_self _ hn

theorem remainder_lt_pow (b n : ℕ) : remainder b n < (b + 2) ^ exponent b n :=
  Nat.mod_lt _ (pow_exponent_pos b n)

theorem remainder_lt {b n : ℕ} (hn : n ≠ 0) : remainder b n < n :=
  (remainder_lt_pow b n).trans_le (pow_exponent_le hn)

theorem digit_pos {b n : ℕ} (hn : n ≠ 0) : 0 < digit b n :=
  Nat.div_pos (pow_exponent_le hn) (pow_exponent_pos b n)

/-- Leading digits are genuine base-`b + 2` digits. -/
theorem digit_lt (b n : ℕ) : digit b n < b + 2 := by
  apply Nat.div_lt_of_lt_mul
  rw [← pow_succ]
  exact Nat.lt_pow_succ_log_self (by omega) n

theorem pow_mul_digit_add_remainder (b n : ℕ) :
    (b + 2) ^ exponent b n * digit b n + remainder b n = n :=
  Nat.div_add_mod n _

/-- The children of `n` in hereditary base `b + 2`: the notation of each exponent, repeated as
often as its digit, leading term first. -/
def terms (b n : ℕ) : List Hydra :=
  if h : n = 0 then [] else
    List.replicate (digit b n) (.node (terms b (exponent b n))) ++ terms b (remainder b n)
termination_by n
decreasing_by
  · exact exponent_lt h
  · exact remainder_lt h

/-- Hereditary base-`b + 2` notation, as the tree of exponent notations. -/
def rep (b n : ℕ) : Hydra := .node (terms b n)

theorem terms_zero (b : ℕ) : terms b 0 = [] := by
  rw [terms, dif_pos rfl]

theorem terms_of_ne_zero (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    terms b n = List.replicate (digit b n) (rep b (exponent b n)) ++ terms b (remainder b n) := by
  rw [terms, dif_neg hn]
  rfl

theorem rep_zero (b : ℕ) : rep b 0 = .node [] := by
  rw [rep, terms_zero]

/-- The notation denotes the number it was built from. -/
theorem value_rep (b n : ℕ) : value (b + 2) (rep b n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [rep_zero, value_node, valueList]
    · rw [rep, value_node, terms_of_ne_zero b hn, valueList_append, valueList_replicate,
        ih _ (exponent_lt hn), ← value_node, ← rep, ih _ (remainder_lt hn), Nat.mul_comm]
      exact pow_mul_digit_add_remainder b n

theorem rep_exponent_mem {b n : ℕ} (hn : n ≠ 0) : rep b (exponent b n) ∈ terms b n := by
  rw [terms_of_ne_zero b hn]
  exact List.mem_append_left _ (List.mem_replicate.2 ⟨(digit_pos hn).ne', rfl⟩)

theorem mem_terms {b n : ℕ} {child : Hydra} (h : child ∈ terms b n) :
    ∃ j, child = rep b j ∧ (b + 2) ^ j ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp [terms_zero] at h
    · rw [terms_of_ne_zero b hn, List.mem_append] at h
      rcases h with h | h
      · exact ⟨exponent b n, List.eq_of_mem_replicate h, pow_exponent_le hn⟩
      · obtain ⟨j, rfl, hj⟩ := ih _ (remainder_lt hn) h
        exact ⟨j, rfl, hj.trans (Nat.mod_le _ _)⟩

theorem le_exponent_of_pow_le {b n j : ℕ} (h : (b + 2) ^ j ≤ n) : j ≤ exponent b n :=
  Nat.le_log_of_pow_le (by omega) h

/-- Read the hereditary base-`b + 2` notation of `n` in base `b + 3`. -/
def bump (b n : ℕ) : ℕ := value (b + 1 + 2) (rep b n)

theorem bump_zero (b : ℕ) : bump b 0 = 0 := by
  rw [bump, rep_zero, value_node, valueList]

theorem bump_of_ne_zero (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    bump b n = digit b n * (b + 1 + 2) ^ bump b (exponent b n) + bump b (remainder b n) := by
  rw [bump, rep, value_node, terms_of_ne_zero b hn, valueList_append, valueList_replicate,
    ← value_node, ← rep]
  rfl

theorem bump_pow (b e : ℕ) : bump b ((b + 2) ^ e) = (b + 1 + 2) ^ bump b e := by
  have hpos : 0 < (b + 2) ^ e := Nat.pow_pos (by omega)
  have hexp : exponent b ((b + 2) ^ e) = e := Nat.log_pow (by omega) e
  have hdigit : digit b ((b + 2) ^ e) = 1 := by rw [digit, hexp, Nat.div_self hpos]
  have hrem : remainder b ((b + 2) ^ e) = 0 := by rw [remainder, hexp, Nat.mod_self]
  rw [bump_of_ne_zero b hpos.ne', hdigit, hrem, hexp, bump_zero, Nat.one_mul, Nat.add_zero]

/-- Changing the base preserves the order of numbers. -/
theorem bump_lt_bump (b : ℕ) {x y : ℕ} (hxy : x < y) : bump b x < bump b y := by
  induction y using Nat.strong_induction_on generalizing x with
  | _ y ih =>
    have hy : y ≠ 0 := by omega
    have hdy := digit_pos (b := b) hy
    have hKy : 0 < (b + 1 + 2) ^ bump b (exponent b y) := Nat.pow_pos (by omega)
    rw [bump_of_ne_zero b hy]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [bump_zero]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos hdy hKy) (Nat.le_add_right _ _)
    have hremx : bump b (remainder b x) < (b + 1 + 2) ^ bump b (exponent b x) := by
      rw [← bump_pow]
      exact ih _ ((pow_exponent_le hx).trans_lt hxy) (remainder_lt_pow b x)
    have hdx := digit_lt b x
    rw [bump_of_ne_zero b hx]
    have hlead : digit b x * (b + 1 + 2) ^ bump b (exponent b x) + bump b (remainder b x) <
        (digit b x + 1) * (b + 1 + 2) ^ bump b (exponent b x) := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left hremx _
    have hexp : exponent b x ≤ exponent b y := Nat.log_mono_right hxy.le
    rcases hexp.lt_or_eq with hlt | heq
    · have hbe : bump b (exponent b x) < bump b (exponent b y) := ih _ (exponent_lt hy) hlt
      calc _ < (digit b x + 1) * (b + 1 + 2) ^ bump b (exponent b x) := hlead
        _ ≤ (b + 1 + 2) * (b + 1 + 2) ^ bump b (exponent b x) := Nat.mul_le_mul_right _ (by omega)
        _ = (b + 1 + 2) ^ (bump b (exponent b x) + 1) := by rw [pow_succ, Nat.mul_comm]
        _ ≤ (b + 1 + 2) ^ bump b (exponent b y) := Nat.pow_le_pow_right (by omega) hbe
        _ ≤ digit b y * (b + 1 + 2) ^ bump b (exponent b y) := Nat.le_mul_of_pos_left _ hdy
        _ ≤ _ := Nat.le_add_right _ _
    · have hdxy : digit b x ≤ digit b y := by
        rw [digit, digit, heq]
        exact Nat.div_le_div_right hxy.le
      rcases hdxy.lt_or_eq with hdlt | hdeq
      · rw [heq] at hlead ⊢
        calc _ < (digit b x + 1) * (b + 1 + 2) ^ bump b (exponent b y) := hlead
          _ ≤ digit b y * (b + 1 + 2) ^ bump b (exponent b y) := Nat.mul_le_mul_right _ hdlt
          _ ≤ _ := Nat.le_add_right _ _
      · have hx' := pow_mul_digit_add_remainder b x
        have hy' := pow_mul_digit_add_remainder b y
        rw [heq, hdeq] at hx'
        generalize (b + 2) ^ exponent b y * digit b y = T at hx' hy'
        have hrem : remainder b x < remainder b y := by omega
        rw [heq, hdeq]
        exact Nat.add_lt_add_left (ih _ (remainder_lt hy) hrem) _

theorem bump_lt_pow {b x e : ℕ} (h : x < (b + 2) ^ e) : bump b x < (b + 1 + 2) ^ bump b e := by
  rw [← bump_pow]
  exact bump_lt_bump b h

theorem bump_pos {b n : ℕ} (hn : n ≠ 0) : 0 < bump b n := by
  rw [← bump_zero b]
  exact bump_lt_bump b (Nat.pos_of_ne_zero hn)

/-- Rewriting in the next base does not change the notation: the bumped number's hereditary
base-`b + 3` notation is the same tree. -/
theorem rep_bump (b n : ℕ) : rep (b + 1) (bump b n) = rep b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [bump_zero, rep_zero, rep_zero]
    have hK : 0 < (b + 1 + 2) ^ bump b (exponent b n) := Nat.pow_pos (by omega)
    have hR : bump b (remainder b n) < (b + 1 + 2) ^ bump b (exponent b n) :=
      bump_lt_pow (remainder_lt_pow b n)
    have hd := digit_pos (b := b) hn
    have hdl := digit_lt b n
    have hm := bump_of_ne_zero b hn
    have hm0 : bump b n ≠ 0 := (bump_pos hn).ne'
    have hexp : exponent (b + 1) (bump b n) = bump b (exponent b n) := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · rw [hm]
        exact (Nat.le_mul_of_pos_left _ hd).trans (Nat.le_add_right _ _)
      · rw [hm, pow_succ]
        calc _ < (digit b n + 1) * (b + 1 + 2) ^ bump b (exponent b n) := by
              rw [Nat.succ_mul]
              exact Nat.add_lt_add_left hR _
          _ ≤ (b + 1 + 2) * (b + 1 + 2) ^ bump b (exponent b n) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = _ := Nat.mul_comm _ _
    have hdigit : digit (b + 1) (bump b n) = digit b n := by
      rw [digit, hexp, hm, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hK,
        Nat.div_eq_of_lt hR, Nat.zero_add]
    have hrem : remainder (b + 1) (bump b n) = bump b (remainder b n) := by
      rw [remainder, hexp, hm, Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hR]
    have hrest := ih _ (remainder_lt (b := b) hn)
    rw [rep, rep, Hydra.node.injEq] at hrest
    rw [rep, rep, terms_of_ne_zero (b + 1) hm0, terms_of_ne_zero b hn, hexp, hdigit, hrem,
      ih _ (exponent_lt (b := b) hn), hrest]

/-- Larger numbers have notations at least as tall. -/
theorem height_rep_mono {b x y : ℕ} (hxy : x ≤ y) : (rep b x).height ≤ (rep b y).height := by
  induction y using Nat.strong_induction_on generalizing x with
  | _ y ih =>
    rcases eq_or_ne x 0 with rfl | hx
    · rw [rep_zero]
      exact Nat.zero_le _
    have hy : y ≠ 0 := by omega
    have hupper : (rep b x).height ≤ (rep b (exponent b x)).height + 1 := by
      rw [rep, height_le_iff]
      intro child hchild
      obtain ⟨j, rfl, hj⟩ := mem_terms hchild
      exact Nat.add_le_add_right
        (ih _ ((exponent_lt hx).trans_le hxy) (le_exponent_of_pow_le hj)) 1
    have hmono : (rep b (exponent b x)).height ≤ (rep b (exponent b y)).height :=
      ih _ (exponent_lt hy) (Nat.log_mono_right hxy)
    have hlower : (rep b (exponent b y)).height < (rep b y).height :=
      height_lt_of_mem (rep_exponent_mem hy)
    omega

/-- Hereditary notation is strictly monotone into nested multisets: a smaller number has a
smaller notation in the iterated Dershowitz–Manna order. Only the larger notation needs to fit
within depth `d`. -/
theorem measure_rep_lt {b x y d : ℕ} (hxy : x < y) (hd : (rep b y).height ≤ d) :
    measure d (rep b x) < measure d (rep b y) := by
  induction y using Nat.strong_induction_on generalizing x d with
  | _ y ih =>
    have hy : y ≠ 0 := by omega
    have hchild : (rep b (exponent b y)).height < (rep b y).height :=
      height_lt_of_mem (rep_exponent_mem hy)
    obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have below : ∀ j < exponent b y, measure d (rep b j) < measure d (rep b (exponent b y)) :=
      fun j hj => ih _ (exponent_lt hy) hj (by omega)
    have hleadY : measure d (rep b (exponent b y)) ∈
        (((terms b y).map (measure d) : List (Nested d)) : Multiset (Nested d)) :=
      Multiset.mem_coe.2 (List.mem_map_of_mem (rep_exponent_mem hy))
    have hNne : (((terms b y).map (measure d) : List (Nested d)) : Multiset (Nested d)) ≠ ∅ := by
      intro h0
      rw [h0] at hleadY
      simp at hleadY
    have hsplit : ∀ m : ℕ, m ≠ 0 →
        (((terms b m).map (measure d) : List (Nested d)) : Multiset (Nested d)) =
          Multiset.replicate (digit b m) (measure d (rep b (exponent b m))) +
            ((terms b (remainder b m)).map (measure d) : Multiset (Nested d)) := by
      intro m hm
      rw [terms_of_ne_zero b hm, List.map_append, List.map_replicate, ← Multiset.coe_add,
        Multiset.coe_replicate]
    show Nested.ofMultiset _ < Nested.ofMultiset _
    rw [Nested.ofMultiset_lt_ofMultiset]
    rcases eq_or_ne x 0 with rfl | hx
    · refine ⟨0, 0, _, hNne, by simp [terms_zero], (zero_add _).symm, by simp⟩
    have hexp : exponent b x ≤ exponent b y := Nat.log_mono_right hxy.le
    rcases hexp.lt_or_eq with hlt | heq
    · -- A smaller leading exponent: every child of `x` lies below the leading child of `y`.
      refine ⟨0, _, _, hNne, (zero_add _).symm, (zero_add _).symm, fun t ht => ?_⟩
      obtain ⟨child, hmem, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ht)
      obtain ⟨j, rfl, hj⟩ := mem_terms hmem
      exact ⟨_, hleadY, below j ((le_exponent_of_pow_le hj).trans_lt hlt)⟩
    have hdxy : digit b x ≤ digit b y := by
      rw [digit, digit, heq]
      exact Nat.div_le_div_right hxy.le
    rw [hsplit x hx, hsplit y hy, heq]
    have hsmall : ∀ t ∈ (((terms b (remainder b x)).map (measure d) : List (Nested d)) :
        Multiset (Nested d)), t < measure d (rep b (exponent b y)) := by
      intro t ht
      obtain ⟨child, hmem, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ht)
      obtain ⟨j, rfl, hj⟩ := mem_terms hmem
      refine below j ?_
      rw [← heq]
      exact (Nat.pow_lt_pow_iff_right (by omega)).1 (hj.trans_lt (remainder_lt_pow b x))
    rcases hdxy.lt_or_eq with hdlt | hdeq
    · -- A smaller leading digit: one more leading child in `y` dominates the rest of `x`.
      refine ⟨Multiset.replicate (digit b x) (measure d (rep b (exponent b y))), _,
        Multiset.replicate (digit b y - digit b x) (measure d (rep b (exponent b y))) +
          ((terms b (remainder b y)).map (measure d) : Multiset (Nested d)), ?_, rfl, ?_,
        fun t ht => ⟨_, ?_, hsmall t ht⟩⟩
      · intro h0
        have hmem : measure d (rep b (exponent b y)) ∈
            Multiset.replicate (digit b y - digit b x) (measure d (rep b (exponent b y))) +
              ((terms b (remainder b y)).map (measure d) : Multiset (Nested d)) :=
          Multiset.mem_add.2 (.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩))
        rw [h0] at hmem
        simp at hmem
      · rw [← add_assoc, ← Multiset.replicate_add, Nat.add_sub_cancel' hdlt.le]
      · exact Multiset.mem_add.2 (.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩))
    · -- Equal leading terms: compare the remainders one level down, by induction.
      have hx' := pow_mul_digit_add_remainder b x
      have hy' := pow_mul_digit_add_remainder b y
      rw [heq, hdeq] at hx'
      generalize (b + 2) ^ exponent b y * digit b y = T at hx' hy'
      have hrem : remainder b x < remainder b y := by omega
      have hrestY : (rep b (remainder b y)).height ≤ d + 1 :=
        (height_le_of_subset fun child h => by
          rw [terms_of_ne_zero b hy]
          exact List.mem_append_right _ h).trans hd
      have hlow := ih _ (remainder_lt hy) hrem hrestY
      rw [hdeq]
      exact dm_add_left (Nested.ofMultiset_lt_ofMultiset.1 hlow) _

/-- Goodstein's sequence from `n`: stage `k` writes the current value in hereditary base `k + 2`,
rewrites it in base `k + 3`, and subtracts one. -/
def goodstein (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => bump k (goodstein n k) - 1

/-- Goodstein's theorem: every Goodstein sequence reaches zero. The nested-multiset measure of
the current notation strictly decreases at every stage, at a depth fixed by the starting value. -/
theorem goodstein_terminates (n : ℕ) : ∃ k, goodstein n k = 0 := by
  by_contra! hne
  have hheight : ∀ k, (rep k (goodstein n k)).height ≤ (rep 0 n).height := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      calc (rep (k + 1) (goodstein n (k + 1))).height
          ≤ (rep (k + 1) (bump k (goodstein n k))).height := height_rep_mono (Nat.sub_le _ _)
        _ = (rep k (goodstein n k)).height := by rw [rep_bump]
        _ ≤ _ := ih
  have hdesc : ∀ k, measure (rep 0 n).height (rep (k + 1) (goodstein n (k + 1))) <
      measure (rep 0 n).height (rep k (goodstein n k)) := by
    intro k
    rw [← rep_bump k (goodstein n k)]
    exact measure_rep_lt (Nat.sub_lt (bump_pos (hne k)) Nat.one_pos)
      (by rw [rep_bump]; exact hheight k)
  exact (wellFounded_iff_isEmpty_descending_chain.mp (nested_wellFounded _)).false
    ⟨fun k => measure (rep 0 n).height (rep k (goodstein n k)), hdesc⟩

theorem goodstein_succ_eq_zero {n k : ℕ} (h : goodstein n k = 0) : goodstein n (k + 1) = 0 := by
  show bump k (goodstein n k) - 1 = 0
  rw [h, bump_zero]

/-- The stage at which Goodstein's sequence from `n` first reaches zero. The search is total
because of `goodstein_terminates`. -/
def goodsteinLength (n : ℕ) : ℕ := Nat.find (goodstein_terminates n)

theorem goodstein_goodsteinLength (n : ℕ) : goodstein n (goodsteinLength n) = 0 :=
  Nat.find_spec (goodstein_terminates n)

theorem goodstein_ne_zero_of_lt {n k : ℕ} (h : k < goodsteinLength n) : goodstein n k ≠ 0 :=
  Nat.find_min (goodstein_terminates n) h

/-- Once the sequence reaches zero, it stays there. -/
theorem goodstein_eq_zero_of_le {n k : ℕ} (h : goodsteinLength n ≤ k) : goodstein n k = 0 := by
  induction k, h using Nat.le_induction with
  | base => exact goodstein_goodsteinLength n
  | succ k _ ih => exact goodstein_succ_eq_zero ih

end Descent.Goodstein
