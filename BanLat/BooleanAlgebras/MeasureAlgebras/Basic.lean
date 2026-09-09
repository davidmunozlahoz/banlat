/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.SigmaComplete
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Measure algebras

This file introduces **measure algebras `(B, μ)`**, where `B` is a `σ`-order complete
Boolean algebra and `μ : B → [0, ∞]` is a function, satisfying that:
* `μ(a) = 0 ↔ a = ⊥`
* `μ(⊤) < ∞`.
* `μ(∨ a i) = ∑ μ(a i)` for every pairwise disjoint sequence `a i` in `B`.
It also introduces **equivalence of measure algebras** as order isomorphism that preserve
the measure.
-/

open Function
open scoped ENNReal

universe u v

/-- A measure algebra on `B` is a finite and countably additive measure on a σ-complete
Boolean algebra that vanishes only at the bottom element. -/
structure MeasureAlgebra (B : Type u) [SigmaCompleteBooleanAlgebra B] where
  /-- The measure of an element of the Boolean algebra. -/
  toFun : B → ℝ≥0∞
  /-- The measure vanishes exactly at the bottom element. -/
  measure_eq_zero_iff (a : B) : toFun a = 0 ↔ a = ⊥
  /-- The total measure is finite. -/
  m_top_ne_top : toFun ⊤ ≠ ∞
  /-- The measure is countably additive on pairwise disjoint sequences. -/
  m_iSup ⦃a : ℕ → B⦄ : Pairwise (Disjoint on a) →
    toFun (⨆ i, a i) = ∑' i, toFun (a i)

instance {B : Type u} [SigmaCompleteBooleanAlgebra B] :
    CoeFun (MeasureAlgebra B) (fun _ ↦ B → ℝ≥0∞) :=
  ⟨MeasureAlgebra.toFun⟩

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-- The bottom element has measure zero. -/
@[simp]
theorem measure_bot : μ ⊥ = 0 := by
  exact (μ.measure_eq_zero_iff ⊥).2 rfl

/-- The measure is countably additive on pairwise disjoint sequences. -/
theorem measure_iSup {a : ℕ → B} (ha : Pairwise (Disjoint on a)) :
    μ (⨆ i, a i) = ∑' i, μ (a i) := by
  exact μ.m_iSup ha

/-- The measure is additive on disjoint elements. -/
theorem measure_sup {a b : B} (h : Disjoint a b) :
    μ (a ⊔ b) = μ a + μ b := by
  let c : ℕ → B := fun n ↦ if n = 0 then a else if n = 1 then b else ⊥
  have hc : Pairwise (Disjoint on c) := by
    rintro i j hij
    change Disjoint (c i) (c j)
    simp only [c]
    split_ifs
    all_goals first | omega | exact h | exact h.symm | simp
  have hiSup : (⨆ n, c n) = a ⊔ b := by
    apply le_antisymm
    · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
      intro n
      simp only [c]
      split_ifs <;> simp
    · exact sup_le (by simpa [c] using SigmaCompleteBooleanAlgebra.le_iSup_nat c 0)
        (by simpa [c] using SigmaCompleteBooleanAlgebra.le_iSup_nat c 1)
  have hsum : ∑' n, μ (c n) = μ a + μ b := by
    rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 1]
    have hz (x : ℕ) : (if x = 1 then 0 else if x = 0 then 0 else μ (c x)) = 0 := by
      simp only [c]
      split_ifs <;> simp
    simp only [hz, tsum_zero, add_zero, c, if_pos, if_false, Nat.one_ne_zero]
  rw [← hiSup, measure_iSup μ hc, hsum]

/-- The measure of the supremum of a finite pairwise disjoint family is the
sum of the measures. -/
theorem measure_finset_sup (s : Finset B)
    (hs : (s : Set B).PairwiseDisjoint id) :
    μ (s.sup id) = ∑ a ∈ s, μ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [μ.measure_bot]
  | @insert a s ha ih =>
      have hs' : (s : Set B).PairwiseDisjoint id := by
        intro x hx y hy hxy
        exact hs (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy
      have ha_disjoint : Disjoint a (s.sup id) := by
        rw [Finset.disjoint_sup_right]
        intro b hb
        exact hs (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
          (fun hab ↦ ha (hab ▸ hb))
      rw [Finset.sup_insert]
      simp only [id_eq]
      rw [μ.measure_sup ha_disjoint, Finset.sum_insert ha, ih hs']

private theorem measure_partialSups_of_pairwise_disjoint (a : ℕ → B)
    (ha : Pairwise (Disjoint on a)) (n : ℕ) :
    μ (partialSups a n) = ∑ i ∈ Finset.range (n + 1), μ (a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpartial : partialSups a (n + 1) = partialSups a n ⊔ a (n + 1) := by
      simpa using partialSups_succ a n
    rw [hpartial,
      measure_sup μ (partialSups_disjoint_of_disjoint a ha (Nat.lt_succ_self n)), ih,
      Finset.sum_range_succ]
    simp [Finset.sum_range_succ, add_assoc]

/-- The measure is monotone. -/
@[gcongr]
theorem measure_mono {a b : B} (h : a ≤ b) : μ a ≤ μ b := by
  rw [← sup_sdiff_cancel_right h, measure_sup μ disjoint_sdiff_self_right]
  simp

/-- The measure of every element is finite. -/
@[simp]
theorem measure_ne_top (a : B) : μ a ≠ ∞ := by
  exact ne_top_of_le_ne_top μ.m_top_ne_top (measure_mono μ le_top)

/-- The measure of a supremum is at most the sum of the measures. -/
theorem measure_sup_le (a b : B) : μ (a ⊔ b) ≤ μ a + μ b := by
  rw [← sup_sdiff_self a b, measure_sup μ disjoint_sdiff_self_right]
  exact add_le_add_right (measure_mono μ (sdiff_le : b \ a ≤ b)) (μ a)

/-- An element is the disjoint supremum of its difference and intersection
with another element. -/
theorem measure_sdiff_add_inf (a b : B) :
    μ (a \ b) + μ (a ⊓ b) = μ a := by
  rw [← measure_sup μ disjoint_inf_sdiff.symm, sup_sdiff_inf]

/-- The measure satisfies the inclusion-exclusion identity for two elements. -/
theorem measure_sup_add_inf (a b : B) :
    μ (a ⊔ b) + μ (a ⊓ b) = μ a + μ b := by
  rw [← sdiff_sup_self b a, measure_sup μ disjoint_sdiff_self_left,
    ← measure_sdiff_add_inf μ a b]
  ac_rfl

/-- The measures of an element and its complement add up to the total measure. -/
theorem measure_add_measure_compl (a : B) :
    μ a + μ aᶜ = μ ⊤ := by
  rw [← measure_sup μ disjoint_compl_right, sup_compl_eq_top]

/-- The measure of a countable supremum is at most the sum of the measures. -/
theorem measure_iSup_le (a : ℕ → B) :
    μ (⨆ i, a i) ≤ ∑' i, μ (a i) := by
  rw [← SigmaCompleteBooleanAlgebra.iSup_disjointed_nat a,
    measure_iSup μ (disjoint_disjointed a)]
  exact ENNReal.tsum_le_tsum fun n ↦ measure_mono μ (disjointed_le a n)

/-- The measure of the supremum of an increasing sequence is the supremum
of its measures. -/
theorem measure_iSup_eq_iSup {a : ℕ → B} (ha : Monotone a) :
    μ (⨆ i, a i) = ⨆ i, μ (a i) := by
  rw [← SigmaCompleteBooleanAlgebra.iSup_disjointed_nat a,
    measure_iSup μ (disjoint_disjointed a),
    ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  simp_rw [← measure_partialSups_of_pairwise_disjoint μ (disjointed a)
    (disjoint_disjointed a), partialSups_disjointed, ha.partialSups_eq]

end MeasureAlgebra

/-- An **equivalence of measure algebras** is an order isomorphism that preserves the measure. -/
structure MeasureAlgebraEquiv
    {B : Type u} {C : Type v}
    [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (ν : MeasureAlgebra C)
    extends B ≃o C where
  /-- The order isomorphism preserves the measure. -/
  map_measure' (a : B) : ν (toFun a) = μ a

namespace MeasureAlgebraEquiv

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

instance : CoeFun (MeasureAlgebraEquiv μ ν) (fun _ ↦ B → C) := by
  exact ⟨fun e ↦ e.toFun⟩

/-- A measure-algebra equivalence preserves the measure. -/
@[simp]
theorem map_measure (e : MeasureAlgebraEquiv μ ν) (a : B) :
    ν (e a) = μ a := by
  exact e.map_measure' a

end MeasureAlgebraEquiv
