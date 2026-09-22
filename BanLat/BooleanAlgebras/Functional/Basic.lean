/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.SigmaComplete
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countably additive functionals on Boolean algebras

This file introduces **nonnegative countably additive functionals** defined on
`σ`-complete Boolean algebras, with some of their basic properties.
-/

open Function
open Filter Topology
open scoped ENNReal symmDiff

universe u v

/-- `ν : B → ℝ≥0∞` is a **countably additive functional** on a `σ`-complete Boolean algebra
if `ν(⊥) = 0` and `ν(⨆ n, a n) = ∑ n, ν(a n)` for each pair-wise disjoint sequence. -/
structure CountablyAdditiveFunctional (B : Type u)
    [SigmaCompleteBooleanAlgebra B] where
  /-- The value of the functional. -/
  toFun : B → ℝ≥0∞
  /-- The functional vanishes at the bottom element. -/
  map_bot' : toFun ⊥ = 0
  /-- The functional is countably additive on pairwise disjoint sequences. -/
  map_iSup' ⦃a : ℕ → B⦄ : Pairwise (Disjoint on a) →
    toFun (⨆ n, a n) = ∑' n, toFun (a n)

instance {B : Type u} [SigmaCompleteBooleanAlgebra B] :
    CoeFun (CountablyAdditiveFunctional B) (fun _ ↦ B → ℝ≥0∞) :=
  ⟨CountablyAdditiveFunctional.toFun⟩

namespace CountablyAdditiveFunctional

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (ν : CountablyAdditiveFunctional B)

/-- A countably additive functional is finite if its value at the top element
is finite. -/
def IsFinite : Prop := ν ⊤ ≠ ∞

/-- A countably additive functional is faithful if it vanishes only at the
bottom element. -/
def IsFaithful : Prop := ∀ b, ν b = 0 ↔ b = ⊥

/-- A countably additive functional vanishes at the bottom element. -/
@[simp]
theorem map_bot : ν ⊥ = 0 := by
  exact ν.map_bot'

/-- A countably additive functional preserves disjoint countable suprema. -/
theorem map_iSup {a : ℕ → B} (ha : Pairwise (Disjoint on a)) :
    ν (⨆ n, a n) = ∑' n, ν (a n) := by
  exact ν.map_iSup' ha

/-- A countably additive functional is additive on disjoint elements. -/
theorem map_sup {a b : B} (h : Disjoint a b) :
    ν (a ⊔ b) = ν a + ν b := by
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
  have hsum : ∑' n, ν (c n) = ν a + ν b := by
    rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 1]
    have hz (x : ℕ) : (if x = 1 then 0 else if x = 0 then 0 else ν (c x)) = 0 := by
      simp only [c]
      split_ifs <;> simp
    simp only [hz, tsum_zero, add_zero, c, if_pos, if_false, Nat.one_ne_zero]
  rw [← hiSup, ν.map_iSup hc, hsum]

/-- A countably additive functional maps the supremum of a finite pairwise
disjoint family to the sum of its values. -/
theorem map_finset_sup (s : Finset B) (hs : (s : Set B).PairwiseDisjoint id) :
    ν (s.sup id) = ∑ b ∈ s, ν b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
      have hs' : (s : Set B).PairwiseDisjoint id := by
        intro c hc d hd hcd
        exact hs (Finset.mem_insert_of_mem hc) (Finset.mem_insert_of_mem hd) hcd
      have hb_disjoint : Disjoint b (s.sup id) := by
        rw [Finset.disjoint_sup_right]
        intro c hc
        exact hs (Finset.mem_insert_self b s) (Finset.mem_insert_of_mem hc)
          (fun hbc ↦ hb (hbc ▸ hc))
      rw [Finset.sup_insert]
      simp only [id_eq]
      rw [ν.map_sup hb_disjoint, Finset.sum_insert hb, ih hs']

/-- A countably additive functional is monotone. -/
theorem monotone : Monotone ν := by
  intro a b h
  rw [← sup_sdiff_cancel_right h, ν.map_sup disjoint_sdiff_self_right]
  simp

/-- Decomposing an element into its difference and intersection preserves its
functional value. -/
theorem map_sdiff_add_inf (a b : B) :
    ν (a \ b) + ν (a ⊓ b) = ν a := by
  rw [← ν.map_sup disjoint_inf_sdiff.symm, sup_sdiff_inf]

/-- The value of a difference is the difference of the values when the
subtracted element lies below the first and has finite value. -/
theorem map_sdiff {a b : B} (hba : b ≤ a) (hb : ν b ≠ ∞) :
    ν (a \ b) = ν a - ν b := by
  have h := ν.map_sdiff_add_inf a b
  rw [inf_eq_right.mpr hba] at h
  exact ENNReal.eq_sub_of_add_eq hb h

/-- A countably additive functional maps a symmetric difference to the sum of
the two corresponding differences. -/
theorem map_symmDiff (a b : B) :
    ν (a ∆ b) = ν (a \ b) + ν (b \ a) := by
  exact ν.map_sup disjoint_sdiff_sdiff

/-- The value of a supremum is at most the sum of the values. -/
theorem map_sup_le (a b : B) : ν (a ⊔ b) ≤ ν a + ν b := by
  rw [← sup_sdiff_self a b, ν.map_sup disjoint_sdiff_self_right]
  exact add_le_add_right (ν.monotone (sdiff_le : b \ a ≤ b)) (ν a)

/-- A countably additive functional is a valuation. -/
theorem map_sup_add_inf (a b : B) :
    ν (a ⊔ b) + ν (a ⊓ b) = ν a + ν b := by
  rw [← sdiff_sup_self b a, ν.map_sup disjoint_sdiff_self_left,
    ← ν.map_sdiff_add_inf a b]
  ac_rfl

/-- The values of an element and its complement add up to the value at the
top element. -/
theorem map_add_map_compl (a : B) : ν a + ν aᶜ = ν ⊤ := by
  rw [← ν.map_sup disjoint_compl_right, sup_compl_eq_top]

/-- The value of a countable supremum is at most the sum of the values. -/
theorem map_iSup_le (a : ℕ → B) :
    ν (⨆ n, a n) ≤ ∑' n, ν (a n) := by
  rw [← SigmaCompleteBooleanAlgebra.iSup_disjointed_nat a,
    ν.map_iSup (disjoint_disjointed a)]
  exact ENNReal.tsum_le_tsum fun n ↦ ν.monotone (disjointed_le a n)

/-- On every `σ`-complete Boolean subalgebra `A`, intersection with a fixed
element defines a countably additive functional. -/
noncomputable def infFunctional (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (b : B) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    CountablyAdditiveFunctional A := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  refine
    { toFun := fun a ↦ ν ((a : B) ⊓ b)
      map_bot' := by simp
      map_iSup' := ?_ }
  intro a ha
  rw [hA.coe_iSup, SigmaCompleteBooleanAlgebra.iSup_inf_nat]
  apply ν.map_iSup
  intro i j hij
  have hd := ha hij
  change Disjoint (a i) (a j) at hd
  have hd' : Disjoint (a i : B) (a j : B) := by
    rw [disjoint_iff] at hd ⊢
    exact congrArg Subtype.val hd
  exact hd'.mono inf_le_left inf_le_left

/-- The functional obtained by intersecting with `b` evaluates `a` as
`ν (a ⊓ b)`. -/
@[simp]
theorem infFunctional_apply (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (b : B) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ν.infFunctional A hA b a = ν ((a : B) ⊓ b) := by
  rfl

/-- The functional obtained by intersecting with a disjoint supremum is the
sum of the functionals obtained from its two terms. -/
theorem infFunctional_sup_apply (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) {b c : B} (hbc : Disjoint b c) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ν.infFunctional A hA (b ⊔ c) a =
      ν.infFunctional A hA b a + ν.infFunctional A hA c a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  simp only [infFunctional_apply, inf_sup_left]
  exact ν.map_sup (hbc.mono inf_le_right inf_le_right)

/-- The functional obtained by intersecting with `b` is dominated by the
restriction of the original functional. -/
theorem infFunctional_le (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (b : B) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ν.infFunctional A hA b a ≤ ν (a : B) := by
  simp only [infFunctional_apply]
  exact ν.monotone inf_le_left

/-- The restriction of a countably additive functional to a principal
interval. -/
noncomputable def restrict (b : B) :
    CountablyAdditiveFunctional (Set.Iic b) where
  toFun c := ν c
  map_bot' := ν.map_bot
  map_iSup' {a} ha := by
    rw [Set.Iic.coe_iSup_nat]
    exact ν.map_iSup fun _ _ hij ↦ Set.Iic.disjoint_iff.mp (ha hij)

@[simp]
theorem restrict_apply (b : B) (c : Set.Iic b) :
    ν.restrict b c = ν c := by
  rfl

/-- The restriction of a countably additive functional to a `σ`-complete
Boolean subalgebra. -/
noncomputable def restrictToSubalgebra (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    CountablyAdditiveFunctional A := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  refine
    { toFun := fun a ↦ ν (a : B)
      map_bot' := ν.map_bot
      map_iSup' := ?_ }
  intro a ha
  rw [hA.coe_iSup]
  apply ν.map_iSup
  intro i j hij
  change Disjoint (a i : B) (a j : B)
  rw [disjoint_iff]
  have hd := ha hij
  change Disjoint (a i) (a j) at hd
  rw [disjoint_iff] at hd
  exact congrArg Subtype.val hd

@[simp]
theorem restrictToSubalgebra_apply (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ν.restrictToSubalgebra A hA a = ν (a : B) := by
  rfl

/-- Every value of a finite countably additive functional is finite. -/
theorem ne_top (hν : ν.IsFinite) (a : B) : ν a ≠ ∞ := by
  exact ne_top_of_le_ne_top hν (ν.monotone le_top)

/-- Intersecting with an element of finite functional value produces a finite
functional on every `σ`-complete Boolean subalgebra. -/
theorem infFunctional_isFinite (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (b : B) (hb : ν b ≠ ∞) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (ν.infFunctional A hA b).IsFinite := by
  change ν (((⊤ : A) : B) ⊓ b) ≠ ∞
  simpa using hb

/-- A finite faithful countably additive functional is strictly monotone. -/
theorem strictMono (hν_fin : ν.IsFinite) (hν_faith : ν.IsFaithful) :
    StrictMono ν := by
  intro a b hab
  refine lt_of_le_of_ne (ν.monotone hab.le) ?_
  intro hν
  have hsum := ν.map_sdiff_add_inf b a
  rw [inf_eq_right.mpr hab.le, ← hν] at hsum
  have hzero : ν (b \ a) = 0 :=
    (ENNReal.add_left_inj (ν.ne_top hν_fin a)).mp (by simpa using hsum)
  apply not_le_of_gt hab
  rw [← sdiff_eq_bot_iff, ← hν_faith]
  exact hzero

/-- Restriction to a principal interval is finite when the functional is
finite at the endpoint. -/
theorem restrict_isFinite (b : B) (hb : ν b ≠ ∞) :
    (ν.restrict b).IsFinite := by
  exact hb

/-- Restriction to a principal interval preserves faithfulness. -/
theorem restrict_isFaithful (b : B) (hν : ν.IsFaithful) :
    (ν.restrict b).IsFaithful := by
  intro c
  rw [restrict_apply, hν]
  constructor
  · intro hc
    exact Subtype.ext hc
  · intro hc
    exact congrArg Subtype.val hc

/-- Restriction to a `σ`-complete Boolean subalgebra preserves finiteness. -/
theorem restrictToSubalgebra_isFinite (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (hν : ν.IsFinite) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (ν.restrictToSubalgebra A hA).IsFinite := by
  exact hν

/-- Restriction to a `σ`-complete Boolean subalgebra preserves faithfulness. -/
theorem restrictToSubalgebra_isFaithful (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (hν : ν.IsFaithful) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (ν.restrictToSubalgebra A hA).IsFaithful := by
  intro a
  rw [restrictToSubalgebra_apply, hν]
  constructor
  · intro ha
    exact Subtype.ext ha
  · intro ha
    exact congrArg Subtype.val ha

/-- For `r ∈ ℝ≥0` and `ν : B → ℝ≥0∞`, `ν.scaledFunctional r` is the countably
additive functional given by `b ↦ r * ν b`. -/
noncomputable def scaledFunctional (r : NNReal) :
    CountablyAdditiveFunctional B where
  toFun := fun b ↦ (r : ℝ≥0∞) * ν b
  map_bot' := by simp
  map_iSup' := by
    intro a ha
    rw [ν.map_iSup ha, ENNReal.tsum_mul_left]

@[simp]
theorem scaledFunctional_apply (r : NNReal) (b : B) :
    scaledFunctional ν r b = (r : ℝ≥0∞) * ν b := rfl

/-- If `ν` is finite, then `ν.scaledFunctional r` is finite for every
`r ∈ ℝ≥0`. -/
theorem scaledFunctional_isFinite (r : NNReal) (hν : ν.IsFinite) :
    (scaledFunctional ν r).IsFinite := by
  exact ENNReal.mul_ne_top (by simp) hν

/-- Let `ρ, ν : B → ℝ≥0∞` be countably additive functionals such that `ρ` is
finite and `ρ b ≤ ν b` for every `b ∈ B`. Then `subFunctional ν ρ hρ hρν` is
the countably additive functional given by `b ↦ ν b - ρ b`. -/
noncomputable def subFunctional (ρ : CountablyAdditiveFunctional B)
    (hρ : ρ.IsFinite) (hρν : ∀ b, ρ b ≤ ν b) :
    CountablyAdditiveFunctional B where
  toFun := fun b ↦ ν b - ρ b
  map_bot' := by simp
  map_iSup' := by
    intro a ha
    have hsum : ∑' n, ρ (a n) ≠ ∞ := by
      rw [← ρ.map_iSup ha]
      exact ρ.ne_top hρ _
    rw [ν.map_iSup ha, ρ.map_iSup ha]
    exact (ENNReal.tsum_sub hsum fun n ↦ hρν (a n)).symm

/-- The subtracted functional evaluates to the pointwise difference. -/
@[simp]
theorem subFunctional_apply (ρ : CountablyAdditiveFunctional B)
    (hρ : ρ.IsFinite) (hρν : ∀ b, ρ b ≤ ν b) (b : B) :
    ν.subFunctional ρ hρ hρν b = ν b - ρ b := by
  rfl

/-- Adding a subtracted functional back to the finite functional being
subtracted recovers the original functional. -/
theorem add_subFunctional_apply (ρ : CountablyAdditiveFunctional B)
    (hρ : ρ.IsFinite) (hρν : ∀ b, ρ b ≤ ν b) (b : B) :
    ρ b + ν.subFunctional ρ hρ hρν b = ν b := by
  rw [subFunctional_apply, add_comm, tsub_add_cancel_of_le (hρν b)]

/-- Let `e : B ≃o C` be an order isomorphism and let `ρ : C → ℝ≥0∞` be a
countably additive functional. Then `pullbackFunctional e ρ` is the countably
additive functional on `B` given by `b ↦ ρ (e b)`. -/
noncomputable def pullbackFunctional {C : Type v} [SigmaCompleteBooleanAlgebra C]
    (e : B ≃o C) (ρ : CountablyAdditiveFunctional C) :
    CountablyAdditiveFunctional B where
  toFun := fun b ↦ ρ (e b)
  map_bot' := by rw [e.map_bot, ρ.map_bot]
  map_iSup' := by
    intro a ha
    rw [OrderIso.map_iSup_nat e a]
    apply ρ.map_iSup
    intro i j hij
    exact (ha hij).map_orderIso e

private theorem map_partialSups_of_pairwise_disjoint (a : ℕ → B)
    (ha : Pairwise (Disjoint on a)) (n : ℕ) :
    ν (partialSups a n) = ∑ i ∈ Finset.range (n + 1), ν (a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpartial : partialSups a (n + 1) = partialSups a n ⊔ a (n + 1) := by
        simpa using partialSups_succ a n
      rw [hpartial,
        ν.map_sup (partialSups_disjoint_of_disjoint a ha (Nat.lt_succ_self n)), ih,
        Finset.sum_range_succ]
      simp [Finset.sum_range_succ, add_assoc]

/-- A countably additive functional preserves suprema of increasing
sequences. -/
theorem map_iSup_eq_iSup {a : ℕ → B} (ha : Monotone a) :
    ν (⨆ n, a n) = ⨆ n, ν (a n) := by
  rw [← SigmaCompleteBooleanAlgebra.iSup_disjointed_nat a,
    ν.map_iSup (disjoint_disjointed a),
    ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  simp_rw [← map_partialSups_of_pairwise_disjoint ν (disjointed a)
    (disjoint_disjointed a), partialSups_disjointed, ha.partialSups_eq]

/-- The values of a countably additive functional along an increasing
sequence converge to the value of its supremum. -/
theorem tendsto_map_iSup {a : ℕ → B} (ha : Monotone a) :
    Filter.Tendsto (fun n ↦ ν (a n)) Filter.atTop (𝓝 (ν (⨆ n, a n))) := by
  rw [ν.map_iSup_eq_iSup ha]
  exact tendsto_atTop_iSup (ν.monotone.comp ha)

end CountablyAdditiveFunctional
