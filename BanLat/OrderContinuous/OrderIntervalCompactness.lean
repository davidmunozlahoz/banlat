/-
Authors: Pedro Tradacete
-/

import BanLat.Examples.Lp.WeakCompactness
import BanLat.L1repr.Basic
import BanLat.Quotient
import BanLat.OrderContinuous.Ando
import BanLat.OrderContinuous.Nakano
import BanLat.Operators.Carrier
import Mathlib.Order.PartialSups

/-!
# Weak compactness of order intervals

Order intervals in a Banach lattice with order continuous norm are weakly compact.
The proof uses a positive functional that separates a fixed interval and an `L¹`
representation whose inverse on that interval is weakly continuous.
-/

noncomputable section

open Set Filter Topology

universe u

namespace BanachLattice

variable (X : Type u) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- A positive functional `φ` admits a lattice map into an `L¹` space whose norm
at `x` is `φ |x|`. The map factors through the quotient by the null ideal of `φ`,
where the induced functional is strictly positive. -/
private lemma exists_L1_normingHom (φ : StrongDual ℝ X) (hφ : 0 ≤ φ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
      (j : VecLatHom X (MeasureTheory.Lp ℝ 1 μ)), ∀ x : X, ‖j x‖ = φ |x| := by
  let J := OrderBoundedHom.null (StrongDual.toOrderDualSpace φ)
  have hmem (x : X) : x ∈ J ↔ φ |x| = 0 := by
    simp only [J, OrderBoundedHom.mem_null,
      abs_of_nonneg (show 0 ≤ StrongDual.toOrderDualSpace φ from hφ)]
    rfl
  have hker : J.toSubmodule ≤ LinearMap.ker φ.toLinearMap := fun x hx ↦
    (abs_eq_zero_iff_zero _).mp (le_antisymm
      ((StrongDual.abs_apply_le_apply_abs hφ x).trans_eq ((hmem x).mp hx)) (abs_nonneg _))
  let ψ := J.toSubmodule.liftQ φ.toLinearMap hker
  have hψ : StrictlyPositive ψ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := J.lift_pos hz.le
    refine lt_of_le_of_ne (StrongDual.apply_nonneg_of_nonneg hφ hx) ?_
    exact fun heq ↦ hz.ne' ((Submodule.Quotient.mk_eq_zero J.toSubmodule).mpr
      ((hmem x).mpr ((congrArg φ (abs_of_nonneg hx)).trans heq.symm)))
  obtain ⟨Ω, m, μ, T, _, _, hT⟩ := exists_L1_representation_of_strictlyPositive ψ hψ
  refine ⟨Ω, m, μ, T.comp J.mkQVecLatHom, fun x ↦ ?_⟩
  exact (norm_map_eq_apply_abs ψ T hT (J.mkQ x)).trans (congrArg ψ (J.mkQ_abs x).symm)

/-- In an order-continuous Banach lattice, the vectors whose moduli are annihilated
by a positive functional form a projection band. -/
private lemma positiveFunctional_kernel_projectionBand [IsOrderContinuousNorm X]
    (φ : StrongDual ℝ X) (hφ : 0 ≤ φ) :
    ∃ P : ProjectionBand X, ∀ x : X, x ∈ P ↔ φ |x| = 0 := by
  let J := OrderBoundedHom.null (StrongDual.toOrderDualSpace φ)
  have hmem (x : X) : x ∈ J ↔ φ |x| = 0 := by
    rw [OrderBoundedHom.mem_null, abs_of_nonneg (show 0 ≤ StrongDual.toOrderDualSpace φ from hφ)]
    rfl
  have hJ : IsClosed (J : Set X) := by
    change IsClosed {x | x ∈ J}
    simp only [hmem]
    exact isClosed_eq (φ.continuous.comp (continuous_id.sup continuous_id.neg)) continuous_const
  obtain ⟨P, hP⟩ := projectionBand_of_isClosed_orderIdeal J hJ
  exact ⟨P, fun x ↦ (Set.ext_iff.mp hP x).trans (hmem x)⟩

/-- A positive vector admits a positive norming functional of norm at most one,
together with the projection band on which that functional annihilates moduli. -/
private theorem exists_norming_null_projection [IsOrderContinuousNorm X]
    (x : X) (hx : 0 ≤ x) :
    ∃ (φ : StrongDual ℝ X) (P : ProjectionBand X),
      0 ≤ φ ∧ ‖φ‖ ≤ 1 ∧ φ x = ‖x‖ ∧
      (∀ y : X, y ∈ P ↔ φ |y| = 0) := by
  obtain ⟨φ, hφ, hnorm, hval⟩ := StrongDual.exists_positive_dual_norming hx
  obtain ⟨P, hP⟩ := positiveFunctional_kernel_projectionBand X φ hφ
  exact ⟨φ, P, hφ, hnorm, hval, hP⟩

/-- With order continuous norm, a decreasing positive sequence converges in norm to
zero if each term has a positive norming functional of norm at most one that
annihilates the next term. -/
private theorem norming_null_sequence_tendsto_zero [IsOrderContinuousNorm X]
    (r : ℕ → X) (φ : ℕ → StrongDual ℝ X)
    (hr : Antitone r) (hpos : ∀ n, 0 ≤ r n)
    (hφpos : ∀ n, 0 ≤ φ n) (hφnorm : ∀ n, ‖φ n‖ ≤ 1)
    (hnorm : ∀ n, φ n (r n) = ‖r n‖)
    (hnull : ∀ n, φ n (r (n + 1)) = 0) : Tendsto r atTop (nhds 0) := by
  obtain ⟨a, ha, ht⟩ := BanachLattice.tendsto_of_monotone_bddAbove
    (fun i j hij ↦ sub_le_sub_left (hr hij) (r 0))
    (show BddAbove (range (fun n ↦ r 0 - r n)) from
      ⟨r 0, fun _ ⟨n, hn⟩ ↦ hn ▸ sub_le_self _ (hpos n)⟩)
  have hl : Tendsto r atTop (nhds (r 0 - a)) := by
    simpa only [sub_sub_cancel] using ht.const_sub (r 0)
  have hglb : IsGLB (range r) (r 0 - a) := isGLB_of_tendsto_atTop hr hl
  have hlpos : 0 ≤ r 0 - a := hglb.2 (fun _ ⟨n, hn⟩ ↦ hn ▸ hpos n)
  have hφl (n : ℕ) : φ n (r 0 - a) = 0 :=
    le_antisymm
      ((StrongDual.apply_le_apply_of_nonneg (hφpos n)
        (hglb.1 ⟨n + 1, rfl⟩)).trans_eq (hnull n))
      (StrongDual.apply_nonneg_of_nonneg (hφpos n) hlpos)
  have hn (n : ℕ) : ‖r n‖ ≤ ‖r n - (r 0 - a)‖ := by
    calc
      ‖r n‖ = φ n (r n - (r 0 - a)) := by rw [map_sub, hφl, sub_zero, hnorm]
      _ ≤ ‖φ n (r n - (r 0 - a))‖ := le_abs_self _
      _ ≤ ‖φ n‖ * ‖r n - (r 0 - a)‖ := (φ n).le_opNorm _
      _ ≤ ‖r n - (r 0 - a)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (hφnorm n)
  have hd : Tendsto (fun n ↦ ‖r n - (r 0 - a)‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using (hl.sub_const (r 0 - a)).norm
  have hzero : r 0 - a = 0 :=
    norm_eq_zero.mp (le_antisymm (le_of_tendsto_of_tendsto' hl.norm hd hn)
      (norm_nonneg _))
  simpa only [hzero] using hl

/-- In an order-continuous Banach lattice, countably many positive functionals of
norm at most one jointly detect every nonzero vector in a fixed positive interval. -/
private theorem exists_positive_interval_separating_sequence
   [IsOrderContinuousNorm X] (e : X) (he : 0 ≤ e) :
    ∃ φ : ℕ → StrongDual ℝ X,
      (∀ n, 0 ≤ φ n) ∧ (∀ n, ‖φ n‖ ≤ 1) ∧
      ∀ y : X, 0 ≤ y → y ≤ e → (∀ n, φ n y = 0) → y = 0 := by
  classical
  choose φ P hφpos hφnorm hφval hP using
    (fun x : {x : X // 0 ≤ x} ↦ exists_norming_null_projection X x.val x.property)
  let q : ℕ → {x : X // 0 ≤ x} :=
    Nat.rec ⟨e, he⟩ (fun _ x ↦ ⟨(P x).bandProjection x.val,
      Positive.zero_le_iff.mp (P x).bandProjection_nonneg x.val x.property⟩)
  have hanti : Antitone (fun n ↦ (q n).val) :=
    antitone_nat_of_succ_le (fun n ↦
      Positive.le_iff.mp (P (q n)).bandProjection_le_id (q n).val (q n).property)
  have hnull (n : ℕ) : φ (q n) (q (n + 1)).val = 0 := by
    simpa only [abs_of_nonneg (q (n + 1)).property] using
      (hP (q n) (q (n + 1)).val).mp ((P (q n)).bandProjection_mem (q n).val)
  have ht : Tendsto (fun n ↦ (q n).val) atTop (nhds 0) :=
    norming_null_sequence_tendsto_zero X (fun n ↦ (q n).val) (fun n ↦ φ (q n))
      hanti (fun n ↦ (q n).property) (fun n ↦ hφpos (q n))
      (fun n ↦ hφnorm (q n)) (fun n ↦ hφval (q n)) hnull
  refine ⟨fun n ↦ φ (q n), fun n ↦ hφpos (q n), fun n ↦ hφnorm (q n), ?_⟩
  intro y hy hye hzero
  have hyq : ∀ n, y ≤ (q n).val := by
    intro n
    induction n with
    | zero => exact hye
    | succ n ih =>
      have hymem : y ∈ P (q n) := (hP (q n) y).mpr
        (by simpa only [abs_of_nonneg hy] using hzero n)
      simpa only [(P (q n)).bandProjection_eq_of_mem hymem] using
        (Positive.monotone_iff.mpr (Positive.zero_le_iff.mp
          (P (q n)).bandProjection_nonneg)) ih
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds ht hyq) hy

/-- Every positive order interval in an order-continuous Banach lattice admits a
positive continuous functional that vanishes only at zero on that interval. -/
private theorem exists_positive_interval_strict_functional
    [IsOrderContinuousNorm X] (e : X) (he : 0 ≤ e) :
    ∃ φ : StrongDual ℝ X, 0 ≤ φ ∧
      ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0 := by
  obtain ⟨φ, hpos, hnorm, hsep⟩ := exists_positive_interval_separating_sequence X e he
  let f : ℕ → StrongDual ℝ X := fun n ↦ (1 / 2 : ℝ) ^ n • φ n
  have hg : Summable (fun n ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hb (n : ℕ) : ‖f n‖ ≤ (1 / 2 : ℝ) ^ n := by
    simpa only [f, norm_smul,
      Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)] using
      mul_le_of_le_one_right (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n) (hnorm n)
  have hs : Summable f := hg.of_norm_bounded hb
  have hfpos (n : ℕ) : 0 ≤ f n :=
    smul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n) (hpos n)
  refine ⟨∑' n, f n, tsum_nonneg hfpos, ?_⟩
  intro y hy hye hzero
  apply hsep y hy hye
  intro n
  have hn : f n y ≤ 0 :=
    (StrongDual.le_iff.mp (hs.le_tsum n (fun m _ ↦ hfpos m)) y hy).trans_eq hzero
  change (1 / 2 : ℝ) ^ n * φ n y ≤ 0 at hn
  exact le_antisymm
    (nonpos_of_mul_nonpos_right hn (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))
    (StrongDual.apply_nonneg_of_nonneg (hpos n) hy)

/-- Under order continuity, a positive functional's value at the supremum of a
positive sequence is bounded by the sum of its values, when that sum converges. -/
private lemma positive_functional_range_sup_le_tsum [IsOrderContinuousNorm X]
    (φ : StrongDual ℝ X) (hφ : 0 ≤ φ) (r : ℕ → X) (hr : ∀ n, 0 ≤ r n)
    (hs : Summable (fun n ↦ φ (r n))) (z : X) (hz : IsLUB (range r) z) :
    φ z ≤ ∑' n, φ (r n) := by
  have hfz : IsLUB (range (partialSups r)) z := by
    simpa only [IsLUB, upperBounds_range_partialSups] using hz
  have hfs (n : ℕ) : partialSups r n ≤ ∑ k ∈ Finset.Iic n, r k :=
    partialSups_le _ _ _ (fun k hk ↦
      Finset.single_le_sum (fun j _ ↦ hr j) (Finset.mem_Iic.mpr hk))
  refine le_of_tendsto' (φ.continuous.tendsto z |>.comp
    (IsSigmaOrderContinuousNorm.tendsto_of_monotone_isLUB (partialSups r).monotone hfz))
    (fun n ↦ ?_)
  exact (show φ (partialSups r n) ≤ ∑ k ∈ Finset.Iic n, φ (r k) from by
    simpa only [map_sum] using StrongDual.apply_le_apply_of_nonneg hφ (hfs n)).trans
      (hs.sum_le_tsum _ (fun k _ ↦ StrongDual.apply_nonneg_of_nonneg hφ (hr k)))

/-- With order continuous norm, a sequence in `[0, e]` converges in norm to zero if
its values under a positive functional strictly positive on this interval are summable. -/
private lemma positive_interval_tendsto_zero_of_summable
    [IsOrderContinuousNorm X] (e : X)
    (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0)
    (r : ℕ → X) (hr : ∀ n, 0 ≤ r n) (hre : ∀ n, r n ≤ e)
    (hs : Summable (fun n ↦ φ (r n))) : Tendsto r atTop (nhds 0) := by
  let : ConditionallyCompleteLattice X := conditionallyCompleteLatticeOfIsOrderContinuousNorm
  let z : ℕ → X := fun n ↦ sSup (range (fun k ↦ r (k + n)))
  have hz (n : ℕ) : IsLUB (range (fun k ↦ r (k + n))) (z n) :=
    isLUB_csSup (range_nonempty _) ⟨e, fun _ ⟨k, hk⟩ ↦ hk ▸ hre (k + n)⟩
  have hanti : Antitone z := antitone_nat_of_succ_le (fun n ↦
    (hz (n + 1)).2 (fun _ ⟨k, hk⟩ ↦ hk ▸
      (hz n).1 ⟨k + 1, congrArg r (by omega)⟩))
  have hrz (n : ℕ) : r n ≤ z n := (hz n).1 ⟨0, by simp⟩
  have hzpos (n : ℕ) : 0 ≤ z n := (hr n).trans (hrz n)
  have hze (n : ℕ) : z n ≤ e := (hz n).2 (fun _ ⟨k, hk⟩ ↦ hk ▸ hre (k + n))
  let b := sSup (range (fun n ↦ -z n))
  have hb : IsLUB (range (fun n ↦ -z n)) b :=
    isLUB_csSup (range_nonempty _) ⟨0, fun _ ⟨n, hn⟩ ↦ hn ▸ neg_nonpos.mpr (hzpos n)⟩
  have ht : Tendsto z atTop (nhds (-b)) := by
    simpa only [neg_neg] using
      (IsSigmaOrderContinuousNorm.tendsto_of_monotone_isLUB hanti.neg hb).neg
  have hφz (n : ℕ) : φ (z n) ≤ ∑' k, φ (r (k + n)) :=
    positive_functional_range_sup_le_tsum X φ hφ (fun k ↦ r (k + n))
      (fun k ↦ hr (k + n)) (hs.comp_injective (add_left_injective n)) (z n) (hz n)
  have hble : φ (-b) ≤ 0 :=
    le_of_tendsto_of_tendsto' (φ.continuous.tendsto (-b) |>.comp ht)
      (tendsto_sum_nat_add (fun k ↦ φ (r k))) hφz
  have hbpos : 0 ≤ -b := ge_of_tendsto' ht hzpos
  have hbzero : -b = 0 := hsep (-b) hbpos (le_of_tendsto' ht hze)
    (le_antisymm hble (StrongDual.apply_nonneg_of_nonneg hφ hbpos))
  exact squeeze_zero_norm (a := fun n ↦ ‖z n‖) (fun n ↦ norm_le_norm_of_abs_le_abs
    (by simpa only [abs_of_nonneg (hr n), abs_of_nonneg (hzpos n)] using hrz n))
    (by simpa only [hbzero, norm_zero] using ht.norm)

/-- Under order continuity, a functional strictly positive on `[0, e]` controls the
norm uniformly there: sufficiently small evaluations imply small norms. -/
private lemma positive_interval_uniform_norm_control
    [IsOrderContinuousNorm X] (e : X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : X, 0 ≤ y → y ≤ e → φ y < δ → ‖y‖ < ε := by
  intro ε hε
  by_contra hno
  push Not at hno
  choose r hr hre hrφ hrnorm using (fun n : ℕ ↦ hno ((1 / 2 : ℝ)^n)
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))
  have hs : Summable (fun n ↦ φ (r n)) := Summable.of_nonneg_of_le
    (fun n ↦ StrongDual.apply_nonneg_of_nonneg hφ (hr n)) (fun n ↦ (hrφ n).le)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))
  have ht : Tendsto (fun n ↦ ‖r n‖) atTop (nhds 0) := by
    simpa only [norm_zero] using
      (positive_interval_tendsto_zero_of_summable X e φ hφ hsep r hr hre hs).norm
  exact hε.not_ge (le_of_tendsto_of_tendsto' tendsto_const_nhds ht hrnorm)

variable (Z : Type u) [NormedAddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
  [BanachLattice Z]

/-- A lattice map satisfying `‖j y‖ = φ |y|` induces the original norm uniformity
on an order interval where `φ` is strictly positive, under order continuity. -/
private lemma interval_norming_isUniformInducing [IsOrderContinuousNorm X]
    (e : X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0)
    (j : VecLatHom X Z) (hj : ∀ y, ‖j y‖ = φ |y|) :
    IsUniformInducing (fun y : Icc (0 : X) e ↦ j y.val) := by
  apply Metric.isUniformInducing_iff.mpr
  refine ⟨(show X →L[ℝ] Z from ⟨j.toLinearMap,
      Positive.continuous (Positive.monotone_iff.mp j.monotone)⟩).uniformContinuous.comp
      uniformContinuous_subtype_val, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := positive_interval_uniform_norm_control X e φ hφ hsep ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a b hab
  have hb : |a.val - b.val| ≤ e := abs_le'.mpr
    ⟨(sub_le_self _ b.property.1).trans a.property.2,
      by simpa only [neg_sub] using (sub_le_self _ a.property.1).trans b.property.2⟩
  simpa only [Subtype.dist_eq, dist_eq_norm, norm_abs_eq_norm] using
    hc |a.val - b.val| (abs_nonneg _) hb
      (by rw [← hj, map_sub]; simpa only [dist_eq_norm] using hab)

/-- Under order continuity, a lattice map normed by a functional strictly positive
on the interval sends closed subsets of that interval to norm-closed sets. -/
private lemma interval_norming_isClosed_image [IsOrderContinuousNorm X]
    (e : X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0)
    (j : VecLatHom X Z) (hj : ∀ y, ‖j y‖ = φ |y|)
    (C : Set X) (hC : IsClosed C) (hs : C ⊆ Icc 0 e) : IsClosed (j '' C) := by
  let : CompleteSpace (Icc (0 : X) e) := isClosed_Icc.completeSpace_coe
  have hu := interval_norming_isUniformInducing X Z e φ hφ hsep j hj
  have he : IsClosedEmbedding (fun y : Icc (0 : X) e ↦ j y.val) :=
    (isUniformEmbedding_iff_isUniformInducing.mpr hu).isClosedEmbedding
  have hc := he.isClosedMap (Subtype.val ⁻¹' C) (hC.preimage continuous_subtype_val)
  have heq : (fun y : Icc (0 : X) e ↦ j y.val) '' (Subtype.val ⁻¹' C) = j '' C := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.val, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hs hy⟩, hy, rfl⟩
  simpa only [heq] using hc

/-- Under order continuity, a lattice map normed by a functional strictly positive
on the interval sends closed convex subsets of that interval to weakly closed sets. -/
private lemma interval_norming_isClosed_weak_image [IsOrderContinuousNorm X]
    (e : X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0)
    (j : VecLatHom X Z) (hj : ∀ y, ‖j y‖ = φ |y|)
    (C : Set X) (hC : IsClosed C) (hc : Convex ℝ C) (hs : C ⊆ Icc 0 e) :
    IsClosed (toWeakSpace ℝ Z '' (j '' C)) := by
  have hcl := interval_norming_isClosed_image X Z e φ hφ hsep j hj C hC hs
  have hv : Convex ℝ (j '' C) := hc.linear_image j.toLinearMap
  rw [← closure_eq_iff_isClosed, ← hv.toWeakSpace_closure ℝ, hcl.closure_eq]

/-- Under order continuity, a lattice map normed by a functional strictly positive
on the interval has a weakly continuous inverse on the image of that interval. -/
private lemma interval_norming_inverse_weak_continuous [IsOrderContinuousNorm X]
    (e : X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0)
    (j : VecLatHom X Z) (hj : ∀ y, ‖j y‖ = φ |y|)
    (g : (toWeakSpace ℝ Z '' (j '' Icc 0 e)) → X)
    (hg : ∀ z, g z ∈ Icc 0 e ∧ toWeakSpace ℝ Z (j (g z)) = z.val) :
    Continuous (fun z ↦ toWeakSpace ℝ X (g z)) := by
  have hu := interval_norming_isUniformInducing X Z e φ hφ hsep j hj
  have hinj := hu.isInducing.injective
  have hclosed (C : Set X) (hC : IsClosed C) (hc : Convex ℝ C) (hs : C ⊆ Icc 0 e) :
      IsClosed (g ⁻¹' C) := by
    have hw := interval_norming_isClosed_weak_image X Z e φ hφ hsep j hj C hC hc hs
    have heq : g ⁻¹' C = Subtype.val ⁻¹' (toWeakSpace ℝ Z '' (j '' C)) := by
      ext z
      constructor
      · intro hz
        exact ⟨j (g z), ⟨g z, hz, rfl⟩, (hg z).2⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
        have he : j y = j (g z) := (toWeakSpace ℝ Z).injective (hz.trans (hg z).2.symm)
        have hv : y = g z := congrArg Subtype.val (hinj
          (show (fun a : Icc (0 : X) e ↦ j a.val) ⟨y, hs hy⟩ =
            (fun a : Icc (0 : X) e ↦ j a.val) ⟨g z, (hg z).1⟩ from he))
        change g z ∈ C
        exact hv ▸ hy
    rw [heq]
    exact hw.preimage continuous_subtype_val
  apply WeakBilin.continuous_of_continuous_eval
  intro ψ
  change Continuous (fun a ↦ ψ (g a))
  apply OrderTopology.continuous_iff.mpr
  intro a
  have hlo := hclosed (Icc 0 e ∩ ψ ⁻¹' Iic a)
    (isClosed_Icc.inter (isClosed_Iic.preimage ψ.continuous))
    ((convex_Icc (0 : X) e).inter ((convex_Iic a).linear_preimage ψ.toLinearMap))
    inter_subset_left
  have hhi := hclosed (Icc 0 e ∩ ψ ⁻¹' Ici a)
    (isClosed_Icc.inter (isClosed_Ici.preimage ψ.continuous))
    ((convex_Icc (0 : X) e).inter ((convex_Ici a).linear_preimage ψ.toLinearMap))
    inter_subset_left
  have hlo' : g ⁻¹' (Icc 0 e ∩ ψ ⁻¹' Iic a) =
      ((fun z ↦ ψ (g z)) ⁻¹' Ioi a)ᶜ := by
    ext z
    simp only [mem_preimage, mem_inter_iff, (hg z).1, true_and,
      mem_Iic, mem_compl_iff, mem_Ioi, not_lt]
  have hhi' : g ⁻¹' (Icc 0 e ∩ ψ ⁻¹' Ici a) =
      ((fun z ↦ ψ (g z)) ⁻¹' Iio a)ᶜ := by
    ext z
    simp only [mem_preimage, mem_inter_iff, (hg z).1, true_and,
      mem_Ici, mem_compl_iff, mem_Iio, not_lt]
  exact ⟨by simpa only [hlo', compl_compl] using hlo.isOpen_compl,
    by simpa only [hhi', compl_compl] using hhi.isOpen_compl⟩

/-- Under order continuity, weak compactness of the target interval transfers back
along a lattice map normed by a functional strictly positive on the source interval. -/
private lemma interval_norming_isCompact [IsOrderContinuousNorm X]
    (e : X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ)
    (hsep : ∀ y : X, 0 ≤ y → y ≤ e → φ y = 0 → y = 0)
    (j : VecLatHom X Z) (hj : ∀ y, ‖j y‖ = φ |y|)
    (hZ : IsCompact (toWeakSpace ℝ Z '' Icc 0 (j e))) :
    IsCompact (toWeakSpace ℝ X '' Icc 0 e) := by
  let K := toWeakSpace ℝ Z '' (j '' Icc 0 e)
  have hclosed : IsClosed K := interval_norming_isClosed_weak_image X Z e φ hφ hsep
    j hj _ isClosed_Icc (convex_Icc (0 : X) e) subset_rfl
  have hs : K ⊆ toWeakSpace ℝ Z '' Icc 0 (j e) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨j y, ⟨j.map_nonneg hy.1, j.monotone hy.2⟩, rfl⟩
  have hc : IsCompact K := hZ.of_isClosed_subset hclosed hs
  have he : ∀ z : K, ∃ y : X, y ∈ Icc 0 e ∧ toWeakSpace ℝ Z (j y) = z.val := by
    rintro ⟨z, _, ⟨y, hy, rfl⟩, hz⟩
    exact ⟨y, hy, hz⟩
  choose g hg using he
  have hgcont := interval_norming_inverse_weak_continuous X Z e φ hφ hsep j hj g hg
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have hcompact := isCompact_univ.image hgcont
  have hinj := (interval_norming_isUniformInducing X Z e φ hφ hsep j hj).isInducing.injective
  have heq : (fun z ↦ toWeakSpace ℝ X (g z)) '' univ =
      toWeakSpace ℝ X '' Icc 0 e := by
    ext y
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨g z, (hg z).1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      let z : K := ⟨toWeakSpace ℝ Z (j x), ⟨j x, ⟨x, hx, rfl⟩, rfl⟩⟩
      have hje : j (g z) = j x := (toWeakSpace ℝ Z).injective (hg z).2
      have he : g z = x := congrArg Subtype.val (hinj
        (show (fun a : Icc (0 : X) e ↦ j a.val) ⟨g z, (hg z).1⟩ =
          (fun a : Icc (0 : X) e ↦ j a.val) ⟨x, hx⟩ from hje))
      exact ⟨z, mem_univ _, congrArg (toWeakSpace ℝ X) he⟩
  rw [← heq]
  exact hcompact

/-- Positive order intervals in an order-continuous Banach lattice are weakly compact. -/
theorem isCompact_toWeakSpace_Icc_zero [IsOrderContinuousNorm X]
    (e : X) (he : 0 ≤ e) : IsCompact (toWeakSpace ℝ X '' Icc 0 e) := by
  obtain ⟨φ, hφ, hsep⟩ := exists_positive_interval_strict_functional X e he
  obtain ⟨Ω, mΩ, μ, j, hj⟩ := exists_L1_normingHom X φ hφ
  let := mΩ
  exact interval_norming_isCompact X (MeasureTheory.Lp ℝ 1 μ) e φ hφ hsep j hj
    (MeasureTheory.Lp.isCompact_toWeakSpace_Icc_zero μ (j e) (j.map_nonneg he))

/-- Every order interval in an order-continuous Banach lattice is weakly compact. -/
theorem isCompact_toWeakSpace_Icc [IsOrderContinuousNorm X] (a b : X) :
    IsCompact (toWeakSpace ℝ X '' Icc a b) := by
  by_cases hab : a ≤ b
  · have h := (isCompact_toWeakSpace_Icc_zero X (b - a) (sub_nonneg.mpr hab)).image
      (continuous_id.add (continuous_const (y := toWeakSpace ℝ X a)))
    rw [image_image] at h
    change IsCompact ((toWeakSpace ℝ X ∘ (fun x ↦ x + a)) '' Icc 0 (b - a)) at h
    rw [image_comp, image_add_const_Icc, zero_add, sub_add_cancel] at h
    exact h
  · simpa only [Icc_eq_empty hab, image_empty] using
      (isCompact_empty : IsCompact (∅ : Set (WeakSpace ℝ X)))

end BanachLattice

namespace BidualSpace

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- The norm is order continuous exactly when the canonical bidual image is an order ideal. -/
theorem isOrderContinuousNorm_iff_range_inclusion_eq_orderIdeal :
    IsOrderContinuousNorm X ↔
      ∃ J : OrderIdeal (BidualSpace X), range inclusion = (J : Set (BidualSpace X)) :=
  ⟨fun _ ↦ range_inclusion_eq_orderIdeal_iff_isCompact_Icc.mpr
    (BanachLattice.isCompact_toWeakSpace_Icc_zero X),
    isOrderContinuousNorm_of_range_inclusion_eq_orderIdeal⟩

end BidualSpace

/-- A Banach lattice has order continuous norm exactly when its positive intervals
are weakly compact. -/
theorem BanachLattice.isOrderContinuousNorm_iff_isCompact_toWeakSpace_Icc_zero
    {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] :
    IsOrderContinuousNorm X ↔
      ∀ x : X, 0 ≤ x → IsCompact (toWeakSpace ℝ X '' Icc 0 x) :=
  BidualSpace.isOrderContinuousNorm_iff_range_inclusion_eq_orderIdeal.trans
    BidualSpace.range_inclusion_eq_orderIdeal_iff_isCompact_Icc
