/-
Authors: Pedro Tradacete
-/

import BanLat.Examples.C0.Basic
import BanLat.Examples.Ellp.Sum
import BanLat.KBSpace.Basic
import BanLat.Reflexive.Basic

/-!
# Nonreflexivity of the classical sequence spaces

Neither `C₀(ℕ, ℝ)` nor `ℓ¹(ℕ, ℝ)` satisfies `IsReflexiveBanachSpace ℝ`.
The summing basis, given by the sequence of finite initial segments of the basis, witness failure
of the KB property in the first space and in the continuous dual of the second.
-/

noncomputable section

open Set Filter
open scoped ZeroAtInfty lp

/-- The summing basis is the sequence of sums of the first `n` coordinate vectors in `C₀(ℕ, ℝ)`. -/
private def c0PartialSum (n : ℕ) : C₀(ℕ, ℝ) :=
  ZeroAtInftyContinuousMap.ofFinsupp (∑ k ∈ Finset.range n, Finsupp.single k 1)

/-- The summing basis vectors take value one before its cutoff and zero thereafter. -/
private lemma c0PartialSum_apply (n k : ℕ) :
    c0PartialSum n k = if k < n then 1 else 0 := by
  simp [c0PartialSum, ZeroAtInftyContinuousMap.ofFinsupp_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply]

/-- The summing basis forms an increasing sequence of vectors in the pointwise
lattice order. -/
private lemma c0PartialSum_monotone : Monotone c0PartialSum := by
  intro n m h k
  rw [c0PartialSum_apply, c0PartialSum_apply]
  by_cases hn : k < n
  · simp only [ite_eq_left hn, ite_eq_left (hn.trans_le h), le_refl]
  · simp only [ite_eq_right hn]
    positivity

/-- Each term in the summing basis is positive. -/
private lemma c0PartialSum_nonneg (n : ℕ) : 0 ≤ c0PartialSum n := by
  intro k
  change 0 ≤ c0PartialSum n k
  rw [c0PartialSum_apply]
  positivity

/-- The summing basis vectors all belong to the closed unit ball. -/
private lemma norm_c0PartialSum_le (n : ℕ) : ‖c0PartialSum n‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro k
  change ‖c0PartialSum n k‖ ≤ 1
  rw [c0PartialSum_apply]
  split_ifs <;> norm_num

/-- Consecutive vectors in the summing basis stay a unit distance apart. -/
private lemma one_le_dist_c0PartialSum (n : ℕ) :
    1 ≤ dist (c0PartialSum (n + 1)) (c0PartialSum n) := by
  have h := (c0PartialSum (n + 1) - c0PartialSum n).toBCF.norm_coe_le_norm n
  change ‖c0PartialSum (n + 1) n - c0PartialSum n n‖ ≤
    ‖c0PartialSum (n + 1) - c0PartialSum n‖ at h
  simpa [c0PartialSum_apply, dist_eq_norm] using h

/-- The space `C₀(ℕ, ℝ)` is not reflexive. -/
theorem ZeroAtInftyContinuousMap.not_isReflexiveBanachSpace :
    ¬ IsReflexiveBanachSpace ℝ C₀(ℕ, ℝ) := by
  intro h
  let := IsKbSpace.of_isReflexiveBanachSpace h
  have hb : Bornology.IsBounded (range c0PartialSum) :=
    (isBounded_iff_forall_norm_le).mpr ⟨1, fun _ ⟨n, hn⟩ ↦ hn ▸ norm_c0PartialSum_le n⟩
  obtain ⟨x, hx⟩ := IsKbSpace.tendsto_of_monotone_of_isBounded
    c0PartialSum_monotone c0PartialSum_nonneg hb
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hx.cauchySeq 1 zero_lt_one
  exact (not_lt_of_ge (one_le_dist_c0PartialSum N)) (hN (N + 1) (Nat.le_succ N))

/-- Summing the first `n` coordinates defines a continuous functional on `ℓ¹`. -/
private def ell1PartialSum (n : ℕ) : StrongDual ℝ ℓ¹(ℕ, ℝ) :=
  ∑ k ∈ Finset.range n, lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 1 k

private lemma ell1PartialSum_apply (n : ℕ) (x : ℓ¹(ℕ, ℝ)) :
    ell1PartialSum n x = ∑ k ∈ Finset.range n, x k := by
  simp only [ell1PartialSum, sum_apply]
  rfl

/-- The sum of the first `n` coordinates defines a positive functional on `ℓ¹`. -/
private lemma ell1PartialSum_nonneg (n : ℕ) : 0 ≤ ell1PartialSum n := by
  refine StrongDual.nonneg_iff.mpr fun x hx ↦ ?_
  rw [ell1PartialSum_apply]
  exact Finset.sum_nonneg fun k _ ↦ hx k

/-- The sequence of sums of the first `n` coordinates define an increasing sequence of functionals
 in the dual lattice order. -/
private lemma ell1PartialSum_monotone : Monotone ell1PartialSum := by
  refine fun n m h ↦ StrongDual.le_iff.mpr fun x hx ↦ ?_
  rw [ell1PartialSum_apply, ell1PartialSum_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun k _ _ ↦ hx k)

/-- Summing the first `n` coordinates has operator norm at most one on `ℓ¹`. -/
private lemma norm_ell1PartialSum_le (n : ℕ) : ‖ell1PartialSum n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul, ell1PartialSum_apply]
  exact (norm_sum_le _ _).trans (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (1 : ENNReal).toReal) x (Finset.range n))

/-- Successive terms in the sequence of sums of the first `n` coordinates as functionals have
distance at least one. -/
private lemma one_le_dist_ell1PartialSum (n : ℕ) :
    1 ≤ dist (ell1PartialSum (n + 1)) (ell1PartialSum n) := by
  have h := (ell1PartialSum (n + 1) - ell1PartialSum n).le_opNorm
    (lp.single 1 n (1 : ℝ))
  simpa [sub_apply, ell1PartialSum_apply, lp.coeFn_single, Pi.single_apply,
    dist_eq_norm] using h

/-- Real `ℓ¹` is not a reflexive Banach space. -/
theorem lp.not_isReflexiveBanachSpace_ell1 : ¬ IsReflexiveBanachSpace ℝ ℓ¹(ℕ, ℝ) := by
  intro h
  let := IsKbSpace.of_isReflexiveBanachSpace h.dual
  have hb : Bornology.IsBounded (range ell1PartialSum) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, fun _ ⟨n, hn⟩ ↦ hn ▸ norm_ell1PartialSum_le n⟩
  obtain ⟨x, hx⟩ := IsKbSpace.tendsto_of_monotone_of_isBounded
    ell1PartialSum_monotone ell1PartialSum_nonneg hb
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hx.cauchySeq 1 zero_lt_one
  exact (not_lt_of_ge (one_le_dist_ell1PartialSum N)) (hN (N + 1) (Nat.le_succ N))
