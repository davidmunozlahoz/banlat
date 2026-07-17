import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.IdentDistrib

/-!
# This file contains the following properties of finite sums of independent symmetric
# `q`-stable random variables:

  • `IndepFun.hasSymmetricStableLaw_fun_add`: the sum of two independent symmetric `q`-stable
    random variables is again a symmetric `q`-stable random variable..
  • `IndepFun.hasSymmetricStableLaw_add`: the pointwise addition of two independent symmetric
    `q`-stable random variables is again a symmetric `q`-stable random variable.
  • `iIndepFun.hasSymmetricStableLaw_finset_sum`: a finite sum of independent symmetric `q`-stable
    random variables is again a symmetric `q`-stable random variable.
  • `iIndepFun.hasSymmetricStableLaw_finset_sum_mul`: a finite linear combination of independent and
  symmetric `q`-stable random variables is again a symmetric `q`-stable random variable.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X Y : Ω → ℝ} {q : ℝ} {c d : ℝ≥0}

namespace IndepFun

/-- If `X` and `Y` are independent symmetric `q`-stable random variables with scale parameters
`c` and `d`, then their sum is symmetric `q`-stable with scale parameter `c + d`. -/
lemma hasSymmetricStableLaw_fun_add (hXY : IndepFun X Y P)
    (hX : HasSymmetricStableLaw X q c P) (hY : HasSymmetricStableLaw Y q d P) :
    HasSymmetricStableLaw (fun ω ↦ X ω + Y ω) q (c + d) P := by
  letI := hX.isProbabilityMeasure
  refine ⟨?_⟩
  rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map₀ hX.aemeasurable hY.aemeasurable]
  exact hX.isSymmetricStable_map.conv hY.isSymmetricStable_map

/-- If `X` and `Y` are independent symmetric `q`-stable random variables with scale parameters
`c` and `d`, then their pointwise sum is symmetric `q`-stable with scale parameter `c + d`. -/
lemma hasSymmetricStableLaw_add (hXY : IndepFun X Y P)
    (hX : HasSymmetricStableLaw X q c P) (hY : HasSymmetricStableLaw Y q d P) :
    HasSymmetricStableLaw (X + Y) q (c + d) P := by
  exact hXY.hasSymmetricStableLaw_fun_add hX hY

end IndepFun

namespace iIndepFun

/-- Let `Xₖ, k ∈ s` be an independent set of symmetric `q`-stable random variables with scales
`cₖ ≥ 0, k ∈ s`. Then `∑ₖ Xₖ` is symmetric `q`-stable with scale `∑ₖ cₖ`. -/
lemma hasSymmetricStableLaw_finset_sum {X : ι → Ω → ℝ} {c : ι → ℝ≥0}
    (hX : ∀ i, HasSymmetricStableLaw (X i) q (c i) P) (h_indep : iIndepFun X P)
    (hq_pos : 0 < q) (hq_le_two : q ≤ 2) (s : Finset ι) :
    HasSymmetricStableLaw (fun ω ↦ ∑ i ∈ s, X i ω) q (∑ i ∈ s, c i) P := by
  letI := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasSymmetricStableLaw_zero (P := P) hq_pos hq_le_two
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      apply IndepFun.hasSymmetricStableLaw_fun_add _ (hX i) ih
      convert (h_indep.indepFun_finsetSum_of_notMem₀
        (fun j ↦ (hX j).aemeasurable) hi).symm using 1
      ext ω
      simp

/-- Let `Xₖ, k ∈ s` be an independent set of symmetric `q`-stable random variables with scales
`cₖ ≥ 0` and `aₖ ∈ ℝ`. Then `∑ₖ aₖXₖ` is symmetric `q`-stable with scale `∑ₖ cₖ|aₖ|^q`. -/
lemma hasSymmetricStableLaw_finset_sum_mul {X : ι → Ω → ℝ} {c : ι → ℝ≥0}
    (hX : ∀ i, HasSymmetricStableLaw (X i) q (c i) P) (h_indep : iIndepFun X P)
    (hq_pos : 0 < q) (hq_le_two : q ≤ 2) (s : Finset ι) (a : ι → ℝ) :
    HasSymmetricStableLaw (fun ω ↦ ∑ i ∈ s, a i * X i ω) q
      (∑ i ∈ s, c i * ‖a i‖₊ ^ q) P := by
  apply hasSymmetricStableLaw_finset_sum
    (X := fun i ω ↦ a i * X i ω) (c := fun i ↦ c i * ‖a i‖₊ ^ q)
    (fun i ↦ (hX i).const_mul (a i)) _ hq_pos hq_le_two s
  convert h_indep.comp (fun i x ↦ a i * x) (fun _ ↦ by fun_prop) using 1

/-- Let `Xₖ, k ∈ s` be a fnite set of independent symmetric `q`-stable random variables with
common scale index `c` and `aₖ ∈ ℝ, k ∈ s`. Then `∑ k ∈ s, aₖXₖ` has the same distribution as
`(∑ k ∈ s, |a_k| ^ q) ^ q⁻¹ · Z` where is a symmetric `q`-stable random variable with index `c`. -/
lemma identDistrib_finset_sum_mul_of_hasSymmetricStableLaw
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {X : ι → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, HasSymmetricStableLaw (X i) q c P)
    (hZ : HasSymmetricStableLaw Z q c Q)
    (h_indep : iIndepFun X P) (s : Finset ι) (a : ι → ℝ) :
    IdentDistrib (fun ω ↦ ∑ i ∈ s, a i * X i ω)
      (fun ω ↦ ((↑(∑ i ∈ s, ‖a i‖₊ ^ q) : ℝ) ^ q⁻¹) * Z ω) P Q := by
  let A : ℝ≥0 := ∑ i ∈ s, ‖a i‖₊ ^ q
  have hq : q ≠ 0 := ne_of_gt hZ.isSymmetricStable_map.index_pos
  have hsum : HasSymmetricStableLaw (fun ω ↦ ∑ i ∈ s, a i * X i ω) q (c * A) P := by
    simpa [A, Finset.mul_sum] using h_indep.hasSymmetricStableLaw_finset_sum_mul hX
      hZ.isSymmetricStable_map.index_pos hZ.isSymmetricStable_map.index_le_two s a
  have hroot : ‖(A : ℝ) ^ q⁻¹‖₊ ^ q = A := by
    apply NNReal.eq
    have hnonneg : 0 ≤ (A : ℝ) ^ q⁻¹ := Real.rpow_nonneg A.2 _
    rw [NNReal.coe_rpow, coe_nnnorm, Real.norm_of_nonneg hnonneg]
    exact Real.rpow_inv_rpow A.2 hq
  have hscaled : HasSymmetricStableLaw (fun ω ↦ ((A : ℝ) ^ q⁻¹) * Z ω) q (c * A) Q := by
    simpa [hroot] using hZ.const_mul ((A : ℝ) ^ q⁻¹)
  refine ⟨hsum.aemeasurable, hscaled.aemeasurable, ?_⟩
  exact hsum.isSymmetricStable_map.eq hscaled.isSymmetricStable_map

end iIndepFun

end ProbabilityTheory
