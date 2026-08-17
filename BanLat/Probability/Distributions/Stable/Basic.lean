import BanLat.Probability.Distributions.Stable.Def

/-!
# This file establishes the following basic properties of symmetric `q`-stable measures:

  • `isSymmetricStable_dirac_zero`: the Dirac measure at zero is symmetric `q`-stable with
    scale zero.
  • `IsSymmetricStable.eq`: the index and scale parameter determine the measure uniquely.
  • `IsSymmetricStable.scale_eq`: the scale parameter is unique.
  • `IsSymmetricStable.map_mul`: scaling a symmetric `q`-stable measure gives a symmetric
    `q`-stable measure.
  • `IsSymmetricStable.map_neg`: reflecting a symmetric `q`-stable measure gives a symmetric
    `q`-stable measure.
  • `IsSymmetricStable.map_neg_eq_self`: symmetric `q`-stable measures are invariant under
    reflection.
  • `IsSymmetricStable.conv`: the convolution of two symmetric `q`-stable measures is symmetric
    `q`-stable, with scale parameter equal to the sum of their scale parameters.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {μ ν : Measure ℝ} {q : ℝ} {c d : ℝ≥0}

/-- The Dirac measure at zero is symmetric `q`-stable with scale zero for every `0 < q ≤ 2`. -/
lemma isSymmetricStable_dirac_zero (hq_pos : 0 < q) (hq_le_two : q ≤ 2) :
    IsSymmetricStable (Measure.dirac 0) q 0 := by
  refine ⟨hq_pos, hq_le_two, inferInstance, ?_⟩
  intro t
  simp

namespace IsSymmetricStable

/-- If `μ` and `ν` are symmetric `q`-stable measures with the same scale parameter, then `μ = ν`. -/
lemma eq (hμ : IsSymmetricStable μ q c)
    (hν : IsSymmetricStable ν q c) : μ = ν := by
  letI := hμ.isProbabilityMeasure
  letI := hν.isProbabilityMeasure
  apply Measure.ext_of_charFun
  funext t
  rw [hμ.charFun_eq, hν.charFun_eq]

/-- If `μ` is a symmetric `q`-stable measure with scale parameter `c` and a symmetric `q`-stable
measure with scale parameter `d`, then `c = d`. -/
lemma scale_eq (hμc : IsSymmetricStable μ q c)
    (hμd : IsSymmetricStable μ q d) : c = d := by
  have h := (hμc.charFun_eq 1).symm.trans (hμd.charFun_eq 1)
  have hre := congrArg Complex.re h
  simp only [abs_one, Real.one_rpow, mul_one, Complex.exp_ofReal_re] at hre
  exact NNReal.eq (neg_injective (Real.exp_injective hre))

/-- If `μ` is a symmetric `q`-stable measure with scale parameter `c` and `a ∈ ℝ`, then
`μ(a · •)` is symmetric `q`-stable with scale parameter `c * |a| ^ q`. -/
lemma map_mul (hμ : IsSymmetricStable μ q c) (a : ℝ) :
    IsSymmetricStable (μ.map (a * ·)) q (c * ‖a‖₊ ^ q) := by
  refine ⟨hμ.index_pos, hμ.index_le_two, ?_, ?_⟩
  · letI := hμ.isProbabilityMeasure
    exact μ.isProbabilityMeasure_map (by fun_prop)
  · intro t
    rw [charFun_map_mul, hμ.charFun_eq]
    congr 2
    simp only [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg t),
      NNReal.coe_mul, NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs]
    ring

/-- If `μ` is a symmetric `q`-stable measure, then `μ(- · •)` is symmetric
`q`-stable with the same scale parameter. -/
lemma map_neg (hμ : IsSymmetricStable μ q c) :
    IsSymmetricStable (μ.map (-·)) q c := by
  convert hμ.map_mul (-1) using 1 <;> simp

/-- If `μ` is a symmetric `q`-stable measure, then `μ` is invariant under reflection. -/
lemma map_neg_eq_self (hμ : IsSymmetricStable μ q c) :
    μ.map (-·) = μ := by
  exact hμ.map_neg.eq hμ

/-- If `μ` and `ν` are symmetric `q`-stable measures with scale parameters `c` and `d`, then
their convolution is symmetric `q`-stable with scale parameter `c + d`. -/
lemma conv (hμ : IsSymmetricStable μ q c) (hν : IsSymmetricStable ν q d) :
    IsSymmetricStable (μ ∗ ν) q (c + d) := by
  letI := hμ.isProbabilityMeasure
  letI := hν.isProbabilityMeasure
  refine ⟨hμ.index_pos, hμ.index_le_two, inferInstance, ?_⟩
  intro t
  rw [charFun_conv, hμ.charFun_eq, hν.charFun_eq, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end IsSymmetricStable

end ProbabilityTheory
