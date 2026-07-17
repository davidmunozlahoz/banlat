import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.IndependentFinSums
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distributions as symmetric `2`-stable distributions

This file identifies symmetric `2`-stable distributions with centered real Gaussian distributions.
Following Mathlib, `gaussianReal m v` uses `v : ℝ≥0` for the variance. A centered Gaussian with
variance `v` has symmetric `2`-stable scale parameter `v / 2`; equivalently, scale parameter `c`
corresponds to variance `2 * c`.
It also identifies the law of a finite linear combination of independent standard centered
Gaussian random variables.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → ℝ} {μ : Measure ℝ} {c v : ℝ≥0}

/-- A centered real Gaussian distribution with variance `v` is symmetric `2`-stable with scale
parameter `v / 2`. -/
lemma isSymmetricStable_gaussianReal :
    IsSymmetricStable (gaussianReal 0 v) 2 (v / 2) := by
  refine ⟨by norm_num, by norm_num, inferInstance, ?_⟩
  intro t
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  norm_num [sq_abs]
  ring

/-- A symmetric `2`-stable measure is the centered Gaussian measure with variance twice its scale
parameter. -/
lemma IsSymmetricStable.eq_gaussianReal (hμ : IsSymmetricStable μ 2 c) :
    μ = gaussianReal 0 (2 * c) := by
  exact hμ.eq (by simpa using isSymmetricStable_gaussianReal (v := 2 * c))

/-- A random variable has a symmetric `2`-stable law exactly when it has the corresponding centered
Gaussian law. -/
lemma hasSymmetricStableLaw_two_iff_hasLaw_gaussianReal :
    HasSymmetricStableLaw X 2 c P ↔ HasLaw X (gaussianReal 0 (2 * c)) P := by
  constructor
  · intro hX
    exact ⟨hX.aemeasurable, hX.isSymmetricStable_map.eq_gaussianReal⟩
  · intro hX
    exact hX.hasSymmetricStableLaw (by
      simpa using isSymmetricStable_gaussianReal (v := 2 * c))

/-- A centered Gaussian random variable with variance `v` has a symmetric `2`-stable law with
scale parameter `v / 2`. -/
lemma HasLaw.hasSymmetricStableLaw_two
    (hX : HasLaw X (gaussianReal 0 v) P) :
    HasSymmetricStableLaw X 2 (v / 2) P := by
  exact hX.hasSymmetricStableLaw isSymmetricStable_gaussianReal

/-- The zero random variable has the centered Gaussian law with variance zero. -/
lemma hasLaw_zero_gaussianReal [IsProbabilityMeasure P] :
    HasLaw (fun _ : Ω ↦ 0) (gaussianReal 0 0) P := by
  refine ⟨by fun_prop, ?_⟩
  simp [Measure.map_const, gaussianReal_zero_var]

/-- A finite linear combination of independent standard centered Gaussian random variables is
centered Gaussian with variance equal to the sum of the squared coefficients. -/
lemma iIndepFun.hasLaw_finset_sum_mul_standardGaussian {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (s : Finset ι) (a : ι → ℝ) :
    HasLaw (fun ω ↦ ∑ i ∈ s, a i * X i ω)
      (gaussianReal 0 (∑ i ∈ s, ‖a i‖₊ ^ 2)) P := by
  have hstable := h_indep.hasSymmetricStableLaw_finset_sum_mul
    (fun i ↦ (hX i).hasSymmetricStableLaw_two) (by norm_num) (by norm_num) s a
  have hgaussian :=
    hasSymmetricStableLaw_two_iff_hasLaw_gaussianReal.mp hstable
  convert hgaussian using 1
  congr 2
  simp [Finset.mul_sum]

end ProbabilityTheory
