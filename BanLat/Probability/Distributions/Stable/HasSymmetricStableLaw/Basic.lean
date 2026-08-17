import BanLat.Probability.Distributions.Stable.Basic
import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.Def
import Mathlib.Probability.HasLaw

/-!
# This file establishes the following basic properties of symmetric `q`-stable random variables:

  • `HasLaw.hasSymmetricStableLaw`: a random variable whose distribution is a symmetric
    `q`-stable measure has a symmetric `q`-stable law.
  • `hasSymmetricStableLaw_zero`: the zero random variable has a symmetric `q`-stable law with
    scale zero.
  • `HasSymmetricStableLaw.aemeasurable`: random variables with a symmetric `q`-stable law are
    almost everywhere measurable.
  • `HasSymmetricStableLaw.isProbabilityMeasure`: their underlying measure is a probability measure.
  • `HasSymmetricStableLaw.congr`: the law is preserved under almost everywhere equality.
  • `HasSymmetricStableLaw.const_mul`: scaling a random variable with a symmetric `q`-stable law
    gives a random variable with a symmetric `q`-stable law.
  • `HasSymmetricStableLaw.neg`: the opposite of a symmetric `q`-stable law is a symmetric
    `q`-stable law.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X Y : Ω → ℝ} {μ : Measure ℝ} {q : ℝ} {c : ℝ≥0}

/-- If `X` has law `μ` under `P` and `μ` is symmetric `q`-stable with scale parameter `c`, then
`X` has a symmetric `q`-stable law with scale parameter `c` under `P`. -/
lemma HasLaw.hasSymmetricStableLaw (hX : HasLaw X μ P) (hμ : IsSymmetricStable μ q c) :
    HasSymmetricStableLaw X q c P := by
  refine ⟨?_⟩
  rwa [hX.map_eq]

/-- If `P` is a probability measure and `0 < q ≤ 2`, then the zero random variable has a symmetric
`q`-stable law with scale zero under `P`. -/
lemma hasSymmetricStableLaw_zero [IsProbabilityMeasure P]
    (hq_pos : 0 < q) (hq_le_two : q ≤ 2) :
    HasSymmetricStableLaw (fun _ ↦ 0) q 0 P := by
  refine ⟨?_⟩
  simpa [Measure.map_const] using
    (isSymmetricStable_dirac_zero (q := q) hq_pos hq_le_two)

namespace HasSymmetricStableLaw

/-- If `X` has a symmetric `q`-stable law under `P`, then `X` is almost everywhere measurable
with respect to `P`. -/
@[fun_prop]
lemma aemeasurable (hX : HasSymmetricStableLaw X q c P) : AEMeasurable X P := by
  exact AEMeasurable.of_map_ne_zero
    hX.isSymmetricStable_map.isProbabilityMeasure.ne_zero

/-- If `X` has a symmetric `q`-stable law under `P`, then `P` is a probability measure. -/
lemma isProbabilityMeasure (hX : HasSymmetricStableLaw X q c P) : IsProbabilityMeasure P := by
  letI := hX.isSymmetricStable_map.isProbabilityMeasure
  exact P.isProbabilityMeasure_of_map X

/-- If `X` has a symmetric `q`-stable law and `X = Y` almost everywhere under `P`, then `Y` has
the same symmetric `q`-stable law. -/
lemma congr (hX : HasSymmetricStableLaw X q c P)
    (h : X =ᵐ[P] Y) : HasSymmetricStableLaw Y q c P := by
  refine ⟨?_⟩
  rw [← Measure.map_congr h]
  exact hX.isSymmetricStable_map

/-- A symmetric `q`-stable random variable has scale parameter zero exactly when it is zero
almost everywhere. -/
lemma scale_eq_zero_iff_ae_eq_zero (hX : HasSymmetricStableLaw X q c P) :
    c = 0 ↔ X =ᵐ[P] 0 := by
  constructor
  · intro hc
    have hmap : P.map X = Measure.dirac 0 := by
      apply hX.isSymmetricStable_map.eq
      rw [hc]
      exact isSymmetricStable_dirac_zero hX.isSymmetricStable_map.index_pos
        hX.isSymmetricStable_map.index_le_two
    change ∀ᵐ x ∂P, X x = 0
    rw [← ae_map_iff (p := fun x : ℝ ↦ x = 0) hX.aemeasurable
      (by simp)]
    rw [hmap]
    simp
  · intro hzero
    letI := hX.isProbabilityMeasure
    have hzeroLaw := hasSymmetricStableLaw_zero (P := P)
      hX.isSymmetricStable_map.index_pos hX.isSymmetricStable_map.index_le_two
    exact (hX.congr hzero).isSymmetricStable_map.scale_eq hzeroLaw.isSymmetricStable_map

/-- If `X` has a symmetric `q`-stable law with scale parameter `c`, then multiplication by `a ∈ ℝ`
gives a symmetric `q`-stable law with scale parameter `c * |a| ^ q`. -/
lemma const_mul (hX : HasSymmetricStableLaw X q c P) (a : ℝ) :
    HasSymmetricStableLaw (fun ω ↦ a * X ω) q (c * ‖a‖₊ ^ q) P := by
  refine ⟨?_⟩
  rw [show (fun ω ↦ a * X ω) = (a * ·) ∘ X from rfl,
    ← AEMeasurable.map_map_of_aemeasurable]
  · exact hX.isSymmetricStable_map.map_mul a
  all_goals fun_prop

/-- If `X` has a symmetric `q`-stable law, then `-X` has the same symmetric `q`-stable law. -/
lemma neg (hX : HasSymmetricStableLaw X q c P) :
    HasSymmetricStableLaw (fun ω ↦ -X ω) q c P := by
  convert hX.const_mul (-1) using 1 <;> simp

end HasSymmetricStableLaw

end ProbabilityTheory
