import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-!
# Regularity of signed measures

For a compact Hausdorff space `K` with its Borel σ-algebra, a signed measure is
**regular** if its total-variation measure is a regular Borel measure. This file
defines `SignedMeasure.IsRegular` and proves that regularity is preserved by the
linear operations (addition, scalar multiplication, negation, subtraction).
-/

open MeasureTheory Set

/-! ### Preliminary helpers on regularity of measures -/

/-- On a compact Hausdorff Borel space, if `μ + ν` is regular (with `μ`, `ν` finite),
then `μ` itself is regular. -/
private lemma MeasureTheory.Measure.Regular.of_add_right {K : Type*}
    [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ ν : Measure K} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : (μ + ν).Regular) : μ.Regular := by
  haveI := h
  haveI : Measure.InnerRegularCompactLTTop μ := by
    refine ⟨fun A hA r hr => ?_⟩
    obtain ⟨hA_meas, hA_fin⟩ := hA
    have hν_fin : ν A ≠ ⊤ := measure_ne_top _ _
    have h_add : (μ + ν) A = μ A + ν A := Measure.add_apply _ _ _
    have h_addA_fin : (μ + ν) A ≠ ⊤ := by
      rw [h_add]; exact ENNReal.add_ne_top.mpr ⟨hA_fin, hν_fin⟩
    have h_rν_lt : r + ν A < (μ + ν) A := by
      rw [h_add]; exact ENNReal.add_lt_add_right hν_fin hr
    obtain ⟨K₀, hK₀A, hK₀, hK₀_mass⟩ :=
      Measure.InnerRegularCompactLTTop.innerRegular (μ := μ + ν)
        ⟨hA_meas, h_addA_fin⟩ _ h_rν_lt
    refine ⟨K₀, hK₀A, hK₀, ?_⟩
    have h_addK : (μ + ν) K₀ = μ K₀ + ν K₀ := Measure.add_apply _ _ _
    have hνK_le_νA : ν K₀ ≤ ν A := measure_mono hK₀A
    have h1 : r + ν A < μ K₀ + ν K₀ := h_addK ▸ hK₀_mass
    have h2 : μ K₀ + ν K₀ ≤ μ K₀ + ν A := by gcongr
    exact (ENNReal.add_lt_add_iff_right hν_fin).mp (lt_of_lt_of_le h1 h2)
  infer_instance

/-- On a compact Hausdorff Borel space, if `μ` and `ν` are both regular, so is `μ - ν`. -/
private lemma MeasureTheory.Measure.Regular.sub {K : Type*} [TopologicalSpace K] [T2Space K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ ν : Measure K} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.Regular) (_hν : ν.Regular) : (μ - ν).Regular := by
  haveI := hμ
  obtain ⟨s, hs⟩ := MeasureTheory.exists_isHahnDecomposition μ ν
  have hs_meas : MeasurableSet s := hs.measurableSet
  have h_subzero : (μ - ν).restrict s = 0 := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hs_meas]
    exact Measure.sub_eq_zero_of_le hs.le_on
  have h_le_on_compl : ν.restrict sᶜ ≤ μ.restrict sᶜ := hs.compl.le_on
  have h_eq : (μ - ν) + ν.restrict sᶜ = μ.restrict sᶜ := by
    have h_restrict_sub : (μ - ν).restrict sᶜ = μ.restrict sᶜ - ν.restrict sᶜ :=
      Measure.restrict_sub_eq_restrict_sub_restrict hs_meas.compl
    have h_sub_add : (μ - ν).restrict sᶜ + ν.restrict sᶜ = μ.restrict sᶜ := by
      rw [h_restrict_sub]; exact Measure.sub_add_cancel_of_le h_le_on_compl
    have hμν_eq : μ - ν = (μ - ν).restrict sᶜ := by
      conv_lhs =>
        rw [← Measure.restrict_add_restrict_compl (μ := μ - ν) hs_meas, h_subzero, zero_add]
    rw [hμν_eq]; exact h_sub_add
  haveI : (μ.restrict sᶜ).Regular :=
    Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)
  haveI : ((μ - ν) + ν.restrict sᶜ).Regular := h_eq ▸ this
  exact Measure.Regular.of_add_right this

/-- If a finite non-negative measure can be uniformly approximated by regular finite
measures up to arbitrary precision, then it is itself regular. -/
lemma MeasureTheory.Measure.Regular.of_uniform_approx {K : Type*}
    [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ : Measure K} [IsFiniteMeasure μ]
    (h : ∀ ε : ℝ, 0 < ε → ∃ ν : Measure K,
      IsFiniteMeasure ν ∧ ν.Regular ∧
        ∀ E : Set K, MeasurableSet E → |(ν E).toReal - (μ E).toReal| < ε) :
    μ.Regular := by
  haveI : Measure.InnerRegularCompactLTTop μ := by
    refine ⟨fun A hA r hr => ?_⟩
    obtain ⟨hA_meas, hA_fin⟩ := hA
    have hr_fin : r ≠ ⊤ := (hr.trans_le le_top).ne
    have hμA_lt : r.toReal < (μ A).toReal := ENNReal.toReal_strict_mono hA_fin hr
    have hr_nn : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    set δ : ℝ := ((μ A).toReal - r.toReal) / 3 with hδ_def
    have hδ_pos : 0 < δ := div_pos (sub_pos.mpr hμA_lt) (by norm_num)
    obtain ⟨ν, _hν_fin, hν_reg, hν⟩ := h δ hδ_pos
    haveI := hν_reg
    have hνA_close : |(ν A).toReal - (μ A).toReal| < δ := hν A hA_meas
    have hνA_lt : (ν A).toReal > r.toReal + 2 * δ := by
      have h := abs_lt.mp hνA_close
      have : (μ A).toReal = r.toReal + 3 * δ := by rw [hδ_def]; ring
      linarith [h.1, h.2]
    have hνA_fin : ν A ≠ ⊤ := measure_ne_top _ _
    have hr_plus_δ_lt : ENNReal.ofReal (r.toReal + δ) < ν A := by
      have h_re : (ν A).toReal > r.toReal + δ := by linarith
      rw [show ν A = ENNReal.ofReal (ν A).toReal from
          (ENNReal.ofReal_toReal hνA_fin).symm]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith [hr_nn])).mpr h_re
    obtain ⟨K₀, hK₀A, hK₀, hK₀_mass⟩ :=
      Measure.InnerRegularCompactLTTop.innerRegular (μ := ν)
        ⟨hA_meas, hνA_fin⟩ _ hr_plus_δ_lt
    refine ⟨K₀, hK₀A, hK₀, ?_⟩
    have hK₀_meas : MeasurableSet K₀ := hK₀.measurableSet
    have hνK₀_close : |(ν K₀).toReal - (μ K₀).toReal| < δ := hν K₀ hK₀_meas
    have hK_fin : ν K₀ ≠ ⊤ := measure_ne_top _ _
    have hνK₀_real : (ν K₀).toReal > r.toReal + δ :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hr_nn]) hK_fin).mp hK₀_mass
    have hμK₀_real : (μ K₀).toReal > r.toReal := by
      have h := abs_lt.mp hνK₀_close
      linarith [h.1, h.2]
    have hμK₀_fin : μ K₀ ≠ ⊤ := measure_ne_top _ _
    rwa [← ENNReal.toReal_lt_toReal hr_fin hμK₀_fin]
  infer_instance

namespace MeasureTheory
namespace SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-! ### Regularity of a signed measure -/

/-- A signed measure is **regular** if its total-variation measure is a regular
Borel measure. Equivalently, both Jordan parts are regular. -/
def IsRegular (s : SignedMeasure K) : Prop :=
  s.totalVariation.Regular

/-- Construct `IsRegular` from regularity of the two Jordan parts. -/
private theorem IsRegular.of_jordan_parts {s : SignedMeasure K}
    [s.toJordanDecomposition.posPart.Regular]
    [s.toJordanDecomposition.negPart.Regular] : s.IsRegular := by
  change (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).Regular
  infer_instance

/-- The positive Jordan part of a regular signed measure is a regular
measure. -/
theorem IsRegular.posPart_regular {s : SignedMeasure K} (hs : s.IsRegular) :
    s.toJordanDecomposition.posPart.Regular :=
  Measure.Regular.of_add_right hs

/-- The negative Jordan part of a regular signed measure is a regular
measure. -/
theorem IsRegular.negPart_regular {s : SignedMeasure K} (hs : s.IsRegular) :
    s.toJordanDecomposition.negPart.Regular := by
  have h : (s.toJordanDecomposition.negPart +
      s.toJordanDecomposition.posPart).Regular := by rw [add_comm]; exact hs
  exact Measure.Regular.of_add_right h

namespace IsRegular

omit [T2Space K] [CompactSpace K] [BorelSpace K] in
/-- The zero signed measure is regular. -/
theorem zero : (0 : SignedMeasure K).IsRegular := by
  change (0 : SignedMeasure K).totalVariation.Regular
  rw [totalVariation_zero]; infer_instance

omit [T2Space K] [CompactSpace K] [BorelSpace K] in
/-- The negative of a regular signed measure is regular. -/
theorem neg {s : SignedMeasure K} (hs : s.IsRegular) : (-s).IsRegular := by
  change (-s).totalVariation.Regular
  rw [SignedMeasure.totalVariation_neg]; exact hs

/-- The sum of two regular signed measures is regular. -/
theorem add {s t : SignedMeasure K} (hs : s.IsRegular) (ht : t.IsRegular) :
    (s + t).IsRegular := by
  haveI := hs.posPart_regular
  haveI := hs.negPart_regular
  haveI := ht.posPart_regular
  haveI := ht.negPart_regular
  set μ := s.toJordanDecomposition.posPart + t.toJordanDecomposition.posPart
  set ν := s.toJordanDecomposition.negPart + t.toJordanDecomposition.negPart
  have hst_eq : s + t = μ.toSignedMeasure - ν.toSignedMeasure := by
    have hs_eq : s = s.toJordanDecomposition.posPart.toSignedMeasure -
        s.toJordanDecomposition.negPart.toSignedMeasure :=
      s.toSignedMeasure_toJordanDecomposition.symm
    have ht_eq : t = t.toJordanDecomposition.posPart.toSignedMeasure -
        t.toJordanDecomposition.negPart.toSignedMeasure :=
      t.toSignedMeasure_toJordanDecomposition.symm
    change _ = (s.toJordanDecomposition.posPart + t.toJordanDecomposition.posPart).toSignedMeasure -
        (s.toJordanDecomposition.negPart + t.toJordanDecomposition.negPart).toSignedMeasure
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    conv_lhs => rw [hs_eq, ht_eq]
    abel
  have hJD : (s + t).toJordanDecomposition =
      Measure.jordanDecompositionOfToSignedMeasureSub μ ν := by
    refine toJordanDecomposition_eq ?_
    rw [Measure.jordanDecompositionOfToSignedMeasureSub_toSignedMeasure, ← hst_eq]
  haveI : (s + t).toJordanDecomposition.posPart.Regular := by
    rw [hJD]; exact Measure.Regular.sub inferInstance inferInstance
  haveI : (s + t).toJordanDecomposition.negPart.Regular := by
    rw [hJD]; exact Measure.Regular.sub inferInstance inferInstance
  exact of_jordan_parts

/-- A scalar multiple of a regular signed measure is regular. -/
theorem smul (c : ℝ) {s : SignedMeasure K} (hs : s.IsRegular) :
    (c • s).IsRegular := by
  haveI := hs.posPart_regular
  haveI := hs.negPart_regular
  rcases lt_or_ge c 0 with hc | hc
  · haveI : (c • s).toJordanDecomposition.posPart.Regular := by
      rw [toJordanDecomposition_smul_real,
          JordanDecomposition.real_smul_posPart_neg _ _ hc]
      exact Measure.Regular.smul_nnreal _
    haveI : (c • s).toJordanDecomposition.negPart.Regular := by
      rw [toJordanDecomposition_smul_real,
          JordanDecomposition.real_smul_negPart_neg _ _ hc]
      exact Measure.Regular.smul_nnreal _
    exact of_jordan_parts
  · haveI : (c • s).toJordanDecomposition.posPart.Regular := by
      rw [toJordanDecomposition_smul_real,
          JordanDecomposition.real_smul_posPart_nonneg _ _ hc]
      exact Measure.Regular.smul_nnreal _
    haveI : (c • s).toJordanDecomposition.negPart.Regular := by
      rw [toJordanDecomposition_smul_real,
          JordanDecomposition.real_smul_negPart_nonneg _ _ hc]
      exact Measure.Regular.smul_nnreal _
    exact of_jordan_parts

/-- The difference of two regular signed measures is regular. -/
theorem sub {s t : SignedMeasure K} (hs : s.IsRegular) (ht : t.IsRegular) :
    (s - t).IsRegular := by
  rw [sub_eq_add_neg]; exact IsRegular.add hs (IsRegular.neg ht)

end IsRegular

end SignedMeasure
end MeasureTheory
