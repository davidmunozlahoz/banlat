import BanLat.Dual
import BanLat.Operators.Hom
import BanLat.Examples.CofK.Basic
import BanLat.Examples.MofK.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The dual of `C(K, ℝ)` as `M(K)`

For a compact Hausdorff space `K` equipped with its Borel σ-algebra, the
Riesz-Markov-Kakutani theorem identifies the norm dual of `C(K, ℝ)` with the
Banach lattice `M(K)` of regular finite signed Borel measures.

This file provides the statement-level infrastructure for that identification:

* the functional associated to a regular signed measure in `M(K)`;
* the regular finite Borel measure associated to a non-negative functional;
* the element of `M(K)` associated to an arbitrary functional;
* the resulting Banach-lattice equivalence between `M(K)` and `C(K, ℝ)*`.
-/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped CompactlySupported

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- Integration of a continuous function against a finite signed Borel measure,
defined through the Jordan decomposition. -/
noncomputable def signedMeasureIntegral (μ : SignedMeasure K) (f : C(K, ℝ)) : ℝ :=
  ∫ x, f x ∂μ.toJordanDecomposition.posPart -
    ∫ x, f x ∂μ.toJordanDecomposition.negPart

omit [T2Space K] in
/-- A continuous function on a compact space is integrable against any finite
measure. -/
private theorem continuousMap_integrable (f : C(K, ℝ)) (ν : Measure K)
    [IsFiniteMeasure ν] : Integrable (fun x => f x) ν := by
  exact f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f)

/-- The linear functional on `C(K, ℝ)` induced by a finite signed Borel
measure. -/
private noncomputable def signedMeasureLinearMap (μ : SignedMeasure K) :
    C(K, ℝ) →ₗ[ℝ] ℝ where
  toFun f := signedMeasureIntegral μ f
  map_add' := by
    intro f g
    unfold signedMeasureIntegral
    have h₁ : ∫ x, (f + g) x ∂μ.toJordanDecomposition.posPart =
        ∫ x, f x ∂μ.toJordanDecomposition.posPart +
          ∫ x, g x ∂μ.toJordanDecomposition.posPart := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (continuousMap_integrable f _) (continuousMap_integrable g _)
    have h₂ : ∫ x, (f + g) x ∂μ.toJordanDecomposition.negPart =
        ∫ x, f x ∂μ.toJordanDecomposition.negPart +
          ∫ x, g x ∂μ.toJordanDecomposition.negPart := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (continuousMap_integrable f _) (continuousMap_integrable g _)
    rw [h₁, h₂]
    ring
  map_smul' := by
    intro c f
    unfold signedMeasureIntegral
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      integral_const_mul]
    ring

omit [T2Space K] in
/-- The standard operator-norm bound for integration against a signed
measure. -/
private theorem signedMeasureLinearMap_norm_bound (μ : SignedMeasure K)
    (f : C(K, ℝ)) :
    ‖signedMeasureLinearMap μ f‖ ≤ ‖μ‖ * ‖f‖ := by
  rw [show signedMeasureLinearMap μ f = signedMeasureIntegral μ f from rfl]
  unfold signedMeasureIntegral
  have hbound : ∀ x, ‖f x‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f
  have h₁ : ‖∫ x, f x ∂μ.toJordanDecomposition.posPart‖ ≤
      ‖f‖ * (μ.toJordanDecomposition.posPart Set.univ).toReal :=
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)).trans_eq
      (by rw [Measure.real])
  have h₂ : ‖∫ x, f x ∂μ.toJordanDecomposition.negPart‖ ≤
      ‖f‖ * (μ.toJordanDecomposition.negPart Set.univ).toReal :=
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)).trans_eq
      (by rw [Measure.real])
  have hnorm : ‖μ‖ = (μ.toJordanDecomposition.posPart Set.univ).toReal +
      (μ.toJordanDecomposition.negPart Set.univ).toReal := by
    rw [SignedMeasure.norm_def, SignedMeasure.totalVariation, Measure.add_apply,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  calc
    ‖∫ x, f x ∂μ.toJordanDecomposition.posPart -
        ∫ x, f x ∂μ.toJordanDecomposition.negPart‖
      ≤ ‖∫ x, f x ∂μ.toJordanDecomposition.posPart‖ +
          ‖∫ x, f x ∂μ.toJordanDecomposition.negPart‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * (μ.toJordanDecomposition.posPart Set.univ).toReal +
          ‖f‖ * (μ.toJordanDecomposition.negPart Set.univ).toReal :=
        add_le_add h₁ h₂
    _ = ‖μ‖ * ‖f‖ := by
      rw [hnorm]
      ring

/-- The continuous linear functional on `C(K, ℝ)` induced by a finite signed
Borel measure. -/
noncomputable def signedMeasureFunctional (μ : SignedMeasure K) :
    StrongDual ℝ C(K, ℝ) :=
  (signedMeasureLinearMap μ).mkContinuous ‖μ‖
    (signedMeasureLinearMap_norm_bound μ)

omit [T2Space K] in
@[simp]
theorem signedMeasureFunctional_apply (μ : SignedMeasure K) (f : C(K, ℝ)) :
    signedMeasureFunctional μ f = signedMeasureIntegral μ f := rfl

omit [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [T2Space K] in
/-- Each signed measure is the difference of its two Jordan parts viewed as
signed measures. -/
private theorem eq_jordan_diff (μ : SignedMeasure K) :
    μ = μ.toJordanDecomposition.posPart.toSignedMeasure
      - μ.toJordanDecomposition.negPart.toSignedMeasure :=
  (SignedMeasure.toSignedMeasure_toJordanDecomposition μ).symm

omit [T2Space K] in
/-- If a signed measure `μ` decomposes as `α.toSignedMeasure - β.toSignedMeasure`
for finite Borel measures `α, β`, then `signedMeasureIntegral μ f` is the
corresponding difference of integrals. -/
private theorem signedMeasureIntegral_eq_sub_of_eq
    {μ : SignedMeasure K} {α β : Measure K}
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (h : μ = α.toSignedMeasure - β.toSignedMeasure) (f : C(K, ℝ)) :
    signedMeasureIntegral μ f = ∫ x, f x ∂α - ∫ x, f x ∂β := by
  have hjordan :
      μ.toJordanDecomposition.posPart.toSignedMeasure -
        μ.toJordanDecomposition.negPart.toSignedMeasure
      = α.toSignedMeasure - β.toSignedMeasure := by
    rw [show μ.toJordanDecomposition.posPart.toSignedMeasure -
        μ.toJordanDecomposition.negPart.toSignedMeasure
        = μ.toJordanDecomposition.toSignedMeasure from rfl,
      SignedMeasure.toSignedMeasure_toJordanDecomposition, h]
  have hadd : (μ.toJordanDecomposition.posPart + β).toSignedMeasure
      = (α + μ.toJordanDecomposition.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp hjordan
  have hmeas : μ.toJordanDecomposition.posPart + β
      = α + μ.toJordanDecomposition.negPart :=
    Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp hadd
  have hint : ∫ x, f x ∂(μ.toJordanDecomposition.posPart + β)
      = ∫ x, f x ∂(α + μ.toJordanDecomposition.negPart) := by
    rw [hmeas]
  rw [integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _),
    integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _)] at hint
  unfold signedMeasureIntegral
  linarith

omit [T2Space K] in
/-- The signed measure functional is additive. -/
private theorem signedMeasureFunctional_add (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ + ν) =
      signedMeasureFunctional μ + signedMeasureFunctional ν := by
  ext f
  simp only [signedMeasureFunctional_apply, ContinuousLinearMap.add_apply]
  have hsum : (μ + ν : SignedMeasure K) =
      (μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.posPart).toSignedMeasure
      - (μ.toJordanDecomposition.negPart + ν.toJordanDecomposition.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    conv_lhs => rw [eq_jordan_diff μ, eq_jordan_diff ν]
    abel
  rw [signedMeasureIntegral_eq_sub_of_eq hsum f,
    integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _),
    integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _)]
  change _ = signedMeasureIntegral _ _ + signedMeasureIntegral _ _
  unfold signedMeasureIntegral
  ring

omit [CompactSpace K] [BorelSpace K] [T2Space K] in
/-- Integration against `c • μ` scales by `c`. -/
private theorem signedMeasureIntegral_smul (c : ℝ) (μ : SignedMeasure K) (f : C(K, ℝ)) :
    signedMeasureIntegral (c • μ) f = c * signedMeasureIntegral μ f := by
  unfold signedMeasureIntegral
  rw [SignedMeasure.toJordanDecomposition_smul_real]
  rcases lt_or_ge c 0 with hc | hc
  · rw [JordanDecomposition.real_smul_posPart_neg _ _ hc,
      JordanDecomposition.real_smul_negPart_neg _ _ hc,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      NNReal.smul_def, NNReal.smul_def,
      Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ -c), smul_eq_mul, smul_eq_mul]
    ring
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
      JordanDecomposition.real_smul_negPart_nonneg _ _ hc,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      NNReal.smul_def, NNReal.smul_def, Real.coe_toNNReal _ hc, smul_eq_mul, smul_eq_mul]
    ring

omit [T2Space K] in
/-- The signed measure functional is homogeneous. -/
private theorem signedMeasureFunctional_smul (c : ℝ) (μ : SignedMeasure K) :
    signedMeasureFunctional (c • μ) = c • signedMeasureFunctional μ := by
  ext f
  simp only [signedMeasureFunctional_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact signedMeasureIntegral_smul c μ f

omit [T2Space K] in
/-- The signed measure functional of `0` is `0`. -/
private theorem signedMeasureFunctional_zero :
    signedMeasureFunctional (0 : SignedMeasure K) = 0 := by
  ext f
  rw [signedMeasureFunctional_apply, signedMeasureIntegral,
    SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart,
    JordanDecomposition.zero_negPart, integral_zero_measure, sub_zero]
  rfl

omit [T2Space K] in
/-- The signed measure functional commutes with negation. -/
private theorem signedMeasureFunctional_neg (μ : SignedMeasure K) :
    signedMeasureFunctional (-μ) = -signedMeasureFunctional μ := by
  calc
    signedMeasureFunctional (-μ)
      = signedMeasureFunctional ((-1 : ℝ) • μ) := by rw [neg_one_smul]
    _ = (-1 : ℝ) • signedMeasureFunctional μ := signedMeasureFunctional_smul (-1) μ
    _ = -signedMeasureFunctional μ := by
      exact neg_one_smul ℝ (signedMeasureFunctional μ)

omit [T2Space K] in
/-- The signed measure functional is compatible with subtraction. -/
private theorem signedMeasureFunctional_sub (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ - ν) =
      signedMeasureFunctional μ - signedMeasureFunctional ν := by
  rw [sub_eq_add_neg, signedMeasureFunctional_add, signedMeasureFunctional_neg,
    sub_eq_add_neg]

/-- Injectivity of `signedMeasureFunctional` on regular signed measures. -/
private theorem signedMeasureFunctional_injective_of_regular
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular)
    (hfun : signedMeasureFunctional μ = signedMeasureFunctional ν) : μ = ν := by
  haveI := hμ.posPart_regular
  haveI := hμ.negPart_regular
  haveI := hν.posPart_regular
  haveI := hν.negPart_regular
  have hint : ∀ f : C(K, ℝ),
      ∫ x, f x ∂(μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) =
      ∫ x, f x ∂(ν.toJordanDecomposition.posPart + μ.toJordanDecomposition.negPart) := by
    intro f
    have := congrArg (fun ψ : StrongDual ℝ C(K, ℝ) => ψ f) hfun
    simp only [signedMeasureFunctional_apply, signedMeasureIntegral] at this
    rw [integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _),
      integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _)]
    linarith
  have hmeas : μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart =
      ν.toJordanDecomposition.posPart + μ.toJordanDecomposition.negPart := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    exact hint f.toContinuousMap
  have hsigned : μ.toJordanDecomposition.toSignedMeasure =
      ν.toJordanDecomposition.toSignedMeasure := by
    have heqs := Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr hmeas
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at heqs
    have h1 : μ.toJordanDecomposition.toSignedMeasure =
        μ.toJordanDecomposition.posPart.toSignedMeasure -
          μ.toJordanDecomposition.negPart.toSignedMeasure := rfl
    have h2 : ν.toJordanDecomposition.toSignedMeasure =
        ν.toJordanDecomposition.posPart.toSignedMeasure -
          ν.toJordanDecomposition.negPart.toSignedMeasure := rfl
    rw [h1, h2, sub_eq_sub_iff_add_eq_add]
    exact heqs
  rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ,
    ← SignedMeasure.toSignedMeasure_toJordanDecomposition ν, hsigned]

omit [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [T2Space K] in
/-- The Jordan decomposition of `α.toSignedMeasure` is `(α, 0)`. -/
private theorem jordan_of_toSignedMeasure (α : Measure K) [IsFiniteMeasure α] :
    α.toSignedMeasure.toJordanDecomposition =
      { posPart := α
        negPart := 0
        mutuallySingular := Measure.MutuallySingular.zero_right } := by
  apply SignedMeasure.toJordanDecomposition_eq
  change α.toSignedMeasure =
    α.toSignedMeasure - (0 : Measure K).toSignedMeasure
  rw [Measure.toSignedMeasure_zero, sub_zero]

omit [CompactSpace K] [BorelSpace K] [T2Space K] in
/-- A finite regular measure gives a regular signed measure after coercion. -/
  private theorem measure_toSignedMeasure_isRegular {α : Measure K}
    [IsFiniteMeasure α] (hα : α.Regular) :
    α.toSignedMeasure.IsRegular := by
  have hja := jordan_of_toSignedMeasure α
  change α.toSignedMeasure.totalVariation.Regular
  rw [SignedMeasure.totalVariation, hja]
  change (α + 0).Regular
  rw [add_zero]
  exact hα

namespace MofK

/-- The functional on `C(K, ℝ)` associated to a regular finite signed Borel
measure. -/
noncomputable def toDual (μ : MofK K) : StrongDual ℝ C(K, ℝ) :=
  signedMeasureFunctional μ.1

@[simp]
theorem toDual_apply (μ : MofK K) (f : C(K, ℝ)) :
    μ.toDual f = signedMeasureIntegral μ.1 f := rfl

end MofK

namespace StrongDual

/-- A non-negative functional on `C(K, ℝ)`, viewed as a positive linear map on
compactly supported continuous functions. Since `K` is compact, these spaces
agree. -/
private noncomputable def toPositiveCompactlySupportedMap
    (φ : StrongDual ℝ C(K, ℝ)) (hφ : 0 ≤ φ) :
    (K →C_c ℝ) →ₚ[ℝ] ℝ := by
  exact PositiveLinearMap.mk₀
    { toFun := fun f => φ f.toContinuousMap
      map_add' := fun f g => by
        change φ (f + g).toContinuousMap = φ f.toContinuousMap + φ g.toContinuousMap
        rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap from rfl,
          map_add]
      map_smul' := fun c f => by
        change φ (c • f).toContinuousMap = c • φ f.toContinuousMap
        rw [show (c • f).toContinuousMap = c • f.toContinuousMap from rfl, map_smul] }
    (fun f hf => by
      have hφ' : 0 ≤ StrongDual.toOrderDualSpace φ := by
        change StrongDual.toOrderDualSpace 0 ≤ StrongDual.toOrderDualSpace φ at hφ
        simpa using hφ
      rw [OrderDualSpace.nonneg_iff] at hφ'
      change 0 ≤ φ f.toContinuousMap
      exact hφ' f.toContinuousMap (by
        intro x
        exact hf x))

/-- The regular finite Borel measure representing a non-negative functional on
`C(K, ℝ)`. -/
noncomputable def measureOfNonneg (φ : StrongDual ℝ C(K, ℝ)) (hφ : 0 ≤ φ) :
    Measure K :=
  RealRMK.rieszMeasure (toPositiveCompactlySupportedMap φ hφ)

instance instIsFiniteMeasureMeasureOfNonneg
    (φ : StrongDual ℝ C(K, ℝ)) (hφ : 0 ≤ φ) :
    IsFiniteMeasure (measureOfNonneg φ hφ) := by
  unfold measureOfNonneg
  infer_instance

instance instRegularMeasureOfNonneg
    (φ : StrongDual ℝ C(K, ℝ)) (hφ : 0 ≤ φ) :
    (measureOfNonneg φ hφ).Regular := by
  unfold measureOfNonneg
  infer_instance

/-- Integration against the representing measure recovers a non-negative
functional. -/
theorem integral_measureOfNonneg (φ : StrongDual ℝ C(K, ℝ)) (hφ : 0 ≤ φ)
    (f : C(K, ℝ)) :
    ∫ x, f x ∂measureOfNonneg φ hφ = φ f := by
  have h := RealRMK.integral_rieszMeasure (toPositiveCompactlySupportedMap φ hφ)
    (CompactlySupportedContinuousMap.continuousMapEquiv (β := ℝ) f)
  simpa [measureOfNonneg, CompactlySupportedContinuousMap.continuousMapEquiv] using h

/-- The regular finite signed Borel measure corresponding to a continuous
functional on `C(K, ℝ)`. -/
noncomputable def toSignedMeasure (φ : StrongDual ℝ C(K, ℝ)) :
    SignedMeasure K :=
  (measureOfNonneg φ⁺ (posPart_nonneg _)).toSignedMeasure -
    (measureOfNonneg φ⁻ (negPart_nonneg _)).toSignedMeasure

/-- The signed measure associated to a functional is regular. -/
theorem isRegular_toSignedMeasure (φ : StrongDual ℝ C(K, ℝ)) :
    (toSignedMeasure φ).IsRegular := by
  exact SignedMeasure.IsRegular.sub
    (measure_toSignedMeasure_isRegular
      (α := measureOfNonneg φ⁺ (posPart_nonneg _)) inferInstance)
    (measure_toSignedMeasure_isRegular
      (α := measureOfNonneg φ⁻ (negPart_nonneg _)) inferInstance)

/-- The element of `M(K)` corresponding to a continuous functional on
`C(K, ℝ)`. -/
noncomputable def toMofK (φ : StrongDual ℝ C(K, ℝ)) : MofK K :=
  ⟨toSignedMeasure φ, isRegular_toSignedMeasure φ⟩

@[simp]
theorem toMofK_coe (φ : StrongDual ℝ C(K, ℝ)) :
    ((toMofK φ : MofK K) : SignedMeasure K) = toSignedMeasure φ := rfl

/-- Integration against the signed measure associated to a functional recovers
that functional. -/
theorem toSignedMeasure_apply (φ : StrongDual ℝ C(K, ℝ)) (f : C(K, ℝ)) :
    signedMeasureIntegral (toSignedMeasure φ) f = φ f := by
  rw [signedMeasureIntegral_eq_sub_of_eq (rfl : toSignedMeasure φ = _) f,
    integral_measureOfNonneg, integral_measureOfNonneg]
  exact congrArg (fun ψ : StrongDual ℝ C(K, ℝ) => ψ f) (posPart_sub_negPart φ)

@[simp]
theorem toDual_toMofK (φ : StrongDual ℝ C(K, ℝ)) :
    (toMofK φ).toDual = φ := by
  ext f
  rw [MofK.toDual_apply, toMofK_coe, toSignedMeasure_apply]

end StrongDual

omit [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [T2Space K] in
/-- For a non-negative signed measure, the Jordan negative part vanishes. -/
private theorem jordan_negPart_eq_zero
    {μ : SignedMeasure K} (hμ : 0 ≤ μ) :
    μ.toJordanDecomposition.negPart = 0 := by
  have h := SignedMeasure.nonneg_iff_negPart_eq_zero.mp hμ
  have h1 : (μ.toJordanDecomposition.negPart).toSignedMeasure =
      (0 : Measure K).toSignedMeasure := by
    rw [Measure.toSignedMeasure_zero]
    exact h
  exact Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp h1

omit [T2Space K] in
/-- A non-negative signed measure induces a non-negative functional. -/
private theorem signedMeasureFunctional_nonneg
    {μ : SignedMeasure K} (hμ : 0 ≤ μ) :
    0 ≤ signedMeasureFunctional μ := by
  have hzero : μ.toJordanDecomposition.negPart = 0 := jordan_negPart_eq_zero hμ
  change 0 ≤ StrongDual.toOrderDualSpace (signedMeasureFunctional μ)
  rw [OrderDualSpace.nonneg_iff]
  intro f hf
  rw [StrongDual.toOrderDualSpace_apply, signedMeasureFunctional_apply,
    signedMeasureIntegral, hzero, integral_zero_measure, sub_zero]
  exact integral_nonneg (fun x => ContinuousMap.le_def.mp hf x)

/-- The Jordan decomposition of `(measureOfNonneg φ hφ).toSignedMeasure`
is `(measureOfNonneg φ hφ, 0)`. -/
private theorem jordan_of_measureOfNonneg_toSignedMeasure
    (φ : StrongDual ℝ C(K, ℝ)) (hφ : 0 ≤ φ) :
    ((StrongDual.measureOfNonneg φ hφ).toSignedMeasure).toJordanDecomposition =
      { posPart := StrongDual.measureOfNonneg φ hφ
        negPart := 0
        mutuallySingular := Measure.MutuallySingular.zero_right } := by
  apply SignedMeasure.toJordanDecomposition_eq
  change (StrongDual.measureOfNonneg φ hφ).toSignedMeasure =
    (StrongDual.measureOfNonneg φ hφ).toSignedMeasure - (0 : Measure K).toSignedMeasure
  rw [Measure.toSignedMeasure_zero, sub_zero]

/-- A non-negative functional corresponds to a non-negative signed measure. -/
private theorem toSignedMeasure_nonneg
    {φ : StrongDual ℝ C(K, ℝ)} (hφ : 0 ≤ φ) :
    0 ≤ StrongDual.toSignedMeasure φ := by
  set ν : SignedMeasure K := (StrongDual.measureOfNonneg φ hφ).toSignedMeasure with hν
  have hν_nonneg : 0 ≤ ν := Measure.zero_le_toSignedMeasure _
  have hjd := jordan_of_measureOfNonneg_toSignedMeasure φ hφ
  have hfunc : signedMeasureFunctional ν = φ := by
    ext g
    rw [signedMeasureFunctional_apply, signedMeasureIntegral]
    change ∫ x, g x ∂ν.toJordanDecomposition.posPart -
        ∫ x, g x ∂ν.toJordanDecomposition.negPart = φ g
    rw [show ν.toJordanDecomposition.posPart = StrongDual.measureOfNonneg φ hφ from
        by simpa [hν] using congrArg JordanDecomposition.posPart hjd,
      show ν.toJordanDecomposition.negPart = 0 from
        by simpa [hν] using congrArg JordanDecomposition.negPart hjd,
      integral_zero_measure, sub_zero]
    exact StrongDual.integral_measureOfNonneg φ hφ g
  have hν_reg : ν.IsRegular := by
    change ν.totalVariation.Regular
    rw [hν, SignedMeasure.totalVariation, hjd]
    change (StrongDual.measureOfNonneg φ hφ + 0).Regular
    rw [add_zero]
    infer_instance
  have heq : StrongDual.toSignedMeasure φ = ν :=
    signedMeasureFunctional_injective_of_regular
      (StrongDual.isRegular_toSignedMeasure _) hν_reg
      (by
        calc
          signedMeasureFunctional (StrongDual.toSignedMeasure φ)
            = φ := by
                simpa [MofK.toDual, StrongDual.toMofK] using StrongDual.toDual_toMofK φ
          _ = signedMeasureFunctional ν := hfunc.symm)
  rw [heq]
  exact hν_nonneg

/-- Passing to the dual functional and back recovers a regular signed measure. -/
private theorem toSignedMeasure_signedMeasureFunctional
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    StrongDual.toSignedMeasure (signedMeasureFunctional μ) = μ :=
  signedMeasureFunctional_injective_of_regular
    (StrongDual.isRegular_toSignedMeasure _) hμ
    (by
      simpa [MofK.toDual, StrongDual.toMofK] using
        StrongDual.toDual_toMofK (signedMeasureFunctional μ))

/-- For regular signed measures, positivity is detected by the associated
functional. -/
private theorem signedMeasureFunctional_nonneg_iff
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    0 ≤ signedMeasureFunctional μ ↔ 0 ≤ μ := by
  refine ⟨fun h => ?_, signedMeasureFunctional_nonneg⟩
  have := toSignedMeasure_nonneg h
  rwa [toSignedMeasure_signedMeasureFunctional hμ] at this

/-- For regular signed measures, order is detected by the associated
functional. -/
private theorem signedMeasureFunctional_le_iff
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular) :
    signedMeasureFunctional μ ≤ signedMeasureFunctional ν ↔ μ ≤ ν := by
  constructor
  · intro h
    have h' : StrongDual.toOrderDualSpace (signedMeasureFunctional μ) ≤
        StrongDual.toOrderDualSpace (signedMeasureFunctional ν) := by
      simpa using h
    rw [OrderDualSpace.le_iff] at h'
    have hnonneg_fun : 0 ≤ signedMeasureFunctional (ν - μ) := by
      change 0 ≤ StrongDual.toOrderDualSpace (signedMeasureFunctional (ν - μ))
      rw [OrderDualSpace.nonneg_iff]
      intro f hf
      have hfg := h' f hf
      rw [StrongDual.toOrderDualSpace_apply, signedMeasureFunctional_sub,
        ContinuousLinearMap.sub_apply]
      exact sub_nonneg.mpr (by simpa [StrongDual.toOrderDualSpace_apply] using hfg)
    have hnonneg_meas : 0 ≤ ν - μ :=
      (signedMeasureFunctional_nonneg_iff (SignedMeasure.IsRegular.sub hν hμ)).mp hnonneg_fun
    exact sub_nonneg.mp hnonneg_meas
  · intro h
    have hnonneg_fun : 0 ≤ signedMeasureFunctional (ν - μ) :=
      signedMeasureFunctional_nonneg (sub_nonneg.mpr h)
    change StrongDual.toOrderDualSpace (signedMeasureFunctional μ) ≤
      StrongDual.toOrderDualSpace (signedMeasureFunctional ν)
    rw [OrderDualSpace.le_iff]
    intro f hf
    have hfun' : 0 ≤ StrongDual.toOrderDualSpace (signedMeasureFunctional (ν - μ)) := by
      simpa using hnonneg_fun
    rw [OrderDualSpace.nonneg_iff] at hfun'
    have hfg := hfun' f hf
    have hfg' : 0 ≤ (signedMeasureFunctional ν) f - (signedMeasureFunctional μ) f := by
      simpa [StrongDual.toOrderDualSpace_apply, signedMeasureFunctional_sub,
        ContinuousLinearMap.sub_apply] using hfg
    exact sub_nonneg.mp hfg'

/-- The positive part of a regular signed measure is regular. -/
private theorem isRegular_posPart {s : SignedMeasure K} (hs : s.IsRegular) :
    s⁺.IsRegular := by
  have key : s + |s| = (2 : ℕ) • s⁺ := add_abs_eq_two_nsmul_posPart s
  have h2 : s⁺ = (2 : ℝ)⁻¹ • (s + |s|) := by
    rw [key, ← Nat.cast_smul_eq_nsmul ℝ 2]
    simp only [Nat.cast_ofNat, smul_smul]
    rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  rw [h2]
  exact SignedMeasure.IsRegular.smul _
    (SignedMeasure.IsRegular.add hs (MeasureTheory.SignedMeasure.IsRegular.abs hs))

/-- Suprema of regular signed measures are regular. -/
private theorem isRegular_sup {μ ν : SignedMeasure K}
    (hμ : μ.IsRegular) (hν : ν.IsRegular) : (μ ⊔ ν).IsRegular := by
  rw [sup_eq_add_posPart]
  exact SignedMeasure.IsRegular.add hμ
    (isRegular_posPart (SignedMeasure.IsRegular.sub hν hμ))

/-- Infima of regular signed measures are regular. -/
private theorem isRegular_inf {μ ν : SignedMeasure K}
    (hμ : μ.IsRegular) (hν : ν.IsRegular) : (μ ⊓ ν).IsRegular := by
  rw [inf_eq_sub_posPart]
  exact SignedMeasure.IsRegular.sub hμ
    (isRegular_posPart (SignedMeasure.IsRegular.sub hμ hν))

/-- The signed measure functional preserves suprema on regular signed measures. -/
private theorem signedMeasureFunctional_sup
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular) :
    signedMeasureFunctional (μ ⊔ ν) =
      signedMeasureFunctional μ ⊔ signedMeasureFunctional ν := by
  set F : StrongDual ℝ C(K, ℝ) := signedMeasureFunctional μ ⊔ signedMeasureFunctional ν with hF
  set σ := StrongDual.toSignedMeasure F with hσ
  have hσ_reg : σ.IsRegular := by
    rw [hσ]
    exact StrongDual.isRegular_toSignedMeasure F
  have hSσ : signedMeasureFunctional σ = F := by
    simpa [hσ, MofK.toDual, StrongDual.toMofK] using StrongDual.toDual_toMofK F
  apply le_antisymm
  · have hle_left : signedMeasureFunctional μ ≤ F := by
      change StrongDual.toOrderDualSpace (signedMeasureFunctional μ) ≤
        StrongDual.toOrderDualSpace F
      rw [hF]
      exact le_sup_left
    have hle_right : signedMeasureFunctional ν ≤ F := by
      change StrongDual.toOrderDualSpace (signedMeasureFunctional ν) ≤
        StrongDual.toOrderDualSpace F
      rw [hF]
      exact le_sup_right
    have h1 : μ ≤ σ := (signedMeasureFunctional_le_iff hμ hσ_reg).mp (by rw [hSσ]; exact hle_left)
    have h2 : ν ≤ σ := (signedMeasureFunctional_le_iff hν hσ_reg).mp (by rw [hSσ]; exact hle_right)
    have hsup : μ ⊔ ν ≤ σ := by
      change μ ⊔ ν ≤ σ
      exact (sup_le_iff.mpr ⟨h1, h2⟩)
    have h4 := (signedMeasureFunctional_le_iff (isRegular_sup hμ hν) hσ_reg).mpr
      hsup
    rw [hSσ] at h4
    exact h4
  · rw [hF]
    have hleft : signedMeasureFunctional μ ≤ signedMeasureFunctional (μ ⊔ ν) :=
      (signedMeasureFunctional_le_iff hμ (isRegular_sup hμ hν)).mpr le_sup_left
    have hright : signedMeasureFunctional ν ≤ signedMeasureFunctional (μ ⊔ ν) :=
      (signedMeasureFunctional_le_iff hν (isRegular_sup hμ hν)).mpr le_sup_right
    change StrongDual.toOrderDualSpace
        (signedMeasureFunctional μ ⊔ signedMeasureFunctional ν) ≤
      StrongDual.toOrderDualSpace (signedMeasureFunctional (μ ⊔ ν))
    change (StrongDual.toOrderDualSpace (signedMeasureFunctional μ) ⊔
        StrongDual.toOrderDualSpace (signedMeasureFunctional ν)) ≤
      StrongDual.toOrderDualSpace (signedMeasureFunctional (μ ⊔ ν))
    exact sup_le (by simpa using hleft) (by simpa using hright)

/-- The signed measure functional preserves infima on regular signed measures. -/
private theorem signedMeasureFunctional_inf
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular) :
    signedMeasureFunctional (μ ⊓ ν) =
      signedMeasureFunctional μ ⊓ signedMeasureFunctional ν := by
  have hid : μ ⊓ ν = μ + ν - (μ ⊔ ν) := eq_sub_of_add_eq (inf_add_sup μ ν)
  rw [hid, signedMeasureFunctional_sub, signedMeasureFunctional_add,
    signedMeasureFunctional_sup hμ hν]
  exact (eq_sub_of_add_eq (inf_add_sup (signedMeasureFunctional μ)
    (signedMeasureFunctional ν))).symm

/-- The signed measure functional preserves modulus on regular signed measures. -/
private theorem signedMeasureFunctional_abs
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    |signedMeasureFunctional μ| = signedMeasureFunctional |μ| := by
  have hpos : (signedMeasureFunctional μ)⁺ = signedMeasureFunctional μ⁺ := by
    rw [posPart_def, posPart_def,
      signedMeasureFunctional_sup hμ SignedMeasure.IsRegular.zero,
      signedMeasureFunctional_zero]
  have hneg : (signedMeasureFunctional μ)⁻ = signedMeasureFunctional μ⁻ := by
    rw [negPart_def, negPart_def,
      signedMeasureFunctional_sup (SignedMeasure.IsRegular.neg hμ)
        SignedMeasure.IsRegular.zero,
      signedMeasureFunctional_neg, signedMeasureFunctional_zero]
  rw [← posPart_add_negPart (signedMeasureFunctional μ), hpos, hneg,
    ← signedMeasureFunctional_add, posPart_add_negPart]

omit [T2Space K] in
/-- For a non-negative signed measure, the associated functional has the same
norm as the measure. -/
private theorem norm_signedMeasureFunctional_of_nonneg
    {μ : SignedMeasure K} (hμ : 0 ≤ μ) :
    ‖signedMeasureFunctional μ‖ = ‖μ‖ := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f =>
      signedMeasureLinearMap_norm_bound μ f)
    ?_
  by_cases hK : Nonempty K
  · letI : Nonempty K := hK
    have hzero : μ.toJordanDecomposition.negPart = 0 := jordan_negPart_eq_zero hμ
    have h1 : (1 : C(K, ℝ)) = ContinuousMap.const K 1 := rfl
    have hone_norm : ‖(1 : C(K, ℝ))‖ = 1 := by
      exact (norm_one : ‖(1 : C(K, ℝ))‖ = 1)
    have hjd : μ.toJordanDecomposition =
        ⟨μ.toJordanDecomposition.posPart, 0,
          Measure.MutuallySingular.zero_right⟩ := by
      apply JordanDecomposition.ext <;> simp [hzero]
    have heq : (μ.toJordanDecomposition.posPart.toSignedMeasure : SignedMeasure K) = μ := by
      rw [show μ.toJordanDecomposition.posPart.toSignedMeasure
          = μ.toJordanDecomposition.toSignedMeasure from by
            conv_rhs => rw [hjd]
            change _ = (_ : Measure K).toSignedMeasure - (0 : Measure K).toSignedMeasure
            rw [Measure.toSignedMeasure_zero, sub_zero],
        SignedMeasure.toSignedMeasure_toJordanDecomposition]
    have hval : signedMeasureFunctional μ 1 = ‖μ‖ := by
      rw [signedMeasureFunctional_apply, signedMeasureIntegral, hzero,
        integral_zero_measure, sub_zero, h1]
      simp only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one]
      rw [SignedMeasure.norm_of_nonneg hμ]
      conv_rhs => rw [← heq]
      rw [Measure.toSignedMeasure_apply, if_pos MeasurableSet.univ]
    have hbound : ‖μ‖ = ‖signedMeasureFunctional μ 1‖ := by
      rw [hval, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hbound]
    calc
      ‖signedMeasureFunctional μ 1‖
        ≤ ‖signedMeasureFunctional μ‖ * ‖(1 : C(K, ℝ))‖ :=
          (signedMeasureFunctional μ).le_opNorm 1
      _ = ‖signedMeasureFunctional μ‖ := by rw [hone_norm, mul_one]
  · letI : IsEmpty K := not_nonempty_iff.mp hK
    have hnorm_zero : ‖μ‖ = 0 := by
      rw [SignedMeasure.norm_of_nonneg hμ]
      have h_univ : (Set.univ : Set K) = ∅ := by
        ext x
        exact isEmptyElim x
      simp [h_univ]
    rw [hnorm_zero]
    exact norm_nonneg (signedMeasureFunctional μ)

/-- The signed measure functional preserves the total variation norm on regular
signed measures. -/
private theorem norm_signedMeasureFunctional
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    ‖signedMeasureFunctional μ‖ = ‖μ‖ := by
  rw [← norm_abs_eq_norm (signedMeasureFunctional μ),
    signedMeasureFunctional_abs hμ,
    norm_signedMeasureFunctional_of_nonneg (abs_nonneg μ), norm_abs_eq_norm]

namespace MofK

/-- Passing from a regular finite signed Borel measure to its dual functional
and back recovers the original measure. -/
@[simp]
theorem toMofK_toDual (μ : MofK K) :
    StrongDual.toMofK μ.toDual = μ := by
  apply Subtype.ext
  exact toSignedMeasure_signedMeasureFunctional μ.property

/-- The Riesz-Markov-Kakutani identification `M(K) ≃ C(K, ℝ)*`. -/
noncomputable def dualEquiv :
    BanachLatEquiv (MofK K) (StrongDual ℝ C(K, ℝ)) where
  toLinearEquiv :=
    { toFun := toDual
      invFun := StrongDual.toMofK
      left_inv := by
        intro μ
        exact toMofK_toDual μ
      right_inv := by
        intro φ
        exact StrongDual.toDual_toMofK φ
      map_add' := by
        intro μ ν
        simpa [MofK.toDual] using signedMeasureFunctional_add μ.1 ν.1
      map_smul' := by
        intro c μ
        simpa [MofK.toDual] using signedMeasureFunctional_smul c μ.1 }
  norm_map' := by
    intro μ
    simpa [MofK.toDual] using norm_signedMeasureFunctional μ.property
  map_sup' := by
    intro μ ν
    simpa [MofK.toDual] using signedMeasureFunctional_sup μ.property ν.property
  map_inf' := by
    intro μ ν
    simpa [MofK.toDual] using signedMeasureFunctional_inf μ.property ν.property

@[simp]
theorem dualEquiv_apply (μ : MofK K) :
    dualEquiv μ = μ.toDual := rfl

end MofK
