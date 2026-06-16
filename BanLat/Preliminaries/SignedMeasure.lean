import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# Measure-theoretic facts about signed measures

This file collects measure-theoretic facts about
`MeasureTheory.SignedMeasure.totalVariation` and the Jordan decomposition that
are used to put a Banach lattice structure on the space of finite signed
measures (see `BanLat.Examples.MofK`).
-/

open scoped ENNReal NNReal

namespace MeasureTheory
namespace SignedMeasure

variable {α : Type*} [MeasurableSpace α]

/-! ### Finiteness of the total variation -/

/-- The total variation of any signed measure is a finite (positive) measure. -/
instance instIsFiniteMeasure_totalVariation (s : SignedMeasure α) :
    IsFiniteMeasure s.totalVariation := by
  rw [SignedMeasure.totalVariation]; infer_instance

/-- The total variation on the universe is `< ⊤`. -/
theorem totalVariation_univ_lt_top (s : SignedMeasure α) :
    s.totalVariation Set.univ < ⊤ :=
  measure_lt_top _ _

/-! ### Vanishing -/

/-- The total variation of the zero signed measure is the zero measure. -/
theorem totalVariation_zero_eq :
    totalVariation (0 : SignedMeasure α) = 0 :=
  totalVariation_zero

/-- A signed measure with vanishing total variation on the universe is itself zero. -/
theorem eq_zero_of_totalVariation_univ_eq_zero {s : SignedMeasure α}
    (h : s.totalVariation Set.univ = 0) : s = 0 := by
  ext i hi
  change s i = 0
  exact null_of_totalVariation_zero s
    (le_antisymm (h ▸ measure_mono (Set.subset_univ i)) zero_le)

/-! ### Comparison -/

/-- A non-negative signed measure is monotone on measurable sets. -/
theorem apply_le_apply_of_subset {s : SignedMeasure α} (hs : 0 ≤ s)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    s A ≤ s B := by
  have hBdiffA : MeasurableSet (B \ A) := hB.diff hA
  have h_diff_nn : 0 ≤ s (B \ A) := by
    have := hs _ hBdiffA
    rwa [VectorMeasure.zero_apply] at this
  have h_disj : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  have h_union : A ∪ (B \ A) = B := Set.union_diff_cancel hAB
  have h_add : s A + s (B \ A) = s B := by
    rw [← VectorMeasure.of_union h_disj hA hBdiffA, h_union]
  linarith

/-! ### Sub-additivity -/

/-- A signed measure equals the difference of the (real values of the) Jordan parts. -/
private lemma apply_eq_real_sub (s : SignedMeasure α) {A : Set α} (hA : MeasurableSet A) :
    s A = s.toJordanDecomposition.posPart.real A -
          s.toJordanDecomposition.negPart.real A := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.coe_sub, Pi.sub_apply,
    Measure.toSignedMeasure_apply_measurable hA,
    Measure.toSignedMeasure_apply_measurable hA]

/-- For any measurable set `P`, `s P - s Pᶜ ≤ |s|(univ)`. -/
private lemma diff_le_totalVariation_real (s : SignedMeasure α) {P : Set α}
    (hP : MeasurableSet P) :
    s P - s Pᶜ ≤ (s.totalVariation Set.univ).toReal := by
  rw [SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply,
    apply_eq_real_sub s hP, apply_eq_real_sub s hP.compl]
  have h1 : s.toJordanDecomposition.posPart.real P ≤
      s.toJordanDecomposition.posPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h2 : s.toJordanDecomposition.negPart.real Pᶜ ≤
      s.toJordanDecomposition.negPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h3 : 0 ≤ s.toJordanDecomposition.posPart.real Pᶜ := measureReal_nonneg
  have h4 : 0 ≤ s.toJordanDecomposition.negPart.real P := measureReal_nonneg
  linarith

/-- The total variation is sub-additive on the universe (real-valued form). -/
private lemma toReal_totalVariation_add_univ_le_aux (s t : SignedMeasure α) :
    ((s + t).totalVariation Set.univ).toReal ≤
      (s.totalVariation Set.univ).toReal +
        (t.totalVariation Set.univ).toReal := by
  obtain ⟨P, hP, hP₂, hP₃, hpos, hneg⟩ := (s + t).toJordanDecomposition_spec
  rw [SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply, hpos, hneg,
    toMeasureOfZeroLE_real_apply _ hP₂ hP MeasurableSet.univ,
    toMeasureOfLEZero_real_apply _ hP₃ hP.compl MeasurableSet.univ,
    Set.inter_univ, Set.inter_univ]
  have hs := diff_le_totalVariation_real s hP
  have ht := diff_le_totalVariation_real t hP
  have hadd_P : (s + t) P = s P + t P := by simp
  have hadd_Pc : (s + t) Pᶜ = s Pᶜ + t Pᶜ := by simp
  rw [hadd_P, hadd_Pc]
  linarith

/-- The total variation is sub-additive on the universe:
`|s + t|(univ) ≤ |s|(univ) + |t|(univ)`. -/
theorem totalVariation_add_univ_le (s t : SignedMeasure α) :
    (s + t).totalVariation Set.univ ≤
      s.totalVariation Set.univ + t.totalVariation Set.univ := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact toReal_totalVariation_add_univ_le_aux s t

/-! ### Scalar multiplication -/

/-- Total variation is positively homogeneous in the scalar:
`|c • s|(univ) = ENNReal.ofReal |c| * |s|(univ)`. -/
theorem totalVariation_smul_univ (c : ℝ) (s : SignedMeasure α) :
    (c • s).totalVariation Set.univ =
      ENNReal.ofReal |c| * s.totalVariation Set.univ := by
  rw [SignedMeasure.totalVariation, SignedMeasure.totalVariation,
    toJordanDecomposition_smul_real]
  by_cases hc : 0 ≤ c
  · rw [JordanDecomposition.real_smul_nonneg _ _ hc, JordanDecomposition.smul_posPart,
      JordanDecomposition.smul_negPart, Measure.add_apply, Measure.add_apply,
      Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, ← mul_add,
      abs_of_nonneg hc, ← ENNReal.ofNNReal_toNNReal]
  · push Not at hc
    rw [JordanDecomposition.real_smul_neg _ _ hc, JordanDecomposition.neg_posPart,
      JordanDecomposition.neg_negPart, JordanDecomposition.smul_posPart,
      JordanDecomposition.smul_negPart, Measure.add_apply, Measure.add_apply,
      Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, ← mul_add,
      add_comm (s.toJordanDecomposition.negPart Set.univ) _,
      abs_of_neg hc, ← ENNReal.ofNNReal_toNNReal]

/-! ### Comparison and modulus -/

/-- For a non-negative signed measure, the total variation on the universe agrees with the
value of the measure. -/
theorem totalVariation_univ_eq_of_nonneg {s : SignedMeasure α} (hs : 0 ≤ s) :
    (s.totalVariation Set.univ).toReal = (s Set.univ : ℝ) := by
  have hs' : (0 : SignedMeasure α) ≤[Set.univ] s :=
    (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hs
  let j : JordanDecomposition α :=
    { posPart := s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs'
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : s.toJordanDecomposition = j := by
    refine toJordanDecomposition_eq ?_
    change s = (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs').toSignedMeasure
                - (0 : Measure α).toSignedMeasure
    rw [Measure.toSignedMeasure_zero, sub_zero, toMeasureOfZeroLE_toSignedMeasure s hs']
  rw [SignedMeasure.totalVariation, hj]
  change ((s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs' + (0 : Measure α))
    Set.univ).toReal = s Set.univ
  rw [add_zero, toMeasureOfZeroLE_apply _ _ _ MeasurableSet.univ]
  simp

/-- Sub-additivity rewritten with `.toReal`. -/
theorem toReal_totalVariation_add_univ_le (s t : SignedMeasure α) :
    ((s + t).totalVariation Set.univ).toReal ≤
      (s.totalVariation Set.univ).toReal +
        (t.totalVariation Set.univ).toReal :=
  toReal_totalVariation_add_univ_le_aux s t

/-- The value of a signed measure on a measurable set is bounded in absolute
value by the total variation on the universe: `|s A| ≤ |s|(univ)`. Obtained by
splitting `A = (A ∩ P) ∪ (A ∩ Pᶜ)` along a Hahn decomposition `(P, Pᶜ)` of `s`
and bounding each piece by the corresponding Jordan part. -/
theorem abs_apply_le_totalVariation_univ (s : SignedMeasure α) {A : Set α}
    (hA : MeasurableSet A) :
    |(s A : ℝ)| ≤ (s.totalVariation Set.univ).toReal := by
  rw [SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply,
    apply_eq_real_sub s hA]
  have h1 : s.toJordanDecomposition.posPart.real A ≤
      s.toJordanDecomposition.posPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h2 : s.toJordanDecomposition.negPart.real A ≤
      s.toJordanDecomposition.negPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h3 : 0 ≤ s.toJordanDecomposition.posPart.real A := measureReal_nonneg
  have h4 : 0 ≤ s.toJordanDecomposition.negPart.real A := measureReal_nonneg
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

/-! ### Completeness in total variation

Total-variation Cauchy sequences of signed measures converge in total variation.
The proof uses a finite control measure, Radon--Nikodym densities, and
completeness of `L¹`.
-/

/-- For a measurable integrable real-valued function, the total variation of
the associated signed measure on the universe equals the L¹ norm of the
function. -/
lemma totalVariation_withDensityᵥ_apply_univ {μ : Measure α}
    {f : α → ℝ} (hfm : Measurable f) (hfi : Integrable f μ) :
    (SignedMeasure.totalVariation (μ.withDensityᵥ f) Set.univ).toReal =
      ∫ x, |f x| ∂μ := by
  have h0 : (0 : SignedMeasure α) ⟂ᵥ μ.toENNRealVectorMeasure :=
    VectorMeasure.MutuallySingular.zero_left
  have heq : (μ.withDensityᵥ f : SignedMeasure α) =
      0 + μ.withDensityᵥ f := (zero_add _).symm
  have hjd := toJordanDecomposition_eq_of_eq_add_withDensity hfm hfi h0 heq
  rw [SignedMeasure.totalVariation, hjd]
  simp only [toJordanDecomposition_zero, JordanDecomposition.zero_posPart,
    JordanDecomposition.zero_negPart, zero_add, Measure.add_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hpos : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hfm
  rw [← lintegral_add_left hpos (fun x => ENNReal.ofReal (-f x))]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => abs_nonneg _))
    (by fun_prop : AEStronglyMeasurable (fun x => |f x|) μ)]
  congr 1
  refine lintegral_congr fun x => ?_
  rcases le_or_gt 0 (f x) with h | h
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
  · rw [ENNReal.ofReal_of_nonpos h.le, zero_add, abs_of_neg h]

/-! ### Construction of the control measure -/

/-- The weight assigned to `(s n).totalVariation` in the control measure. The
denominator `2^(n+1) * (1 + |sₙ|(univ))` is finite and positive, so the
inverse is a positive finite ENNReal. -/
private noncomputable def controlWeight (s : ℕ → SignedMeasure α) (n : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (n + 1) * (1 + (s n).totalVariation Set.univ))⁻¹

private lemma controlWeight_denom_ne_top (s : ℕ → SignedMeasure α) (n : ℕ) :
    ((2 : ℝ≥0∞) ^ (n + 1) * (1 + (s n).totalVariation Set.univ)) ≠ ⊤ := by
  refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ?_
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (measure_lt_top _ _).ne⟩

private lemma controlWeight_pos (s : ℕ → SignedMeasure α) (n : ℕ) :
    0 < controlWeight s n :=
  ENNReal.inv_pos.mpr (controlWeight_denom_ne_top s n)

private lemma controlWeight_ne_zero (s : ℕ → SignedMeasure α) (n : ℕ) :
    controlWeight s n ≠ 0 := (controlWeight_pos s n).ne'

/-- A finite measure such that every signed measure in the sequence is
absolutely continuous with respect to it. -/
private noncomputable def controlMeasure (s : ℕ → SignedMeasure α) : Measure α :=
  Measure.sum (fun n => controlWeight s n • (s n).totalVariation)

/-- Each summand of the control measure has small total mass, bounded by
`(1/2)^(n+1) = (2^(n+1))⁻¹`. -/
private lemma controlWeight_smul_totalVariation_le (s : ℕ → SignedMeasure α) (n : ℕ) :
    (controlWeight s n • (s n).totalVariation) Set.univ ≤
      ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
  rw [Measure.smul_apply, smul_eq_mul, controlWeight]
  set r : ℝ≥0∞ := (s n).totalVariation Set.univ
  have hr_lt : r < ⊤ := measure_lt_top _ _
  have h1r_ne_top : (1 + r : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hr_lt.ne⟩
  have h1r_ne_zero : (1 + r : ℝ≥0∞) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have h2_ne_top : ((2 : ℝ≥0∞) ^ (n + 1)) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have h2_ne_zero : ((2 : ℝ≥0∞) ^ (n + 1)) ≠ 0 :=
    pow_ne_zero _ (two_ne_zero (α := ℝ≥0∞))
  rw [ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top), mul_assoc]
  refine mul_le_of_le_one_right zero_le ?_
  rw [ENNReal.inv_mul_le_iff h1r_ne_zero h1r_ne_top, mul_one]
  exact le_add_self

private instance instIsFiniteMeasure_controlMeasure (s : ℕ → SignedMeasure α) :
    IsFiniteMeasure (controlMeasure s) where
  measure_univ_lt_top := by
    rw [controlMeasure, Measure.sum_apply _ MeasurableSet.univ]
    refine lt_of_le_of_lt
      (ENNReal.tsum_le_tsum (controlWeight_smul_totalVariation_le s)) ?_
    -- Bound by ∑' n, (2⁻¹)^n = 2 < ⊤
    have h_pow : ∀ n, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹) ^ n := by
      intro n
      rw [← ENNReal.inv_pow]
      refine ENNReal.inv_le_inv.mpr ?_
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) n.le_succ
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum h_pow) ?_
    rw [ENNReal.tsum_geometric_two]
    exact ENNReal.ofNat_lt_top

private lemma totalVariation_absolutelyContinuous_controlMeasure
    (s : ℕ → SignedMeasure α) (n : ℕ) :
    (s n).totalVariation ≪ controlMeasure s := by
  refine Measure.absolutelyContinuous_sum_right n ?_
  exact Measure.absolutelyContinuous_smul (controlWeight_ne_zero s n)

private lemma signedMeasure_absolutelyContinuous_controlMeasure
    (s : ℕ → SignedMeasure α) (n : ℕ) :
    s n ≪ᵥ (controlMeasure s).toENNRealVectorMeasure := by
  rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact totalVariation_absolutelyContinuous_controlMeasure s n

/-! ### Conclusion -/

/-- **Completeness of signed measures in total variation.** A sequence of
signed measures that is Cauchy in the total-variation distance converges in
total variation to a signed measure. -/
theorem exists_tv_limit_of_cauchy
    (s : ℕ → SignedMeasure α)
    (hs : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ((s m - s n).totalVariation Set.univ).toReal < ε) :
    ∃ t : SignedMeasure α, ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ((s n - t).totalVariation Set.univ).toReal < ε := by
  set μ := controlMeasure s
  haveI : IsFiniteMeasure μ := instIsFiniteMeasure_controlMeasure s
  have hsAC : ∀ n, s n ≪ᵥ μ.toENNRealVectorMeasure :=
    signedMeasure_absolutelyContinuous_controlMeasure s
  -- Densities of each `s n` w.r.t. μ
  let f : ℕ → α → ℝ := fun n => (s n).rnDeriv μ
  have hfm : ∀ n, Measurable (f n) := fun n => SignedMeasure.measurable_rnDeriv _ _
  have hfi : ∀ n, Integrable (f n) μ := fun n => SignedMeasure.integrable_rnDeriv _ _
  -- Each `s n` equals `μ.withDensityᵥ (f n)`
  have hf_eq : ∀ n, μ.withDensityᵥ (f n) = (s n : SignedMeasure α) := fun n =>
    SignedMeasure.withDensityᵥ_rnDeriv_eq (s n) μ (hsAC n)
  -- Build L¹ versions of the densities
  let g : ℕ → Lp ℝ 1 μ := fun n => (hfi n).toL1 (f n)
  -- The sequence (g n) is L¹-Cauchy
  have hgCauchy : CauchySeq g := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hsubm : Measurable (fun x => f m x - f n x) := (hfm m).sub (hfm n)
    have hL1 : ‖g m - g n‖ = ((s m - s n).totalVariation Set.univ).toReal := by
      have hgsub : g m - g n = (hfi m).toL1 (f m) - (hfi n).toL1 (f n) := rfl
      rw [hgsub, ← Integrable.toL1_sub, Integrable.norm_toL1_eq_lintegral_norm]
      have hsubeq : (s m - s n : SignedMeasure α) =
          μ.withDensityᵥ (fun x => f m x - f n x) := by
        rw [withDensityᵥ_sub' (hfi m) (hfi n), hf_eq m, hf_eq n]
      rw [hsubeq, totalVariation_withDensityᵥ_apply_univ
        hsubm ((hfi m).sub (hfi n))]
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (by fun_prop : AEStronglyMeasurable (fun x => |f m x - f n x|) μ)]
      simp only [Real.norm_eq_abs, Pi.sub_apply]
    rw [hL1]
    exact hN m hm n hn
  -- L¹ is complete, so g converges to some limit gLim
  obtain ⟨gLim, hgLim⟩ := cauchySeq_tendsto_of_complete hgCauchy
  -- Take a measurable representative of gLim
  set fLim : α → ℝ := (Lp.aestronglyMeasurable gLim).mk gLim
  have hfLimm : Measurable fLim := (Lp.aestronglyMeasurable gLim).measurable_mk
  have hfLim_ae : (gLim : α → ℝ) =ᵐ[μ] fLim := (Lp.aestronglyMeasurable gLim).ae_eq_mk
  have hfLim_int : Integrable fLim μ := (L1.integrable_coeFn gLim).congr hfLim_ae
  -- The L¹ class of fLim is gLim
  have hgLim_eq_toL1 : gLim = hfLim_int.toL1 fLim := by
    rw [← Integrable.toL1_coeFn gLim (L1.integrable_coeFn gLim)]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr hfLim_ae
  -- The limit signed measure
  refine ⟨μ.withDensityᵥ fLim, fun ε hε => ?_⟩
  rw [Metric.tendsto_atTop] at hgLim
  obtain ⟨N, hN⟩ := hgLim ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- Express the TV difference as L¹ distance
  have hsubm : Measurable (fun x => f n x - fLim x) := (hfm n).sub hfLimm
  have hsubeq : (s n - μ.withDensityᵥ fLim : SignedMeasure α) =
      μ.withDensityᵥ (fun x => f n x - fLim x) := by
    rw [withDensityᵥ_sub' (hfi n) hfLim_int, hf_eq n]
  rw [hsubeq, totalVariation_withDensityᵥ_apply_univ
    hsubm ((hfi n).sub hfLim_int)]
  -- Show ‖g n - gLim‖ equals this integral
  have hL1 : ‖g n - gLim‖ = ∫ x, |f n x - fLim x| ∂μ := by
    rw [hgLim_eq_toL1]
    have hgsub : g n - hfLim_int.toL1 fLim = (hfi n).toL1 (f n) - hfLim_int.toL1 fLim := rfl
    rw [hgsub, ← Integrable.toL1_sub, Integrable.norm_toL1_eq_lintegral_norm]
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (by fun_prop : AEStronglyMeasurable (fun x => |f n x - fLim x|) μ)]
    simp only [Real.norm_eq_abs, Pi.sub_apply]
  -- Conclude
  have hbound : ‖g n - gLim‖ < ε := by
    rw [← dist_eq_norm]; exact hN n hn
  rw [hL1] at hbound
  exact hbound

end SignedMeasure
end MeasureTheory
