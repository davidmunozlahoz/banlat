/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Lp.Basic
import BanLat.QuasiNormed.Maps.Isometry
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Real-valued `ℓᵖ` spaces for `0 < p ≤ ∞`

For `0 < p ≤ ∞`, the correspondence between `ℓᵖ(α, ℝ)` and `Lᵖ` for counting measure
is a linear quasi-norm isometric equivalence. This correspondence equips `ℓᵖ(α, ℝ)`
with a quasi-Banach space structure, extending the usual Banach space treatment
for `1 ≤ p ≤ ∞`.
-/

open MeasureTheory
open scoped ENNReal lp

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
  {p : ENNReal} [Fact (0 < p)]

private lemma memLp_count_top_iff_memℓp (f : α → ℝ) :
    MemLp f ∞ (Measure.count : Measure α) ↔ Memℓp f ∞ := by
  rw [memℓp_infty_iff]
  constructor
  · intro hf
    refine ⟨(eLpNorm f ∞ (Measure.count : Measure α)).toReal, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top
      (enorm_le_eLpNorm_count f i (by simp))
  · rintro ⟨C, hC⟩
    exact memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun i ↦ hC ⟨i, rfl⟩)

/-- For `0 < p ≤ ∞`, a real-valued function belongs to `Lᵖ` for counting measure
exactly when it belongs to `ℓᵖ`. -/
lemma memLp_count_iff_memℓp (f : α → ℝ) :
    MemLp f p (Measure.count : Measure α) ↔ Memℓp f p := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact memLp_count_top_iff_memℓp f
  · have hsm : AEStronglyMeasurable f (Measure.count : Measure α) :=
      Measurable.of_discrete.aestronglyMeasurable
    have hp0 : p ≠ 0 := (Fact.out : 0 < p).ne'
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp hsm,
      memℓp_gen_iff hpos]
    simpa [hasFiniteIntegral_iff_enorm, Real.enorm_rpow_of_nonneg,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg _ _)] using
      (hasFiniteIntegral_count_iff (α := α) (β := ℝ)
        (f := fun i ↦ ‖f i‖ ^ p.toReal))

namespace Lp

private lemma norm_count_eq_lp
    (f : Lp ℝ p (Measure.count : Measure α))
    (hf : Memℓp (fun i ↦ f i) p) :
    ‖f‖ = ‖(⟨fun i ↦ f i, hf⟩ : ℓ^p(α, ℝ))‖ := by
  rcases eq_or_ne p ∞ with hp | hp
  · -- For `p = ∞`, both norms are the supremum of the pointwise norms.
    subst hp
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f), eLpNormEssSup_count,
      ENNReal.toReal_iSup (fun _ ↦ enorm_ne_top), lp.norm_eq_ciSup]
    simp
  · -- For finite `p`, integration against counting measure becomes summation.
    have hp0 : p ≠ 0 := (Fact.out : 0 < p).ne'
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable f),
      lintegral_count, lp.norm_eq_tsum_rpow hpos]
    simp_rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpos.le]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i ↦ Real.rpow_nonneg (norm_nonneg (f i)) _)
      (hf.summable hpos)]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (tsum_nonneg fun i ↦ Real.rpow_nonneg (norm_nonneg (f i)) _)
      (one_div_nonneg.mpr hpos.le)]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
      (tsum_nonneg fun i ↦ Real.rpow_nonneg (norm_nonneg (f i)) _) _)]

private noncomputable def lpCountLinearMap :
    Lp ℝ p (Measure.count : Measure α) →ₗ[ℝ] ℓ^p(α, ℝ) where
  toFun f := ⟨fun i ↦ f i, (memLp_count_iff_memℓp _).mp (Lp.memLp f)⟩
  map_add' f g := by
    apply lp.ext
    funext i
    exact Measure.ae_count_iff.mp (Lp.coeFn_add f g) i
  map_smul' c f := by
    apply lp.ext
    funext i
    exact Measure.ae_count_iff.mp (Lp.coeFn_smul c f) i

/-- For `0 < p ≤ ∞`, `Lᵖ` for counting measure is linearly equivalent to `ℓᵖ`. -/
noncomputable def lpCountLinearEquiv :
    Lp ℝ p (Measure.count : Measure α) ≃ₗ[ℝ] ℓ^p(α, ℝ) := by
  refine LinearEquiv.ofBijective lpCountLinearMap ⟨?_, ?_⟩
  · intro f g hfg
    apply Lp.ext
    exact Measure.ae_count_iff.mpr fun i ↦ congrArg (fun h ↦ h i) hfg
  · intro f
    let hf : MemLp (fun i ↦ f i) p (Measure.count : Measure α) :=
      (memLp_count_iff_memℓp _).mpr (lp.memℓp f)
    refine ⟨hf.toLp (fun i ↦ f i), ?_⟩
    apply lp.ext
    funext i
    exact Measure.ae_count_iff.mp hf.coeFn_toLp i

/-- For `0 < p ≤ ∞`, the counting-measure linear equivalence preserves coordinate values. -/
@[simp]
theorem lpCountLinearEquiv_apply
    (f : Lp ℝ p (Measure.count : Measure α)) (i : α) :
    lpCountLinearEquiv f i = f i := by
  rfl

/-- For `0 < p ≤ ∞`, the counting-measure linear equivalence preserves the norm functional. -/
@[simp]
theorem norm_lpCountLinearEquiv (f : Lp ℝ p (Measure.count : Measure α)) :
    ‖lpCountLinearEquiv f‖ = ‖f‖ := by
  exact (norm_count_eq_lp f _).symm

end Lp

end MeasureTheory

namespace lp

variable {α : Type*} {p : ENNReal} [Fact (0 < p)]

private lemma exists_quasi_triangle_constant_lp :
    ∃ K, IsQuasiTriangleConstant (ℓ^p(α, ℝ)) K := by
  let : MeasurableSpace α := ⊤
  let : DiscreteMeasurableSpace α := inferInstance
  let e := Lp.lpCountLinearEquiv (α := α) (p := p)
  obtain ⟨K, hK⟩ := IsQuasiSeminorm.exists_quasi_triangle_constant
    (E := Lp ℝ p (Measure.count : Measure α))
  have hnorm (f : ℓ^p(α, ℝ)) : ‖e.symm f‖ = ‖f‖ := by
    simpa only [e, LinearEquiv.apply_symm_apply] using
      (Lp.norm_lpCountLinearEquiv (e.symm f)).symm
  refine ⟨K, hK.one_le, fun f g ↦ ?_⟩
  simpa only [← map_add, hnorm] using hK.norm_add_le (e.symm f) (e.symm g)

/-- For `0 < p ≤ ∞`, the usual functional on real-valued `ℓᵖ` is a quasi-norm. -/
instance (priority := 100) instIsQuasiNorm : IsQuasiNorm (ℓ^p(α, ℝ)) where
  norm_zero := lp.norm_zero
  norm_nonneg := lp.norm_nonneg'
  norm_neg := lp.norm_neg
  exists_quasi_triangle_constant := exists_quasi_triangle_constant_lp
  eq_zero_of_norm_eq_zero := fun _ hf ↦ lp.norm_eq_zero_iff.mp hf

/-- For `0 < p ≤ ∞`, real-valued `ℓᵖ` is a quasi-normed real vector space. -/
noncomputable instance (priority := 100) instQuasiNormedSpace :
    QuasiNormedSpace ℝ (ℓ^p(α, ℝ)) where
  toModule := inferInstance
  norm_smul c f := lp.norm_const_smul (c := c) (Fact.out : 0 < p).ne' f

end lp

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
  {p : ENNReal} [Fact (0 < p)]

/-- For `0 < p ≤ ∞`, the counting-measure correspondence is a quasi-linear
isometric equivalence. -/
noncomputable def lpCountQuasiLinearIsometryEquiv :
    QuasiLinearIsometryEquiv ℝ
      (Lp ℝ p (Measure.count : Measure α)) (ℓ^p(α, ℝ)) where
  toLinearEquiv := lpCountLinearEquiv
  norm_map' := norm_lpCountLinearEquiv

end MeasureTheory.Lp

namespace lp

variable {α : Type*} {p : ENNReal} [Fact (0 < p)]

/-- For `0 < p ≤ ∞`, real-valued `ℓᵖ` is complete for its induced quasi-norm uniformity. -/
noncomputable instance (priority := 100) instQuasiSeminormCompleteSpace :
    QuasiSeminormCompleteSpace (ℓ^p(α, ℝ)) := by
  let : MeasurableSpace α := ⊤
  let : DiscreteMeasurableSpace α := inferInstance
  let e := Lp.lpCountQuasiLinearIsometryEquiv (α := α) (p := p)
  exact e.toQuasiIsometryEquiv.quasiSeminormCompleteSpace_iff.mp inferInstance

/-- For `0 < p ≤ ∞`, real-valued `ℓᵖ` is a quasi-Banach real vector space. -/
noncomputable instance (priority := 100) instQuasiBanachSpace :
    QuasiBanachSpace ℝ (ℓ^p(α, ℝ)) where
  toQuasiNormedSpace := instQuasiNormedSpace
  toCompleteSpace := instQuasiSeminormCompleteSpace

section CoordinateExpansion

variable [DecidableEq α] [hp_top : Fact (p < ∞)]

include hp_top

/-- For `0 < p < ∞`, every `f ∈ ℓᵖ(α, ℝ)` admits the unconditional coordinate expansion
`f = ∑ᵢ fᵢ eᵢ` in the quasi-norm topology. -/
theorem hasSum_single_quasi (f : ℓ^p(α, ℝ)) :
    @HasSum (ℓ^p(α, ℝ)) α _ (IsQuasiSeminorm.topology _)
      (fun i ↦ lp.single p i (f i)) f (SummationFilter.unconditional α) := by
  let : TopologicalSpace (ℓ^p(α, ℝ)) := IsQuasiSeminorm.topology _
  have hp : 0 < p.toReal :=
    ENNReal.toReal_pos (Fact.out : 0 < p).ne' (Fact.out : p < ∞).ne
  have hsum := lp.hasSum_norm hp f
  rw [HasSum, Metric.tendsto_nhds] at hsum
  rw [HasSum, IsQuasiSeminorm.tendsto_nhds_iff]
  intro ε hε
  filter_upwards [hsum (ε ^ p.toReal) (Real.rpow_pos_of_pos hε _)] with s hs
  rw [dist_comm, Real.dist_eq, ← lp.norm_compl_sum_single hp f s,
    abs_of_nonneg (Real.rpow_nonneg (lp.norm_nonneg' _) _)] at hs
  rw [IsQuasiSeminorm.norm_sub_rev]
  exact (Real.rpow_lt_rpow_iff (lp.norm_nonneg' _) hε.le hp).mp hs

/-- For `0 < p < ∞`, the canonical unit vectors have dense real linear
span in `ℓᵖ(α, ℝ)`. -/
theorem dense_span_single_quasi :
    @Dense (ℓ^p(α, ℝ)) (IsQuasiSeminorm.topology _)
      (Submodule.span ℝ (Set.range fun i : α ↦ lp.single p i (1 : ℝ)) :
        Set (ℓ^p(α, ℝ))) := by
  let : TopologicalSpace (ℓ^p(α, ℝ)) := IsQuasiSeminorm.topology _
  intro f
  have hmem (i : α) : lp.single p i (f i) ∈
      Submodule.span ℝ (Set.range fun i : α ↦ lp.single p i (1 : ℝ)) := by
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
      Submodule.smul_mem (Submodule.span ℝ
        (Set.range fun i : α ↦ lp.single p i (1 : ℝ))) (f i)
        (Submodule.subset_span (Set.mem_range_self i))
  refine isClosed_closure.mem_of_tendsto (hasSum_single_quasi f) ?_
  exact Filter.Eventually.of_forall fun s ↦
    subset_closure (Submodule.sum_mem _ fun i _ ↦ hmem i)

end CoordinateExpansion

end lp
