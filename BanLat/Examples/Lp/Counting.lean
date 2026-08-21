import BanLat.Examples.Ellp.Basic
import BanLat.Examples.Lp.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# `ℓ^p(α; ℝ)` as `L^p(α, count; ℝ)`

For every `1 ≤ p ≤ ∞`, `L^p(α, 𝒫(α), count; ℝ)` is lattice
isometric to `ℓ^p(α; ℝ)`.
-/

open MeasureTheory
open scoped ENNReal lp

noncomputable section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
  {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Membership for the counting measure -/

/-- A real-valued function belongs to `L^p(α, count; ℝ)` exactly when it
belongs to `ℓ^p(α; ℝ)`. -/
lemma memLp_count_iff_memℓp (f : α → ℝ) :
    MemLp f p (Measure.count : Measure α) ↔ Memℓp f p := by
  have hsm : AEStronglyMeasurable f (Measure.count : Measure α) :=
    Measurable.of_discrete.aestronglyMeasurable
  rcases eq_or_ne p ∞ with hp | hp
  · subst hp
    rw [memℓp_infty_iff]
    constructor
    · intro hf
      refine ⟨(eLpNorm f ∞ (Measure.count : Measure α)).toReal, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact ENNReal.toReal_mono hf.eLpNorm_ne_top
        (enorm_le_eLpNorm_count f i (by simp))
    · rintro ⟨C, hC⟩
      exact memLp_top_of_bound hsm C
        (Filter.Eventually.of_forall fun i => hC ⟨i, rfl⟩)
  · have hp0 : p ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) Fact.out)
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [MemLp, and_iff_right hsm,
      eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp,
      memℓp_gen_iff hpos]
    simpa [hasFiniteIntegral_iff_enorm, Real.enorm_rpow_of_nonneg,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg _ _)] using
      (hasFiniteIntegral_count_iff (α := α) (β := ℝ)
        (f := fun i => ‖f i‖ ^ p.toReal))

namespace Lp

/-! ### Equivalence between `L^p(α, count; ℝ)` and `ℓ^p(α; ℝ)` -/

/-- The pointwise identification of `L^p(α, count; ℝ)` with `ℓ^p(α; ℝ)`
preserves the norm. -/
private lemma norm_count_eq_lp
    (f : Lp ℝ p (Measure.count : Measure α))
    (hf : Memℓp (fun i => f i) p) :
    ‖f‖ = ‖(⟨fun i => f i, hf⟩ : ℓ^p(α, ℝ))‖ := by
  rcases eq_or_ne p ∞ with hp | hp
  · -- For `p = ∞`, both norms are the supremum of the pointwise norms.
    subst hp
    rw [Lp.norm_def, eLpNorm_exponent_top, eLpNormEssSup_count,
      ENNReal.toReal_iSup (fun _ => enorm_ne_top), lp.norm_eq_ciSup]
    simp
  · -- For finite `p`, integration against counting measure becomes summation.
    have hp0 : p ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) Fact.out)
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp,
      lintegral_count, lp.norm_eq_tsum_rpow hpos]
    simp_rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpos.le]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => Real.rpow_nonneg (norm_nonneg (f i)) _)
      (hf.summable hpos)]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (tsum_nonneg fun i => Real.rpow_nonneg (norm_nonneg (f i)) _)
      (one_div_nonneg.mpr hpos.le)]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
      (tsum_nonneg fun i => Real.rpow_nonneg (norm_nonneg (f i)) _) _)]

private noncomputable def lpCountLinearIsometryEquiv :
    Lp ℝ p (Measure.count : Measure α) ≃ₗᵢ[ℝ] ℓ^p(α, ℝ) := by
  let toℓp : Lp ℝ p (Measure.count : Measure α) →ₗᵢ[ℝ] ℓ^p(α, ℝ) :=
    { toLinearMap :=
        { toFun := fun f =>
            ⟨fun i => f i, (memLp_count_iff_memℓp (fun i => f i)).1 (Lp.memLp f)⟩
          map_add' := fun f g => by
            apply lp.ext
            funext i
            exact MeasureTheory.Measure.ae_count_iff.mp (Lp.coeFn_add f g) i
          map_smul' := fun c f => by
            apply lp.ext
            funext i
            exact MeasureTheory.Measure.ae_count_iff.mp (Lp.coeFn_smul c f) i }
      norm_map' := fun f => (norm_count_eq_lp f _).symm }
  refine LinearIsometryEquiv.ofSurjective toℓp ?_
  intro f
  let hf : MemLp (fun i => f i) p (Measure.count : Measure α) :=
    (memLp_count_iff_memℓp (fun i => f i)).2 (lp.memℓp f)
  refine ⟨hf.toLp (fun i => f i), ?_⟩
  apply lp.ext
  funext i
  exact MeasureTheory.Measure.ae_count_iff.mp hf.coeFn_toLp i

private lemma lpCountLinearIsometryEquiv_map_sup
    (f g : Lp ℝ p (Measure.count : Measure α)) :
    lpCountLinearIsometryEquiv (f ⊔ g) =
      lpCountLinearIsometryEquiv f ⊔ lpCountLinearIsometryEquiv g := by
  apply lp.ext
  funext i
  exact MeasureTheory.Measure.ae_count_iff.mp (Lp.coeFn_sup f g) i

/-- The spaces `L^p(α, count; ℝ)` and `ℓ^p(α; ℝ)` are lattice isometric. -/
noncomputable def lpCountEquiv :
    BanachLatEquiv
      (Lp ℝ p (Measure.count : Measure α))
      (ℓ^p(α, ℝ)) := by
  refine
    { toLinearIsometryEquiv := lpCountLinearIsometryEquiv
      map_sup' := lpCountLinearIsometryEquiv_map_sup
      map_inf' := fun f g => ?_ }
  apply lp.ext
  funext i
  exact MeasureTheory.Measure.ae_count_iff.mp (Lp.coeFn_inf f g) i

/-- The equivalence from `L^p(α, count; ℝ)` to `ℓ^p(α; ℝ)` evaluates pointwise. -/
@[simp]
lemma lpCountEquiv_apply
    (f : Lp ℝ p (Measure.count : Measure α)) (x : α) :
    lpCountEquiv f x = f x := by
  rfl

/-- The inverse equivalence from `ℓ^p(α; ℝ)` to `L^p(α, count; ℝ)` evaluates
pointwise. -/
@[simp]
lemma lpCountEquiv_symm_apply
    (f : ℓ^p(α, ℝ)) (x : α) :
    ((lpCountEquiv (α := α) (p := p)).symm f :
      Lp ℝ p (Measure.count : Measure α)) x = f x := by
  have h := congrArg (fun g : ℓ^p(α, ℝ) => g x)
    ((lpCountEquiv (α := α) (p := p)).toLinearIsometryEquiv.apply_symm_apply f)
  simpa only [lpCountEquiv_apply] using h

end Lp

end MeasureTheory
