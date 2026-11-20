/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.AlmostOrderBounded
import BanLat.Examples.Lp.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Almost order bounded families in `L¹`

Almost order bounded subsets of `L¹(μ)` are equi-integrable. If `μ` is finite,
every norm-bounded equi-integrable subset of `L¹(μ)` is almost order bounded.

In this file, equi-integrability means uniformly absolutely continuous integrals,
expressed by Mathlib's `UnifIntegrable` predicate at exponent one. Mathlib's
`UniformIntegrable` additionally requires a uniform bound on the `L¹` norms.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For `f, u ∈ L¹(μ)` and a set `s`, the `L¹` norm of `f` with respect to
`μ.restrict s` is bounded by the corresponding norm of `u` plus the `L¹(μ)`
norm of `(|f| - u)⁺`. -/
private lemma eLpNorm_restrict_le_tail (f u : Lp ℝ 1 μ) (s : Set α) :
    eLpNorm f 1 (μ.restrict s) ≤
      eLpNorm u 1 (μ.restrict s) + ENNReal.ofReal ‖(|f| - u)⁺‖ := by
  let t := (|f| - u)⁺
  have hle : |f| ≤ u + t := by dsimp [t]; llarith
  have hae : ∀ᵐ x ∂μ, ‖f x‖ ≤ u x + t x := by
    filter_upwards [(coeFn_le _ _).mpr hle, coeFn_abs f, coeFn_add u t]
      with x hx hf hsum
    simpa only [hf, hsum, Real.norm_eq_abs, Pi.add_apply] using hx
  calc
    eLpNorm f 1 (μ.restrict s) ≤ eLpNorm (⇑u + ⇑t) 1 (μ.restrict s) :=
      eLpNorm_mono_ae_real (Lp.aestronglyMeasurable f).restrict
        (hae.filter_mono MeasureTheory.ae_restrict_le)
    _ ≤ eLpNorm u 1 (μ.restrict s) + eLpNorm t 1 (μ.restrict s) :=
      eLpNorm_add_le le_rfl
    _ ≤ eLpNorm u 1 (μ.restrict s) + ENNReal.ofReal ‖t‖ := by
      rw [ofReal_norm, enorm_def]
      exact add_le_add le_rfl (eLpNorm_mono_measure t μ.restrict_le_self)

/-- Every almost order bounded subset of real `L¹(μ)` is equi-integrable. -/
theorem unifIntegrable_of_almostOrderBounded {F : Set (Lp ℝ 1 μ)}
    (hF : AlmostOrderBounded F) :
    UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ := by
  refine unifIntegrable_iff'.mpr fun ε hε ↦ ?_
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hhalf
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨u, _, hu⟩ := hF r hrpos
  obtain ⟨δ, hδ, hsmall⟩ := unifIntegrable_iff.mp
    (unifIntegrable_const (ι := F) le_rfl (by norm_num) (Lp.memLp u)) (ε / 2) hhalf
  refine ⟨δ, hδ, fun f s _ hs ↦ ?_⟩
  calc
    eLpNorm (f.1 : α → ℝ) 1 (μ.restrict s) ≤
        eLpNorm u 1 (μ.restrict s) + ENNReal.ofReal ‖(|f.1| - u)⁺‖ :=
      eLpNorm_restrict_le_tail f.1 u s
    _ ≤ ε / 2 + (r : ℝ≥0∞) := add_le_add (hsmall f s hs) (by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hu f.1 f.2))
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hrε.le
    _ = ε := ENNReal.add_halves ε

/-- Every norm-bounded, equi-integrable subset of real `L¹(μ)` satisfies
`UniformIntegrable`. -/
theorem uniformIntegrable_of_isBounded_of_unifIntegrable {F : Set (Lp ℝ 1 μ)}
    (hbounded : Bornology.IsBounded F)
    (hF : UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ) :
    UniformIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ := by
  obtain ⟨C, hC, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨hF, ⟨C, hC.le⟩, fun f ↦ ?_⟩
  rw [← enorm_def, ← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal (hbound f.1 f.2)).trans_eq
    (ENNReal.ofReal_eq_coe_nnreal _)

/-- Let `f ∈ L¹(μ)` and let `u ∈ L¹(μ)` be almost everywhere equal to the
nonnegative constant `C`. Then the `L¹` norm of `(|f| - u)⁺` is bounded by
the integral of `|f|` over the set where `|f| ≥ C`. -/
private lemma eLpNorm_tail_le_indicator (f u : Lp ℝ 1 μ) (C : ℝ≥0)
    (hu : ⇑u =ᵐ[μ] fun _ ↦ (C : ℝ)) :
    eLpNorm ((|f| - u)⁺ : Lp ℝ 1 μ) 1 μ ≤
      eLpNorm ({x | C ≤ ‖f x‖₊}.indicator f) 1 μ := by
  rw [posPart_def]
  apply eLpNorm_mono_ae (Lp.aestronglyMeasurable _)
  filter_upwards [coeFn_sup (|f| - u) 0, coeFn_sub |f| u, coeFn_abs f, hu,
    coeFn_zero ℝ 1 μ] with x hpos hsub habs hconst hzero
  rw [hpos, Pi.sup_apply, hzero, Pi.zero_apply, hsub, Pi.sub_apply, habs, hconst,
    Real.norm_eq_abs,
    abs_of_nonneg (le_max_right _ _)]
  by_cases hx : C ≤ ‖f x‖₊
  · rw [Set.indicator_of_mem (s := {x | C ≤ ‖f x‖₊}) hx, Real.norm_eq_abs]
    exact max_le (sub_le_self _ C.coe_nonneg) (abs_nonneg _)
  · rw [Set.indicator_of_notMem (s := {x | C ≤ ‖f x‖₊}) hx, _root_.norm_zero]
    apply max_le _ le_rfl
    have hlt : |f x| < (C : ℝ) := by exact_mod_cast (lt_of_not_ge hx)
    exact sub_nonpos.mpr hlt.le

/-- If `μ` is finite, every norm-bounded, equi-integrable subset of real
`L¹(μ)` is almost order bounded. -/
private lemma almostOrderBounded_of_unifIntegrable [IsFiniteMeasure μ]
    {F : Set (Lp ℝ 1 μ)} (hbounded : Bornology.IsBounded F)
    (hF : UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ) : AlmostOrderBounded F := by
  intro ε hε
  obtain ⟨C, hC⟩ := (uniformIntegrable_of_isBounded_of_unifIntegrable hbounded hF).spec
    (by norm_num) (by norm_num) (ENNReal.ofReal_pos.mpr hε)
  let u : Lp ℝ 1 μ := (memLp_const (C : ℝ)).toLp (fun _ ↦ (C : ℝ))
  have hu : ⇑u =ᵐ[μ] fun _ ↦ (C : ℝ) := MemLp.coeFn_toLp _
  refine ⟨u, (coeFn_nonneg u).mp ?_, fun f hf ↦ ?_⟩
  · exact hu.mono fun x hx ↦ hx.symm ▸ C.coe_nonneg
  · rw [norm_def]
    exact ENNReal.toReal_le_of_le_ofReal hε.le
      ((eLpNorm_tail_le_indicator f u C hu).trans (hC ⟨f, hf⟩))

/-- For a finite measure `μ`, a norm-bounded subset of real `L¹(μ)` is almost
order bounded if and only if it is equi-integrable. -/
theorem almostOrderBounded_iff_unifIntegrable [IsFiniteMeasure μ]
    {F : Set (Lp ℝ 1 μ)} (hbounded : Bornology.IsBounded F) :
    AlmostOrderBounded F ↔ UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ :=
  ⟨unifIntegrable_of_almostOrderBounded, almostOrderBounded_of_unifIntegrable hbounded⟩

end MeasureTheory.Lp
