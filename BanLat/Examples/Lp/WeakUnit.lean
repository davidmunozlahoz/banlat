/-
Author: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Lp.OrderContinuous
import BanLat.QuasiInteriorPoint
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Weak order units in `L^p` spaces

For `1 ≤ p < ∞`, this file proves that:
* If `f ∈ L^p(μ), f > 0`, then `f` is a weak order unit.
* `∃ f ∈ L^p(μ), f > 0 μ a.e.` iff `μ` is `σ`-finite.
* If `μ` is `σ`-finite, then `f ∈ L^p(μ)` is a weak order unit iff `f > 0, μ-a.e`.
* Every separable `L^p(μ)`-space has a weak order unit (even normalized).
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.Lp

universe u

variable {α : Type u} [MeasurableSpace α] {p : ℝ≥0}

/-- An `L^p` function which is strictly positive almost everywhere is a weak order unit. -/
theorem weakOrderUnit_of_ae_pos {μ : Measure α} {f : Lp ℝ (p : ENNReal) μ}
    (hpos : ∀ᵐ x ∂μ, 0 < f x) : WeakOrderUnit f := by
  have hf : 0 ≤ f := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [hpos] with x hx
    exact hx.le
  refine ⟨hf, fun g hdisj ↦ ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_inf |g| |f|, Lp.coeFn_abs g, Lp.coeFn_abs f,
    Lp.coeFn_zero ℝ (p : ENNReal) μ, hpos] with x hinf hg hfabs hzero hfx
  have hmeet : min |g x| |f x| = 0 := by
    change (|g| ⊓ |f| : Lp ℝ (p : ENNReal) μ) x =
      min ((|g| : Lp ℝ (p : ENNReal) μ) x) ((|f| : Lp ℝ (p : ENNReal) μ) x) at hinf
    rw [hg, hfabs] at hinf
    calc
      min |g x| |f x| = (|g| ⊓ |f| : Lp ℝ (p : ENNReal) μ) x := hinf.symm
      _ = (0 : Lp ℝ (p : ENNReal) μ) x := congrArg (fun u ↦ u x) hdisj
      _ = 0 := hzero
  by_cases hle : |g x| ≤ |f x|
  · rw [min_eq_left hle] at hmeet
    rw [hzero]
    exact abs_eq_zero.mp hmeet
  · rw [min_eq_right (le_of_not_ge hle)] at hmeet
    exact (hfx.ne' (abs_eq_zero.mp hmeet)).elim

section

variable [Fact (1 ≤ p)]

/-- `L^p(μ)` contains a strictly positive almost everywhere function iff `μ` is `σ`-finite. -/
theorem exists_ae_pos_iff_sigmaFinite (μ : Measure α) :
    (∃ f : Lp ℝ (p : ENNReal) μ, ∀ᵐ x ∂μ, 0 < f x) ↔ SigmaFinite μ := by
  constructor
  · rintro ⟨f, hpos⟩
    have hp0 : (p : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr
      (lt_of_lt_of_le zero_lt_one Fact.out).ne'
    obtain ⟨s, hs, hzero, hσ⟩ :=
      (Lp.finStronglyMeasurable f hp0 ENNReal.coe_ne_top).aefinStronglyMeasurable
        |>.exists_set_sigmaFinite
    have hpos' : ∀ᵐ x ∂μ.restrict sᶜ, 0 < f x := ae_restrict_of_ae hpos
    have hempty : ∀ᵐ x ∂μ.restrict sᶜ, x ∈ (∅ : Set α) := by
      filter_upwards [hzero, hpos'] with x hx hfx
      exact (hfx.ne' hx).elim
    have hμsc : μ sᶜ = 0 := by
      have h := ae_iff.mp hempty
      simpa [Measure.restrict_apply, hs.compl] using h
    have haes : ∀ᵐ x ∂μ, x ∈ s := ae_iff.mpr (by simpa [← Set.compl_def] using hμsc)
    rwa [Measure.restrict_eq_self_of_ae_mem haes] at hσ
  · intro hμ
    let : SigmaFinite μ := hμ
    have hpNN : 0 < p := lt_of_lt_of_le zero_lt_one Fact.out
    have hpR : 0 < (p : ℝ) := NNReal.coe_pos.mpr hpNN
    obtain ⟨g, hgpos, hgmeas, hgint⟩ :=
      exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
    let q : ℝ := 1 / (p : ℝ)
    let h : α → ℝ≥0 := fun x ↦ g x ^ q
    have hq : 0 ≤ q := one_div_nonneg.mpr hpR.le
    have hhmeas : Measurable h :=
      NNReal.continuous_rpow_const hq |>.measurable.comp hgmeas
    have hhmem : MemLp (fun x ↦ (h x : ℝ)) (p : ENNReal) μ := by
      rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (ENNReal.coe_ne_zero.mpr hpNN.ne') ENNReal.coe_ne_top
        hhmeas.coe_nnreal_real.aestronglyMeasurable]
      calc
        (∫⁻ x, ‖(h x : ℝ)‖ₑ ^ (p : ℝ) ∂μ) = ∫⁻ x, (g x : ENNReal) ∂μ := by
          apply lintegral_congr
          intro x
          rw [show (h x : ℝ) = (g x : ℝ) ^ q by simp [h]]
          rw [Real.enorm_rpow_of_nonneg (NNReal.coe_nonneg _) hq]
          rw [← ENNReal.rpow_mul, show q * (p : ℝ) = 1 by simp [q, hpR.ne']]
          simp
        _ < 1 := hgint
        _ < ∞ := ENNReal.one_lt_top
    let f := hhmem.toLp fun x ↦ (h x : ℝ)
    refine ⟨f, ?_⟩
    filter_upwards [hhmem.coeFn_toLp] with x hx
    rw [hx]
    exact_mod_cast NNReal.rpow_pos (hgpos x)

end

private lemma indicatorConstLp_one_eq_zero_iff {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    indicatorConstLp (p : ENNReal) hs hμs (1 : ℝ) = 0 ↔ μ s = 0 := by
  simpa [ae_eq_empty] using
    (indicatorConstLp_inj (p := (p : ENNReal)) hs hμs MeasurableSet.empty
      (by simp) (c := (1 : ℝ)) one_ne_zero)

/-- If `μ` is `σ`-finite, then `f ∈ L^p(μ)` is a weak order unit iff
`f > 0, μ-a.e`. -/
theorem weakOrderUnit_iff_ae_pos {μ : Measure α} [SigmaFinite μ]
    {f : Lp ℝ (p : ENNReal) μ} : WeakOrderUnit f ↔ ∀ᵐ x ∂μ, 0 < f x := by
  refine ⟨fun hwu ↦ ?_, weakOrderUnit_of_ae_pos⟩
  have hf_ae : 0 ≤ᵐ[μ] (f : α → ℝ) := (Lp.coeFn_nonneg f).mpr hwu.1
  let s : Set α := {x | f x ≤ 0}
  have hs : MeasurableSet s := (Lp.stronglyMeasurable f).measurable measurableSet_Iic
  have hμs : μ s = 0 := by
    by_contra hμs
    obtain ⟨n, hn⟩ := (Measure.exists_measure_inter_spanningSets_pos s).2
      (pos_iff_ne_zero.mpr hμs)
    let t := s ∩ spanningSets μ n
    have ht : MeasurableSet t := hs.inter (measurableSet_spanningSets μ n)
    have hμt : μ t ≠ ∞ := ne_of_lt
      ((measure_mono (Set.inter_subset_right (s := s))).trans_lt
        (measure_spanningSets_lt_top μ n))
    let g : Lp ℝ (p : ENNReal) μ := indicatorConstLp (p : ENNReal) ht hμt (1 : ℝ)
    have hg_coe : (g : α → ℝ) =ᵐ[μ] t.indicator fun _ ↦ (1 : ℝ) :=
      indicatorConstLp_coeFn
    have hg_nonneg : 0 ≤ g := by
      rw [← Lp.coeFn_nonneg]
      filter_upwards [hg_coe] with x hx
      rw [hx]
      exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
    have hmeet : g ⊓ f = 0 := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_inf g f, Lp.coeFn_zero ℝ (p : ENNReal) μ,
        hg_coe, hf_ae] with x hinf hzero hgx hfx
      rw [hinf, hzero]
      change min (g x) (f x) = 0
      rw [hgx]
      by_cases hxt : x ∈ t
      · have hfx' : f x ≤ 0 := hxt.1
        simp [Set.indicator_of_mem hxt, le_antisymm hfx' hfx]
      · rw [Set.indicator_of_notMem hxt]
        exact min_eq_left hfx
    have hg_disj : IsVLDisjoint g f := by
      unfold IsVLDisjoint
      rw [abs_of_nonneg hg_nonneg, abs_of_nonneg hwu.1, hmeet]
    have hg_zero := hwu.2 g hg_disj
    exact hn.ne' ((indicatorConstLp_one_eq_zero_iff ht hμt).mp hg_zero)
  have hnot : ∀ᵐ x ∂μ, x ∉ s := ae_iff.mpr (by simpa using hμs)
  filter_upwards [hnot, hf_ae] with x hxs hfx
  exact lt_of_le_of_ne hfx fun h ↦ hxs h.symm.le

private lemma weakOrderUnit_ne_zero [Nontrivial (Lp ℝ (p : ENNReal) μ)]
    {e : Lp ℝ (p : ENNReal) μ} (he : WeakOrderUnit e) : e ≠ 0 := by
  intro he0
  obtain ⟨x, hx⟩ := exists_ne (0 : Lp ℝ (p : ENNReal) μ)
  apply hx
  apply he.2 x
  simp [he0, IsVLDisjoint]

section

variable [Fact (1 ≤ p)]

private lemma quasiInteriorPoint_smul_of_pos
    {e : Lp ℝ (p : ENNReal) μ} (he : QuasiInteriorPoint e) {c : ℝ} (hc : 0 < c) :
    QuasiInteriorPoint (c • e) := by
  refine ⟨smul_nonneg hc.le he.1, ?_⟩
  apply Dense.mono _ he.2
  rintro x ⟨r, hr, hxr⟩
  refine ⟨r / c, div_nonneg hr hc.le, ?_⟩
  rw [abs_smul' e c, abs_of_pos hc, smul_smul, div_mul_cancel₀ r hc.ne']
  exact hxr

private lemma normalize_weakOrderUnit {μ : Measure α} {e : Lp ℝ (p : ENNReal) μ}
    (he : WeakOrderUnit e) (he_ne : e ≠ 0) :
    ∃ u : Lp ℝ (p : ENNReal) μ, WeakOrderUnit u ∧ ‖u‖ = 1 := by
  have he' : QuasiInteriorPoint e := quasiInteriorPoint_iff_weakOrderUnit.mpr he
  have he_norm_pos : 0 < ‖e‖ := norm_pos_iff.mpr he_ne
  refine ⟨‖e‖⁻¹ • e, quasiInteriorPoint_iff_weakOrderUnit.mp
    (quasiInteriorPoint_smul_of_pos he' (inv_pos.mpr he_norm_pos)), ?_⟩
  simp [norm_smul, he_norm_pos.ne']

/-- Every nontrivial separable real `L^p` space has a weak order unit of norm one. -/
theorem exists_weakOrderUnit_norm_one_of_separable
    (μ : Measure α)
    [TopologicalSpace.SeparableSpace (Lp ℝ (p : ENNReal) μ)]
    [Nontrivial (Lp ℝ (p : ENNReal) μ)] :
    ∃ e : Lp ℝ (p : ENNReal) μ, WeakOrderUnit e ∧ ‖e‖ = 1 := by
  obtain ⟨e, he⟩ :=
    exists_quasiInteriorPoint_of_separable (X := Lp ℝ (p : ENNReal) μ)
  have hwu : WeakOrderUnit e := quasiInteriorPoint_iff_weakOrderUnit.mp he
  exact normalize_weakOrderUnit hwu (weakOrderUnit_ne_zero hwu)

/-- Every nontrivial real `L^p` space over a sigma-finite measure has a weak order unit
of norm one. -/
theorem exists_weakOrderUnit_norm_one_of_sigmaFinite
    (μ : Measure α) [SigmaFinite μ] [Nontrivial (Lp ℝ (p : ENNReal) μ)] :
    ∃ e : Lp ℝ (p : ENNReal) μ, WeakOrderUnit e ∧ ‖e‖ = 1 := by
  obtain ⟨e, hpos⟩ :=
    (exists_ae_pos_iff_sigmaFinite (p := p) μ).mpr (by infer_instance)
  have he : WeakOrderUnit e := weakOrderUnit_of_ae_pos hpos
  exact normalize_weakOrderUnit he (weakOrderUnit_ne_zero he)

end

end MeasureTheory.Lp
