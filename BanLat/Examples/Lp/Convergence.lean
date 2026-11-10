/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Lp.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Convergence in `Lp E p μ`

This file establishes the following results:
* For `0 < p ≤ ∞`, convergence to `g` in the quasi-norm topology of `Lp E p μ`
  is equivalent to `‖f i - g‖ₚ → 0` and implies convergence in measure.
* For `0 < p < ∞`, if `f n x → f_lim x` almost everywhere and
  `‖f n x‖ ≤ g x` almost everywhere for every `n`, with `g : Lp ℝ p μ`,
  then `‖f n - f_lim‖ₚ → 0`.
-/

open MeasureTheory Filter

open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (0 < p)]

/-- For `0 < p ≤ ∞`, a family `f : ι → Lp E p μ` converges to `g : Lp E p μ`
in quasi-norm if and only if `‖f i - g‖ₚ → 0`. -/
theorem tendsto_quasiLp_iff_tendsto_eLpNorm
    {ι : Type*} {l : Filter ι} (f : ι → Lp E p μ) (g : Lp E p μ) :
    Tendsto f l (@nhds (Lp E p μ) (IsQuasiSeminorm.topology (Lp E p μ)) g) ↔
      Tendsto (fun i ↦ eLpNorm (⇑(f i) - ⇑g) p μ) l (nhds 0) := by
  rw [IsQuasiSeminorm.tendsto_nhds_iff,
    ← ENNReal.tendsto_toReal_zero_iff (fun i ↦ (Lp.memLp (f i)).sub (Lp.memLp g) |>.ne)]
  have hnorm (i : ι) : (eLpNorm (⇑(f i) - ⇑g) p μ).toReal = ‖f i - g‖ :=
    congrArg ENNReal.toReal (eLpNorm_congr_ae (coeFn_sub (f i) g)).symm
  simp_rw [hnorm, tendsto_order]
  exact (and_iff_right (fun a ha ↦ Eventually.of_forall fun i ↦
    ha.trans_le (IsQuasiSeminorm.norm_nonneg (f i - g)))).symm

/-- For `0 < p ≤ ∞` and `g ∈ Lᵖ(μ)`, convergence to the class
of `g` in quasi-norm is equivalent to `‖f i - g‖ₚ → 0`. -/
theorem tendsto_quasiLp_toLp_iff_tendsto_eLpNorm
    {ι : Type*} {l : Filter ι} (f : ι → Lp E p μ)
    (g : α → E) (hg : MemLp g p μ) :
    Tendsto f l
      (@nhds (Lp E p μ) (IsQuasiSeminorm.topology (Lp E p μ)) (hg.toLp g)) ↔
      Tendsto (fun i ↦ eLpNorm (⇑(f i) - g) p μ) l (nhds 0) := by
  exact (tendsto_quasiLp_iff_tendsto_eLpNorm f (hg.toLp g)).trans
    (Filter.tendsto_congr fun i ↦
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hg.coeFn_toLp))

/-! ### Convergence in measure for `0 < p ≤ ∞` -/

/-- For `0 < p ≤ ∞`, convergence in quasi-norm, `‖f i - g‖ₚ → 0`,
implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_quasiLp
    {ι : Type*} {f : ι → Lp E p μ} {g : Lp E p μ} {l : Filter ι}
    (hfg : Tendsto f l
      (@nhds (Lp E p μ) (IsQuasiSeminorm.topology (Lp E p μ)) g)) :
    TendstoInMeasure μ (fun i ↦ f i) l g := by
  exact tendstoInMeasure_of_tendsto_eLpNorm (Fact.out : 0 < p).ne'
    ((tendsto_quasiLp_iff_tendsto_eLpNorm f g).mp hfg)

/-! ### Dominated convergence for `0 < p < ∞` -/

/-- For `0 < p < ∞`, if `f n x → f_lim x` almost everywhere and
`‖f n x‖ ≤ g x` almost everywhere for every `n`, with `g : Lp ℝ p μ`,
then the integral of `‖f n x - f_lim x‖ ^ p` tends to zero. -/
private lemma tendsto_lintegral_rpow_enorm_sub_of_dominated_convergence
    (hp : p ≠ ∞) {f : ℕ → Lp E p μ} {f_lim : Lp E p μ}
    (g : Lp ℝ p μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (nhds (f_lim ω))) :
    Tendsto (fun n ↦ ∫⁻ ω, ‖f n ω - f_lim ω‖ₑ ^ p.toReal ∂μ) atTop (nhds 0) := by
  let b : α → ℝ := fun ω ↦ ‖g ω‖ + ‖f_lim ω‖
  have hb : MemLp b p μ := (Lp.memLp g).norm.add (Lp.memLp f_lim).norm
  suffices h : Tendsto (fun n ↦ ∫⁻ ω, ‖f n ω - f_lim ω‖ₑ ^ p.toReal ∂μ)
      atTop (nhds (∫⁻ _ : α, (0 : ℝ≥0∞) ∂μ)) by
    simpa only [lintegral_zero] using h
  refine tendsto_lintegral_of_dominated_convergence' (fun ω ↦ ‖b ω‖ₑ ^ p.toReal)
    (fun n ↦ ((Lp.aestronglyMeasurable (f n)).sub
      (Lp.aestronglyMeasurable f_lim)).enorm.pow_const _)
    ?_ (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (Fact.out : 0 < p).ne' hp hb).ne ?_
  · refine fun n ↦ (hbound n).mono (fun ω hω ↦ ?_)
    refine ENNReal.rpow_le_rpow ?_ ENNReal.toReal_nonneg
    have hω' : ‖f n ω‖ ≤ ‖g ω‖ :=
      hω.trans (by simpa only [Real.norm_eq_abs] using le_abs_self (g ω))
    simpa only [← ofReal_norm, b,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg (g ω)) (norm_nonneg (f_lim ω)))] using
      ENNReal.ofReal_le_ofReal ((norm_sub_le (f n ω) (f_lim ω)).trans
        (add_le_add hω' le_rfl))
  · filter_upwards [hlim] with ω hω
    have hzero : Tendsto (fun n ↦ ‖f n ω - f_lim ω‖ₑ) atTop (nhds 0) := by
      simpa only [Function.comp_def, sub_self, enorm_zero] using
        (continuous_enorm.tendsto (f_lim ω - f_lim ω)).comp
          (hω.sub tendsto_const_nhds)
    simpa only [Function.comp_def,
      ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos (Fact.out : 0 < p).ne' hp)] using
      ((@ENNReal.continuous_rpow_const p.toReal).tendsto (0 : ℝ≥0∞)).comp hzero

/-- For `0 < p < ∞`, if `f n x → f_lim x` almost everywhere and
`‖f n x‖ ≤ g x` almost everywhere for every `n`, with `g : Lp ℝ p μ`,
then `‖f n - f_lim‖ₚ → 0`. -/
theorem tendsto_quasiLp_of_dominated_convergence
    (hp : p ≠ ∞) {f : ℕ → Lp E p μ} {f_lim : Lp E p μ}
    (g : Lp ℝ p μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (nhds (f_lim ω))) :
    Tendsto f atTop
      (@nhds (Lp E p μ) (IsQuasiSeminorm.topology (Lp E p μ)) f_lim) := by
  apply (tendsto_quasiLp_iff_tendsto_eLpNorm f f_lim).mpr
  have hI := tendsto_lintegral_rpow_enorm_sub_of_dominated_convergence hp g hbound hlim
  have hroot : Tendsto
      (fun n ↦ (∫⁻ ω, ‖f n ω - f_lim ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal))
      atTop (nhds ((0 : ℝ≥0∞) ^ (1 / p.toReal))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hI
  convert hroot using 1
  · exact funext fun n ↦ eLpNorm_eq_lintegral_rpow_enorm_toReal
      (Fact.out : 0 < p).ne' hp
      ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable f_lim))
  · rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr
      (ENNReal.toReal_pos (Fact.out : 0 < p).ne' hp))]

end MeasureTheory.Lp
