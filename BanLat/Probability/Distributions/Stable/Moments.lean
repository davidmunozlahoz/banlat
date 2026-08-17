import BanLat.Probability.Distributions.FractionalAbsMoments
import BanLat.Probability.Distributions.Stable.Basic

/-!
# Absolute moments of symmetric stable measures

For a measure `μ` on `ℝ` and `p > 0`, its absolute `p`-moment is defined by
means of `∫ x, |x| ^ p ∂μ`. This file characterizes the finite absolute moments
of nondegenerate symmetric `q`-stable measures with `0 < q < 2`.

The case where `q = 2` is already considered in MathLib.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {μ : Measure ℝ} {c : ℝ≥0} {q : ℝ}

private lemma integrableOn_stable_moment_kernel_Ioo_iff
    (hc : 0 < c) {r : ℝ} (hr_pos : 0 < r) (hq : 0 < q) :
    IntegrableOn
      (fun t : ℝ ↦
        (1 - Real.exp (-(c : ℝ) * t ^ q)) / t ^ (r + 1))
      (Set.Ioo 0 1) ↔
      r < q := by
  constructor
  · intro h
    have hc_real : 0 < (c : ℝ) := by exact_mod_cast hc
    have hconst_pos : 0 < (c : ℝ) * Real.exp (-(c : ℝ)) :=
      mul_pos hc_real (Real.exp_pos _)
    have hscaled : IntegrableOn
        (fun t : ℝ ↦ ((c : ℝ) * Real.exp (-(c : ℝ))) * t ^ (q - r - 1))
        (Set.Ioo 0 1) := by
      apply Integrable.mono' h
      · fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have htq_le_one : t ^ q ≤ 1 := Real.rpow_le_one ht.1.le ht.2.le hq.le
        have hu_nonneg : 0 ≤ (c : ℝ) * t ^ q :=
          mul_nonneg hc_real.le (Real.rpow_nonneg ht.1.le _)
        have hu_le : (c : ℝ) * t ^ q ≤ c := by
          simpa using mul_le_mul_of_nonneg_left htq_le_one hc_real.le
        have hexp_le : Real.exp (-(c : ℝ)) ≤ Real.exp (-((c : ℝ) * t ^ q)) :=
          Real.exp_le_exp_of_le (neg_le_neg hu_le)
        have hmul := mul_le_mul_of_nonneg_right
          (Real.add_one_le_exp ((c : ℝ) * t ^ q))
          (Real.exp_pos (-((c : ℝ) * t ^ q))).le
        have hexp_mul :
            Real.exp ((c : ℝ) * t ^ q) * Real.exp (-((c : ℝ) * t ^ q)) = 1 := by
          rw [← Real.exp_add]
          simp
        have hlinear :
            ((c : ℝ) * t ^ q) * Real.exp (-((c : ℝ) * t ^ q)) ≤
              1 - Real.exp (-((c : ℝ) * t ^ q)) := by
          rw [add_mul, one_mul, hexp_mul] at hmul
          linarith
        have hden_pos : 0 < t ^ (r + 1) := Real.rpow_pos_of_pos ht.1 _
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hconst_pos.le (Real.rpow_nonneg ht.1.le _))]
        rw [le_div_iff₀ hden_pos]
        calc
          ((c : ℝ) * Real.exp (-(c : ℝ))) * t ^ (q - r - 1) * t ^ (r + 1) =
              ((c : ℝ) * t ^ q) * Real.exp (-(c : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add ht.1]
            ring_nf
          _ ≤ ((c : ℝ) * t ^ q) * Real.exp (-((c : ℝ) * t ^ q)) := by
            exact mul_le_mul_of_nonneg_left hexp_le hu_nonneg
          _ ≤ 1 - Real.exp (-(c : ℝ) * t ^ q) := by
            simpa [neg_mul] using hlinear
    have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (q - r - 1)) (Set.Ioo 0 1) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hconst_pos.ne') _).mp hscaled
    have hexponent := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hpow
    linarith
  · intro hrq
    have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (q - r - 1)) (Set.Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
    apply Integrable.mono' (hpow.const_mul (c : ℝ))
    · exact ((measurable_const.sub (Real.continuous_exp.measurable.comp
        (measurable_const.mul (Real.continuous_rpow_const hq.le).measurable))).div
        (Real.continuous_rpow_const (by linarith)).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hu_nonneg : 0 ≤ (c : ℝ) * t ^ q :=
        mul_nonneg c.2 (Real.rpow_nonneg ht.1.le _)
      have hnum_nonneg : 0 ≤ 1 - Real.exp (-(c : ℝ) * t ^ q) := by
        rw [sub_nonneg, Real.exp_le_one_iff]
        simpa [neg_mul] using neg_nonpos.mpr hu_nonneg
      have hupper : 1 - Real.exp (-(c : ℝ) * t ^ q) ≤ (c : ℝ) * t ^ q := by
        have := Real.one_sub_le_exp_neg ((c : ℝ) * t ^ q)
        simpa [neg_mul] using (show 1 - Real.exp (-((c : ℝ) * t ^ q)) ≤
          (c : ℝ) * t ^ q by linarith)
      have hden_pos : 0 < t ^ (r + 1) := Real.rpow_pos_of_pos ht.1 _
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum_nonneg hden_pos.le)]
      rw [div_le_iff₀ hden_pos]
      calc
        1 - Real.exp (-(c : ℝ) * t ^ q) ≤ (c : ℝ) * t ^ q := hupper
        _ = (c : ℝ) * t ^ (q - r - 1) * t ^ (r + 1) := by
          rw [mul_assoc, ← Real.rpow_add ht.1]
          ring_nf

private lemma integrableOn_stable_moment_kernel_Ioi_one
    {c : ℝ≥0} {q r : ℝ} (hr_pos : 0 < r) (hq : 0 < q) :
    IntegrableOn
      (fun t : ℝ ↦
        (1 - Real.exp (-(c : ℝ) * t ^ q)) / t ^ (r + 1))
      (Set.Ioi 1) := by
  have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (-(r + 1))) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by linarith)
  apply Integrable.mono' hpow
  · exact ((measurable_const.sub (Real.continuous_exp.measurable.comp
      (measurable_const.mul (Real.continuous_rpow_const hq.le).measurable))).div
      (Real.continuous_rpow_const (by linarith)).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have hu_nonneg : 0 ≤ (c : ℝ) * t ^ q :=
      mul_nonneg c.2 (Real.rpow_nonneg ht_pos.le _)
    have hnum_nonneg : 0 ≤ 1 - Real.exp (-(c : ℝ) * t ^ q) := by
      rw [sub_nonneg, Real.exp_le_one_iff]
      simpa [neg_mul] using neg_nonpos.mpr hu_nonneg
    have hnum_le_one : 1 - Real.exp (-(c : ℝ) * t ^ q) ≤ 1 := by
      linarith [Real.exp_pos (-(c : ℝ) * t ^ q)]
    have hden_pos : 0 < t ^ (r + 1) := Real.rpow_pos_of_pos ht_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum_nonneg hden_pos.le)]
    rw [Real.rpow_neg ht_pos.le, ← one_div]
    exact div_le_div_of_nonneg_right hnum_le_one hden_pos.le

/-- The characteristic-function kernel of a nondegenerate symmetric `q`-stable
measure is integrable on the positive half-line exactly when `r < q`. -/
private lemma integrableOn_stable_moment_kernel_iff
    (hc : 0 < c) {r : ℝ} (hr_pos : 0 < r) (hq : 0 < q) :
    IntegrableOn
      (fun t : ℝ ↦
        (1 - Real.exp (-(c : ℝ) * t ^ q)) / t ^ (r + 1))
      (Set.Ioi 0) ↔
      r < q := by
  constructor
  · intro h
    have hIoc : IntegrableOn
        (fun t : ℝ ↦ (1 - Real.exp (-(c : ℝ) * t ^ q)) / t ^ (r + 1))
        (Set.Ioc 0 1) := h.mono_set Set.Ioc_subset_Ioi_self
    have hIoo := (integrableOn_Ioc_iff_integrableOn_Ioo).mp hIoc
    exact (integrableOn_stable_moment_kernel_Ioo_iff hc hr_pos hq).mp hIoo
  · intro hrq
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    apply IntegrableOn.union
    · exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr
        ((integrableOn_stable_moment_kernel_Ioo_iff hc hr_pos hq).mpr hrq)
    · exact integrableOn_stable_moment_kernel_Ioi_one hr_pos hq

namespace IsSymmetricStable

private lemma integrable_abs_rpow_iff_of_exponent_lt_two
    (hμ : IsSymmetricStable μ q c) (hc : 0 < c)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) :
    Integrable (fun x : ℝ ↦ |x| ^ r) μ ↔ r < q := by
  letI := hμ.isProbabilityMeasure
  rw [integrable_abs_rpow_iff_integrableOn_charFun_kernel hr_pos hr_lt_two]
  have hkernel : Set.EqOn
      (fun t : ℝ ↦ (1 - (charFun μ t).re) / t ^ (r + 1))
      (fun t : ℝ ↦ (1 - Real.exp (-(c : ℝ) * t ^ q)) / t ^ (r + 1))
      (Set.Ioi 0) := by
    intro t ht
    dsimp
    rw [hμ.charFun_eq, Complex.exp_ofReal_re, abs_of_pos ht]
  rw [integrableOn_congr_fun hkernel measurableSet_Ioi]
  exact integrableOn_stable_moment_kernel_iff hc hr_pos hμ.index_pos

/-- A nondegenerate symmetric `q`-stable measure with `q < 2` has a finite absolute
`r`-moment exactly when `r < q`. -/
lemma integrable_abs_rpow_iff_of_scale_pos_of_index_lt_two
    (hμ : IsSymmetricStable μ q c) (hc : 0 < c) (hq : q < 2)
    {r : ℝ} (hr_pos : 0 < r) :
    Integrable (fun x : ℝ ↦ |x| ^ r) μ ↔ r < q := by
  letI := hμ.isProbabilityMeasure
  by_cases hr_lt_two : r < 2
  · exact integrable_abs_rpow_iff_of_exponent_lt_two hμ hc hr_pos hr_lt_two
  · constructor
    · intro hr_int
      have hq_int : Integrable (fun x : ℝ ↦ |x| ^ q) μ := by
        simpa [Real.norm_eq_abs] using integrable_norm_rpow_of_le
          (f := id) aestronglyMeasurable_id hμ.index_pos.le hr_pos.le (by linarith) hr_int
      exact (lt_irrefl q
        ((integrable_abs_rpow_iff_of_exponent_lt_two hμ hc hμ.index_pos hq).mp hq_int)).elim
    · intro hrq
      linarith

end IsSymmetricStable

end ProbabilityTheory
