import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Fractional absolute moments and characteristic functions

For `0 < r < 2`, the fractional absolute moment `∫ x, |x|ʳ dμ` of a real
probability measure can be expressed using the real part of its characteristic
function `ϕ_μ` by means of the identity:

`∫ x, |x|ʳ dμ = Cᵣ ∫ t in (0, ∞), (1 - Re(ϕ_μ(t))) / t ^ (r + 1) dt`,

where

`Cᵣ = (∫ t in (0, ∞), (1 - cos(t)) / t ^ (r + 1) dt)⁻¹`.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- The normalization constant `Cᵣ` in the cosine-kernel representation of `|x| ^ r`. -/
noncomputable def fractionalAbsMomentConst (r : ℝ) : ℝ :=
  (∫ t in Set.Ioi (0 : ℝ), (1 - Real.cos t) / t ^ (r + 1))⁻¹

/-- Near zero, the cosine kernel is bounded by a constant multiple of `t ^ (1 - r)`. -/
private lemma integrableOn_one_sub_cos_div_rpow_Ioo
    {r : ℝ} (hr_lt_two : r < 2) :
    IntegrableOn
      (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1))
      (Set.Ioo 0 1) := by
  have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (1 - r)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  have hmajor := hpow.const_mul (1 / 2 : ℝ)
  have hden_cont : ContinuousOn (fun t : ℝ ↦ t ^ (r + 1)) (Set.Ioo 0 1) :=
    continuousOn_id.rpow_const fun t ht ↦ Or.inl ht.1.ne'
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1))
      (volume.restrict (Set.Ioo 0 1)) :=
    ((continuousOn_const.sub Real.continuous_cos.continuousOn).div hden_cont
      (fun t ht ↦ (Real.rpow_pos_of_pos ht.1 _).ne')).aestronglyMeasurable measurableSet_Ioo
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hden_pos : 0 < t ^ (r + 1) := Real.rpow_pos_of_pos ht.1 _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) hden_pos.le)]
  have hrpow : t ^ 2 / t ^ (r + 1) = t ^ (1 - r) := by
    rw [← Real.rpow_two, ← Real.rpow_sub ht.1]
    congr 1
    ring
  calc
    (1 - Real.cos t) / t ^ (r + 1) ≤ (t ^ 2 / 2) / t ^ (r + 1) :=
      (div_le_div_iff_of_pos_right hden_pos).2 (by
        linarith [Real.one_sub_sq_div_two_le_cos (x := t)])
    _ = 1 / 2 * (t ^ 2 / t ^ (r + 1)) := by ring
    _ = 1 / 2 * t ^ (1 - r) := by rw [hrpow]

/-- At infinity, the cosine kernel is bounded by a constant multiple of `t ^ (-(r + 1))`. -/
private lemma integrableOn_one_sub_cos_div_rpow_Ioi_one
    {r : ℝ} (hr_pos : 0 < r) :
    IntegrableOn
      (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1))
      (Set.Ioi 1) := by
  have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (-(r + 1))) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by linarith)
  have hmajor := hpow.const_mul (2 : ℝ)
  have hr_one_nonneg : 0 ≤ r + 1 := by linarith
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1))
      (volume.restrict (Set.Ioi 1)) :=
    ((measurable_const.sub Real.continuous_cos.measurable).div
      (Real.continuous_rpow_const hr_one_nonneg).measurable).aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t := zero_lt_one.trans ht
  have hden_pos : 0 < t ^ (r + 1) := Real.rpow_pos_of_pos ht_pos _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) hden_pos.le)]
  calc
    (1 - Real.cos t) / t ^ (r + 1) ≤ 2 / t ^ (r + 1) :=
      (div_le_div_iff_of_pos_right hden_pos).2 (by
        linarith [Real.neg_one_le_cos t])
    _ = 2 * t ^ (-(r + 1)) := by rw [Real.rpow_neg ht_pos.le]; ring

/-- The cosine kernel is integrable on the positive half-line when `0 < r < 2`. -/
lemma integrableOn_one_sub_cos_div_rpow
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) :
    IntegrableOn
      (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1))
      (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr
      (integrableOn_one_sub_cos_div_rpow_Ioo hr_lt_two)
  · exact integrableOn_one_sub_cos_div_rpow_Ioi_one hr_pos

/-- The integral of the cosine kernel is positive because the kernel is positive on `(1 / 2, 1)`. -/
private lemma integral_one_sub_cos_div_rpow_pos
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) :
    0 < ∫ t in Set.Ioi (0 : ℝ), (1 - Real.cos t) / t ^ (r + 1) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
      (Real.rpow_nonneg ht.le _)
  have hintegrable := integrableOn_one_sub_cos_div_rpow hr_pos hr_lt_two
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hintegrable]
  have hsubset : Set.Ioo (1 / 2 : ℝ) 1 ⊆
      Function.support (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1)) ∩ Set.Ioi 0 := by
    intro t ht
    constructor
    · change (1 - Real.cos t) / t ^ (r + 1) ≠ 0
      have ht_pos : 0 < t := (by norm_num : (0 : ℝ) < 1 / 2).trans ht.1
      have hneg : -(2 * Real.pi) < t := by nlinarith [Real.pi_pos]
      have hlt : t < 2 * Real.pi := ht.2.trans (by nlinarith [Real.two_le_pi])
      have hcos_ne : Real.cos t ≠ 1 := by
        intro hcos
        exact ht_pos.ne' ((Real.cos_eq_one_iff_of_lt_of_lt hneg hlt).mp hcos)
      exact div_ne_zero (sub_ne_zero.mpr hcos_ne.symm)
        (Real.rpow_pos_of_pos ht_pos _).ne'
    · exact (by norm_num : (0 : ℝ) < 1 / 2).trans ht.1
  have hvol : 0 < volume (Set.Ioo (1 / 2 : ℝ) 1) := by
    rw [Real.volume_Ioo]
    norm_num
  exact hvol.trans_le (measure_mono hsubset)

/-- The normalization constant in the fractional absolute-moment identity is positive. -/
lemma fractionalAbsMomentConst_pos
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) :
    0 < fractionalAbsMomentConst r := by
  exact inv_pos.mpr (integral_one_sub_cos_div_rpow_pos hr_pos hr_lt_two)

/-- Scaling the argument of the cosine kernel multiplies its integral by `|x| ^ r`. -/
lemma integral_one_sub_cos_mul_div_rpow
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) (x : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        (1 - Real.cos (t * x)) / t ^ (r + 1)) =
      |x| ^ r *
        ∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos t) / t ^ (r + 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow hr_pos.ne']
  · have hxabs : 0 < |x| := abs_pos.mpr hx
    have hcomp : IntegrableOn
        (fun t : ℝ ↦ (1 - Real.cos (|x| * t)) / (|x| * t) ^ (r + 1))
        (Set.Ioi 0) := by
      exact (integrableOn_Ioi_comp_mul_left_iff
        (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1)) 0 hxabs).2
        (by simpa using integrableOn_one_sub_cos_div_rpow hr_pos hr_lt_two)
    have hchange := integral_comp_mul_left_Ioi
      (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1)) 0 hxabs
    have hchange' :
        (∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos (|x| * t)) / (|x| * t) ^ (r + 1)) =
          |x|⁻¹ * ∫ t in Set.Ioi (0 : ℝ),
            (1 - Real.cos t) / t ^ (r + 1) := by
      simpa [smul_eq_mul] using hchange
    calc
      (∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos (t * x)) / t ^ (r + 1)) =
          ∫ t in Set.Ioi (0 : ℝ), |x| ^ (r + 1) *
            ((1 - Real.cos (|x| * t)) / (|x| * t) ^ (r + 1)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            have hcos : Real.cos (|x| * t) = Real.cos (t * x) := by
              calc
                Real.cos (|x| * t) = Real.cos |x * t| := by
                  rw [abs_mul, (abs_of_pos ht : |t| = t)]
                _ = Real.cos (x * t) := Real.cos_abs _
                _ = Real.cos (t * x) := by rw [mul_comm]
            change (1 - Real.cos (t * x)) / t ^ (r + 1) =
              |x| ^ (r + 1) *
                ((1 - Real.cos (|x| * t)) / (|x| * t) ^ (r + 1))
            rw [hcos, Real.mul_rpow (abs_nonneg x) ht.le]
            have hx_rpow_ne : |x| ^ (r + 1) ≠ 0 := (Real.rpow_pos_of_pos hxabs _).ne'
            have ht_rpow_ne : t ^ (r + 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
            field_simp
      _ = |x| ^ (r + 1) * ∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos (|x| * t)) / (|x| * t) ^ (r + 1) :=
        by simpa [smul_eq_mul] using hcomp.integral_smul (|x| ^ (r + 1))
      _ = |x| ^ r * ∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos t) / t ^ (r + 1) := by
        rw [hchange', Real.rpow_add hxabs, Real.rpow_one]
        field_simp

/-- The fractional power `|x| ^ r` is represented by the normalized cosine kernel. -/
lemma abs_rpow_eq_fractionalAbsMomentConst_mul_integral
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) (x : ℝ) :
    |x| ^ r =
      fractionalAbsMomentConst r *
        ∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos (t * x)) / t ^ (r + 1) := by
  rw [integral_one_sub_cos_mul_div_rpow hr_pos hr_lt_two]
  rw [fractionalAbsMomentConst]
  have hintegral_ne : (∫ t in Set.Ioi (0 : ℝ),
      (1 - Real.cos t) / t ^ (r + 1)) ≠ 0 :=
    (integral_one_sub_cos_div_rpow_pos hr_pos hr_lt_two).ne'
  field_simp

/-- For fixed `x`, the scaled cosine kernel is integrable on the positive half-line. -/
private lemma integrableOn_one_sub_cos_mul_div_rpow
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) (x : ℝ) :
    IntegrableOn
      (fun t : ℝ ↦ (1 - Real.cos (t * x)) / t ^ (r + 1))
      (Set.Ioi 0) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxabs : 0 < |x| := abs_pos.mpr hx
    have hcomp : IntegrableOn
        (fun t : ℝ ↦ (1 - Real.cos (|x| * t)) / (|x| * t) ^ (r + 1))
        (Set.Ioi 0) := by
      exact (integrableOn_Ioi_comp_mul_left_iff
        (fun t : ℝ ↦ (1 - Real.cos t) / t ^ (r + 1)) 0 hxabs).2
        (by simpa using integrableOn_one_sub_cos_div_rpow hr_pos hr_lt_two)
    have hscaled := hcomp.const_mul (|x| ^ (r + 1))
    apply hscaled.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hcos : Real.cos (|x| * t) = Real.cos (t * x) := by
      calc
        Real.cos (|x| * t) = Real.cos |x * t| := by
          rw [abs_mul, (abs_of_pos ht : |t| = t)]
        _ = Real.cos (x * t) := Real.cos_abs _
        _ = Real.cos (t * x) := by rw [mul_comm]
    rw [hcos, Real.mul_rpow (abs_nonneg x) ht.le]
    have hx_rpow_ne : |x| ^ (r + 1) ≠ 0 := (Real.rpow_pos_of_pos hxabs _).ne'
    have ht_rpow_ne : t ^ (r + 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    field_simp

/-- Integrating the cosine kernel in `x` gives the corresponding characteristic-function kernel. -/
private lemma integral_one_sub_cos_mul_div_rpow_eq_charFun_kernel
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (r t : ℝ) :
    (∫ x : ℝ, (1 - Real.cos (t * x)) / t ^ (r + 1) ∂μ) =
      (1 - (charFun μ t).re) / t ^ (r + 1) := by
  have hexp : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    simp [Complex.norm_exp]
  have hcos : Integrable (fun x : ℝ ↦ Real.cos (t * x)) μ := by
    convert hexp.re using 1
    funext x
    rw [← Complex.ofReal_mul]
    exact (Complex.exp_ofReal_mul_I_re (t * x)).symm
  rw [integral_div]
  rw [integral_sub (integrable_const 1) hcos]
  rw [integral_const, probReal_univ, one_smul]
  have hchar : (∫ x : ℝ, Real.cos (t * x) ∂μ) = (charFun μ t).re := by
    rw [charFun_apply_real]
    calc
      (∫ x : ℝ, Real.cos (t * x) ∂μ) =
          ∫ x : ℝ, (Complex.exp (t * x * Complex.I)).re ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [← Complex.ofReal_mul]
            exact (Complex.exp_ofReal_mul_I_re (t * x)).symm
      _ = (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂μ).re := by
        simpa using integral_re hexp
  rw [hchar]

/-- Tonelli's theorem gives the fractional absolute-moment identity for extended integrals. -/
private lemma lintegral_abs_rpow_eq_fractionalAbsMomentConst_mul_lintegral_charFun_kernel
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) :
    (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ r) ∂μ) =
      ENNReal.ofReal (fractionalAbsMomentConst r) *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((1 - (charFun μ t).re) / t ^ (r + 1)) := by
  have hconst_pos := fractionalAbsMomentConst_pos hr_pos hr_lt_two
  have hr_one_nonneg : 0 ≤ r + 1 := by linarith
  have hkernel_meas : Measurable (fun z : ℝ × ℝ ↦
      ENNReal.ofReal ((1 - Real.cos (z.2 * z.1)) / z.2 ^ (r + 1))) := by
    apply Measurable.ennreal_ofReal
    exact (measurable_const.sub
      (Real.continuous_cos.measurable.comp (measurable_snd.mul measurable_fst))).div
      ((Real.continuous_rpow_const hr_one_nonneg).measurable.comp measurable_snd)
  have hfiber (x : ℝ) :
      ENNReal.ofReal (|x| ^ r) = ENNReal.ofReal (fractionalAbsMomentConst r) *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((1 - Real.cos (t * x)) / t ^ (r + 1)) := by
    rw [abs_rpow_eq_fractionalAbsMomentConst_mul_integral hr_pos hr_lt_two x]
    rw [ENNReal.ofReal_mul hconst_pos.le]
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
        fun t : ℝ ↦ (1 - Real.cos (t * x)) / t ^ (r + 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
        (Real.rpow_nonneg ht.le _)
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrableOn_one_sub_cos_mul_div_rpow hr_pos hr_lt_two x) hnonneg]
  rw [lintegral_congr hfiber]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap hkernel_meas.aemeasurable]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht_pos : 0 < t := ht
  have hinner_meas : AEStronglyMeasurable
      (fun x : ℝ ↦ (1 - Real.cos (t * x)) / t ^ (r + 1)) μ := by
    fun_prop
  have hinner_nonneg : 0 ≤ᵐ[μ]
      fun x : ℝ ↦ (1 - Real.cos (t * x)) / t ^ (r + 1) :=
    Filter.Eventually.of_forall fun x ↦ div_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg ht_pos.le _)
  have hinner_int : Integrable
      (fun x : ℝ ↦ (1 - Real.cos (t * x)) / t ^ (r + 1)) μ := by
    apply Integrable.of_bound hinner_meas (2 / t ^ (r + 1))
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg ht_pos.le _))]
    gcongr
    linarith [Real.neg_one_le_cos (t * x)]
  change (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 - Real.cos (t * x)) / t ^ (r + 1)) ∂μ) =
    ENNReal.ofReal ((1 - (charFun μ t).re) / t ^ (r + 1))
  rw [← ofReal_integral_eq_lintegral_ofReal hinner_int hinner_nonneg]
  rw [integral_one_sub_cos_mul_div_rpow_eq_charFun_kernel r t]

/-- The characteristic-function kernel is a.e.-strongly measurable on the positive half-line. -/
private lemma aestronglyMeasurable_charFun_kernel
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr_pos : 0 < r) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (1 - (charFun μ t).re) / t ^ (r + 1))
      (volume.restrict (Set.Ioi 0)) := by
  exact (measurable_const.sub
    (Complex.continuous_re.measurable.comp (measurable_charFun (μ := μ)))).div
    (Real.continuous_rpow_const (by linarith)).measurable |>.aestronglyMeasurable

/-- The real part of a characteristic function is at most one, so its kernel is nonnegative. -/
private lemma charFun_kernel_nonneg
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} :
    0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ ↦ (1 - (charFun μ t).re) / t ^ (r + 1) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact div_nonneg
    (sub_nonneg.mpr ((charFun μ t).re_le_norm.trans (norm_charFun_le_one t)))
    (Real.rpow_nonneg ht.le _)

/-- A probability measure has a finite fractional absolute `r`-moment exactly when
its characteristic-function kernel is integrable on the positive half-line. -/
lemma integrable_abs_rpow_iff_integrableOn_charFun_kernel
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2) :
    Integrable (fun x : ℝ ↦ |x| ^ r) μ ↔
      IntegrableOn
        (fun t : ℝ ↦
          (1 - (charFun μ t).re) / t ^ (r + 1))
        (Set.Ioi 0) := by
  have hmoment_meas : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ r) μ := by
    exact ((Real.continuous_rpow_const hr_pos.le).comp continuous_abs).aestronglyMeasurable
  have hmoment_nonneg : 0 ≤ᵐ[μ] fun x : ℝ ↦ |x| ^ r :=
    Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg x) r
  rw [← lintegral_ofReal_ne_top_iff_integrable hmoment_meas hmoment_nonneg]
  change (∫⁻ a : ℝ, ENNReal.ofReal (|a| ^ r) ∂μ) ≠ ⊤ ↔
    Integrable (fun t : ℝ ↦ (1 - (charFun μ t).re) / t ^ (r + 1))
      (volume.restrict (Set.Ioi 0))
  rw [← lintegral_ofReal_ne_top_iff_integrable
    (aestronglyMeasurable_charFun_kernel hr_pos) charFun_kernel_nonneg]
  rw [lintegral_abs_rpow_eq_fractionalAbsMomentConst_mul_lintegral_charFun_kernel
    hr_pos hr_lt_two]
  have hconst_pos := fractionalAbsMomentConst_pos hr_pos hr_lt_two
  simp [ENNReal.mul_eq_top, ENNReal.ofReal_eq_zero, hconst_pos]

/-- The finite fractional absolute `r`-moment is `Cᵣ` times the integral of the
characteristic-function kernel on the positive half-line. -/
lemma integral_abs_rpow_eq_fractionalAbsMomentConst_mul_integral_charFun_kernel
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_two : r < 2)
    (hμ : Integrable (fun x : ℝ ↦ |x| ^ r) μ) :
    (∫ x : ℝ, |x| ^ r ∂μ) =
      fractionalAbsMomentConst r *
        ∫ t in Set.Ioi (0 : ℝ),
          (1 - (charFun μ t).re) / t ^ (r + 1) := by
  have hkernel :=
    (integrable_abs_rpow_iff_integrableOn_charFun_kernel hr_pos hr_lt_two).mp hμ
  have hmoment_nonneg : 0 ≤ᵐ[μ] fun x : ℝ ↦ |x| ^ r :=
    Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg x) r
  have hmoment_lintegral :=
    ofReal_integral_eq_lintegral_ofReal hμ hmoment_nonneg
  have hkernel_lintegral :=
    ofReal_integral_eq_lintegral_ofReal hkernel charFun_kernel_nonneg
  have hleft : 0 ≤ ∫ x : ℝ, |x| ^ r ∂μ := integral_nonneg_of_ae hmoment_nonneg
  have hright : 0 ≤ fractionalAbsMomentConst r *
      ∫ t in Set.Ioi (0 : ℝ), (1 - (charFun μ t).re) / t ^ (r + 1) :=
    mul_nonneg (fractionalAbsMomentConst_pos hr_pos hr_lt_two).le
      (integral_nonneg_of_ae charFun_kernel_nonneg)
  rw [← ENNReal.ofReal_eq_ofReal_iff hleft hright]
  rw [ENNReal.ofReal_mul (fractionalAbsMomentConst_pos hr_pos hr_lt_two).le]
  rw [hmoment_lintegral, hkernel_lintegral]
  rw [lintegral_abs_rpow_eq_fractionalAbsMomentConst_mul_lintegral_charFun_kernel
    hr_pos hr_lt_two]

end ProbabilityTheory
