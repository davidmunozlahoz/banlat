/-
Authors: Pedro Tradacete
-/

import BanLat.Bidual.Order
import BanLat.Examples.Lp.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Weak compactness of order intervals in `L¹`

Multiplication by the square root of a positive integrable function maps an `L²`
order interval onto its `L¹` order interval. Reflexivity of `L²` therefore gives
weak compactness of order intervals in `L¹`, for arbitrary measures.
-/

noncomputable section

open Set Filter Topology MeasureTheory

universe u

namespace MeasureTheory.Lp

/-- The square root of the modulus of an integrable real function is square integrable. -/
private theorem memLp_sqrt_abs_l1 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Lp ℝ 1 μ) : MemLp (fun ω ↦ Real.sqrt |x ω|) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω ↦ Real.sqrt |x ω|) μ :=
    (Real.continuous_sqrt.comp continuous_abs).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable x)
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [Real.sq_sqrt (abs_nonneg _), Real.norm_eq_abs] using
    (memLp_one_iff_integrable.mp (Lp.memLp x)).norm

/-- For `0 ≤ a ≤ b`, division by `√b` gives a factor in `[0, √b]` whose product with
`√b` is `a`, including when `b = 0`. -/
private theorem sqrt_div_factor {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ a / Real.sqrt b ∧ a / Real.sqrt b ≤ Real.sqrt b ∧
      Real.sqrt b * (a / Real.sqrt b) = a := by
  by_cases hb : b = 0
  · have ha0 : a = 0 := le_antisymm (hab.trans_eq hb) ha
    simp [hb, ha0]
  · have hbp : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
    have hg : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbp
    exact ⟨div_nonneg ha hg.le,
      (div_le_iff₀ hg).mpr (by simpa only [Real.mul_self_sqrt hbp.le] using hab),
      mul_div_cancel₀ a hg.ne'⟩

/-- The square root of the modulus of an `L¹` function, viewed as an element of `L²`. -/
private def l1Sqrt {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (x : Lp ℝ 1 μ) : Lp ℝ 2 μ :=
  (memLp_sqrt_abs_l1 μ x).toLp (fun ω ↦ Real.sqrt |x ω|)

/-- Every function in the `L¹` interval `[0, x]` factors as `√|x|` times an `L²`
function lying between zero and `√|x|`. -/
private theorem l1_interval_l2_factor {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Lp ℝ 1 μ) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    ∃ h : Lp ℝ 2 μ, h ∈ Icc 0 (l1Sqrt μ x) ∧
      ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x)) h = y := by
  let q : Ω → ℝ := fun ω ↦ y ω / Real.sqrt |x ω|
  have hpt : ∀ᵐ ω ∂μ, 0 ≤ q ω ∧ q ω ≤ Real.sqrt |x ω| ∧
      Real.sqrt |x ω| * q ω = y ω :=
    ((Lp.coeFn_nonneg y).mpr hy0 |>.and ((Lp.coeFn_le y x).mpr hyx)).mono
      (fun ω h ↦ by simpa only [q, abs_of_nonneg (h.1.trans h.2)] using
        sqrt_div_factor h.1 h.2)
  have hm : AEStronglyMeasurable q μ :=
    (Lp.aestronglyMeasurable y).div₀ (memLp_sqrt_abs_l1 μ x).aestronglyMeasurable
  have hq : MemLp q 2 μ := (memLp_sqrt_abs_l1 μ x).mono' hm
    (hpt.mono (fun ω h ↦ by simpa only [Real.norm_of_nonneg h.1] using h.2.1))
  have heq : ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x))
      (hq.toLp q) = y := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1)
      (l1Sqrt μ x) (hq.toLp q), (memLp_sqrt_abs_l1 μ x).coeFn_toLp,
      hq.coeFn_toLp, hpt] with ω hprod hg hh hpoint
    exact hprod.trans (by simpa only [ContinuousLinearMap.mul_apply', l1Sqrt, hg, hh]
      using hpoint.2.2)
  refine ⟨hq.toLp q, ?_, heq⟩
  exact ⟨(Lp.coeFn_nonneg _).mp ((hq.coeFn_toLp.and hpt).mono
      (fun ω h ↦ h.1 ▸ h.2.1)),
    (Lp.coeFn_le _ _).mp
      (((hq.coeFn_toLp.and (memLp_sqrt_abs_l1 μ x).coeFn_toLp).and hpt).mono
        (fun ω h ↦ by simpa only [l1Sqrt, h.1.1, h.1.2] using h.2.2.1))⟩

/-- For positive `x`, multiplication by `√x` maps the `L²` interval `[0, √x]` onto
the `L¹` interval `[0, x]`. -/
private theorem l1SqrtMultiply_image_Icc {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x)) ''
      Icc 0 (l1Sqrt μ x) = Icc 0 x := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hb : ∀ᵐ ω ∂μ, 0 ≤
        (((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x)) h) ω ∧
        (((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x)) h) ω ≤ x ω := by
      filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1)
        (l1Sqrt μ x) h, (memLp_sqrt_abs_l1 μ x).coeFn_toLp,
        (Lp.coeFn_nonneg h).mpr hh.1, (Lp.coeFn_le h (l1Sqrt μ x)).mpr hh.2,
        (Lp.coeFn_nonneg x).mpr hx] with ω hprod hg h0 hle hx0
      rw [show (((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x)) h) ω =
        (l1Sqrt μ x) ω * h ω from hprod]
      rw [show (l1Sqrt μ x) ω = Real.sqrt |x ω| from hg] at hle ⊢
      exact ⟨mul_nonneg (Real.sqrt_nonneg _) h0,
        (mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)).trans_eq
          ((Real.mul_self_sqrt (abs_nonneg _)).trans (abs_of_nonneg hx0))⟩
    exact ⟨(Lp.coeFn_nonneg _).mp (hb.mono (fun _ h ↦ h.1)),
      (Lp.coeFn_le _ _).mp (hb.mono (fun _ h ↦ h.2))⟩
  · intro hy
    exact l1_interval_l2_factor μ x y hy.1 hy.2

/-- The canonical bidual embedding of real `L²` is surjective, by the Hilbert space
representation of continuous linear functionals. -/
private theorem inclusion_surjective_l2 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) :
    Function.Surjective (BidualSpace.inclusion (X := Lp ℝ 2 μ)) := by
  intro F
  let e := InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)
  let f : StrongDual ℝ (Lp ℝ 2 μ) := F.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let y := e.symm f
  refine ⟨y, ?_⟩
  ext φ
  let x := e.symm φ
  have hx : e x = φ := e.apply_symm_apply φ
  change φ y = F φ
  rw [← hx]
  change e x y = F (e x)
  calc
    e x y = e y x := by
      simpa [e, InnerProductSpace.toDual_apply_apply] using
        (real_inner_comm x y).symm
    _ = f x := by rw [show e y = f from e.apply_symm_apply f]
    _ = F (e x) := rfl

/-- Positive order intervals in real `L²` are weakly compact for arbitrary measures. -/
private theorem isCompact_toWeakSpace_Icc_l2 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Lp ℝ 2 μ) (hx : 0 ≤ x) :
    IsCompact (toWeakSpace ℝ (Lp ℝ 2 μ) '' Icc 0 x) := by
  apply BidualSpace.isCompact_Icc_of_image_inclusion_Icc _ x hx
  apply BidualSpace.image_inclusion_Icc_iff_range_eq_orderIdeal.mpr
  exact ⟨⊤, Set.range_eq_univ.mpr (inclusion_surjective_l2 μ)⟩

/-- Positive order intervals in `L¹` are weakly compact for arbitrary measures. -/
theorem isCompact_toWeakSpace_Icc_zero {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    IsCompact (toWeakSpace ℝ (Lp ℝ 1 μ) '' Icc 0 x) := by
  have hg : 0 ≤ l1Sqrt μ x := (Lp.coeFn_nonneg _).mp
    ((memLp_sqrt_abs_l1 μ x).coeFn_toLp.mono (fun ω h ↦
      by simpa only [l1Sqrt, h, Pi.zero_apply] using Real.sqrt_nonneg |x ω|))
  let T := (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (l1Sqrt μ x)
  have hc := (isCompact_toWeakSpace_Icc_l2 μ (l1Sqrt μ x) hg).image
    (WeakSpace.map T).continuous
  rw [Set.image_image] at hc
  have hm : (fun z ↦ WeakSpace.map T (toWeakSpace ℝ (Lp ℝ 2 μ) z)) =
      (toWeakSpace ℝ (Lp ℝ 1 μ)) ∘ T := rfl
  rw [hm] at hc
  change IsCompact ((fun z ↦ toWeakSpace ℝ (Lp ℝ 1 μ) (T z)) ''
    Icc 0 (l1Sqrt μ x)) at hc
  rw [← Set.image_image (toWeakSpace ℝ (Lp ℝ 1 μ)) T] at hc
  rw [show T '' Icc 0 (l1Sqrt μ x) = Icc 0 x from l1SqrtMultiply_image_Icc μ x hx] at hc
  exact hc

end MeasureTheory.Lp
