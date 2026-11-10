/-
Authors: David Muñoz-Lahoz, Jesús Illescas-Fiorito
-/

import BanLat.ALSpace.Basic
import BanLat.ALpSpace.Basic
import BanLat.Normed
import BanLat.QuasiNormed.Lattice
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lp` spaces as Banach and quasi-Banach lattices

This file proves that:
* For `0 < p ≤ ∞` and every Banach space `E`, `L_p(μ; E)` is a quasi-Banach space.
* For `0 < p ≤ ∞`, `L_p(μ; ℝ)` is a quasi-Banach lattice.
* For `1 ≤ p ≤ ∞`, `L_p(μ; ℝ)` is a Banach lattice.
* For `1 ≤ p < ∞`, `L_p(μ; ℝ)` is an ALₚ-space.
-/

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {p : ENNReal}

/-! ### Lattice and order structure

Mathlib provides `Lattice (Lp ℝ p μ)` and `IsOrderedAddMonoid (Lp ℝ p μ)`
for `0 ≤ p ≤ ∞`. For `1 ≤ p ≤ ∞`, it also provides
`HasSolidNorm (Lp ℝ p μ)`, `NormedAddCommGroup (Lp ℝ p μ)`, and
`CompleteSpace (Lp ℝ p μ)` via `MeasureTheory.Lp.instLattice`,
`MeasureTheory.Lp.instHasSolidNorm`, and
`MeasureTheory.Lp.instCompleteSpace`.
-/

/-! ### Vector lattice -/

/-- For `0 ≤ p ≤ ∞`, `Lp ℝ p μ` is a vector lattice. -/
noncomputable instance instVectorLatticeLp : VectorLattice (Lp ℝ p μ) where
  smul_le_smul_of_nonneg_left a ha x y hxy := by
    rw [← Lp.coeFn_le] at hxy ⊢
    filter_upwards [Lp.coeFn_smul a x, Lp.coeFn_smul a y, hxy] with i h1 h2 h3
    rw [h1, h2]
    exact smul_le_smul_of_nonneg_left h3 ha

/-! ### Homogeneity of `‖·‖ₚ` -/

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E]

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module

/-- For `0 ≤ p ≤ ∞`, the norm functional on `Lp E p μ` satisfies
Mathlib's quasi-triangle estimate. -/
private lemma norm_add_le_LpAddConst (f g : Lp E p μ) :
    ‖f + g‖ ≤ (ENNReal.LpAddConst p).toReal * (‖f‖ + ‖g‖) := by
  rw [norm_def, norm_def, norm_def, ← ENNReal.toReal_add (eLpNorm_ne_top f) (eLpNorm_ne_top g),
    ← ENNReal.toReal_mul, eLpNorm_congr_ae (coeFn_add f g)]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top p).ne (ENNReal.add_ne_top.mpr
      ⟨eLpNorm_ne_top f, eLpNorm_ne_top g⟩)
  · exact eLpNorm_add_le' p

/-- For `0 ≤ p ≤ ∞`, the `Lᵖ` (quasi-)norm is homogeneous under real scalar
multiplication. -/
theorem norm_smul (r : ℝ) (f : Lp ℝ p μ) :
    ‖r • f‖ = |r| * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_smul r f),
    eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
    Lp.norm_def]

/-! ### Constant indicators -/

/-- For `0 ≤ p ≤ ∞`, the indicators of a union and intersection sum to the indicators
of the two sets. -/
theorem indicatorConstLp_union_add_inter {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ⊤) (hμt : μ t ≠ ⊤) (c : E) :
    indicatorConstLp p (hs.union ht) (by finiteness) c +
        indicatorConstLp p (hs.inter ht) (by finiteness) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, Set.indicator_union_add_inter]

/-- For `0 ≤ p ≤ ∞`, a real-valued constant indicator is a scalar multiple of the
indicator with value one. -/
theorem indicatorConstLp_eq_smul {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    indicatorConstLp p hs hμs c = c • indicatorConstLp p hs hμs (1 : ℝ) := by
  rw [Lp.ext_iff]
  filter_upwards [indicatorConstLp_coeFn (hs := hs) (hμs := hμs) (c := c),
    Lp.coeFn_smul c (indicatorConstLp p hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (hs := hs) (hμs := hμs) (c := (1 : ℝ))]
    with x hc hsmul hone
  rw [hc, hsmul, Pi.smul_apply, hone]
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- For `0 ≤ p ≤ ∞`, scalar multiplication can be moved into the value of a real
constant indicator. -/
theorem smul_indicatorConstLp {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (r c : ℝ) :
    r • indicatorConstLp p hs hμs c = indicatorConstLp p hs hμs (r * c) := by
  rw [indicatorConstLp_eq_smul hs hμs c,
    indicatorConstLp_eq_smul hs hμs (r * c), smul_smul]

/-- For `0 ≤ p ≤ ∞`, a real constant indicator is nonnegative when its value is nonnegative. -/
theorem indicatorConstLp_nonneg {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ indicatorConstLp p hs hμs c := by
  exact (Lp.coeFn_nonneg _).mp <|
    (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)).mono
      (fun x hx ↦ hx.symm ▸ Set.indicator_nonneg (fun _ _ ↦ hc) x)

/-- For `0 ≤ p ≤ ∞`, the absolute value of a real constant indicator is obtained by taking
the absolute value of its value. -/
theorem abs_indicatorConstLp {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    |indicatorConstLp p hs hμs c| = indicatorConstLp p hs hμs |c| := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_abs (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := s) (c := c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := s) (c := |c|)]
    with x habs hc hcabs
  rw [habs, hc, hcabs]
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- For `0 ≤ p ≤ ∞`, constant indicators of disjoint measurable sets are lattice-disjoint
in `Lp ℝ p μ`. -/
theorem indicatorConstLp_isVLDisjoint {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ⊤) (hμt : μ t ≠ ⊤)
    (hst : Disjoint s t) (c d : ℝ) :
    IsVLDisjoint (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt d) := by
  unfold IsVLDisjoint
  apply Lp.ext
  filter_upwards [Lp.coeFn_inf |indicatorConstLp p hs hμs c|
      |indicatorConstLp p ht hμt d|,
    Lp.coeFn_abs (indicatorConstLp p hs hμs c),
    Lp.coeFn_abs (indicatorConstLp p ht hμt d),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := s) (c := c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := t) (c := d),
    Lp.coeFn_zero ℝ p μ] with x hinf habsc habsd hc hd hzero
  rw [hinf, hzero]
  change min _ _ = 0
  rw [habsc, habsd, hc, hd]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.1 hst hxs
    simp [Set.indicator, hxs, hxt]
  · simp [Set.indicator, hxs]

/-- For `0 ≤ p ≤ ∞`, a real-valued simple constant indicator is a scalar multiple of the
indicator with value one. -/
theorem simpleFunc.indicatorConst_eq_smul {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    Lp.simpleFunc.indicatorConst p hs hμs c =
      c • Lp.simpleFunc.indicatorConst p hs hμs (1 : ℝ) := by
  apply Subtype.ext
  change indicatorConstLp p hs hμs c = c • indicatorConstLp p hs hμs (1 : ℝ)
  exact indicatorConstLp_eq_smul hs hμs c

/-- For `0 ≤ p ≤ ∞`, over a finite measure, a simple function in `Lᵖ` is the sum of its
constant fiber indicators. -/
theorem sum_indicatorConstLp [IsFiniteMeasure μ] (f : SimpleFunc α E) :
    (∑ c ∈ f.range, indicatorConstLp p (f.measurableSet_fiber c)
      (measure_ne_top μ _) c) = (f.memLp_of_isFiniteMeasure p μ).toLp f := by
  classical
  refine Lp.ext ?_
  grw [Lp.coeFn_fun_finsetSum, MemLp.coeFn_toLp]
  filter_upwards [(Filter.eventually_all_finset f.range).mpr (fun c _ ↦
    indicatorConstLp_coeFn (p := p) (μ := μ)
      (hs := f.measurableSet_fiber c) (hμs := measure_ne_top μ _) (c := c))] with x hx
  rw [Finset.sum_congr rfl (fun c hc ↦ hx c hc)]
  simp [Set.indicator_apply, eq_comm, f.mem_range_self x]

/-- For `0 ≤ p ≤ ∞`, simple functions with disjoint supports define lattice-disjoint
elements of `Lp ℝ p μ`. -/
theorem simpleFunc.toLp_isVLDisjoint {f g : SimpleFunc α ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hfg : Disjoint (Function.support f) (Function.support g)) :
    IsVLDisjoint (SimpleFunc.toLp f hf : Lp ℝ p μ) (SimpleFunc.toLp g hg : Lp ℝ p μ) := by
  unfold IsVLDisjoint
  apply Lp.ext
  filter_upwards [Lp.coeFn_inf |(SimpleFunc.toLp f hf : Lp ℝ p μ)|
      |(SimpleFunc.toLp g hg : Lp ℝ p μ)|,
    Lp.coeFn_abs (SimpleFunc.toLp f hf : Lp ℝ p μ),
    Lp.coeFn_abs (SimpleFunc.toLp g hg : Lp ℝ p μ), hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_zero ℝ p μ] with x hinf habsf habsg hfx hgx hzero
  rw [hinf, hzero]
  change min _ _ = 0
  rw [habsf, habsg, hfx, hgx]
  by_cases hfx0 : f x = 0
  · simp [hfx0]
  have hgx0 : g x = 0 := by
    by_contra hgx0
    exact Set.disjoint_left.1 hfg hfx0 hgx0
  simp [hgx0]

end MeasureTheory.Lp

/-! ### Norm identities for positive finite exponents -/

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E]

/-- For `0 < p < ∞`, the `p`-th power of the `L^p`-norm equals the integral of the
`p`-th power of the pointwise norm. -/
lemma norm_rpow_eq_integral_norm_rpow
    {p : ℝ≥0} (hp : p ≠ 0) (f : Lp E (p : ENNReal) μ) :
    ‖f‖ ^ (p : ℝ) = ∫ x, ‖f x‖ ^ (p : ℝ) ∂μ := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
    (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top]
  rw [ENNReal.toReal_ofReal]
  · exact Real.rpow_inv_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (NNReal.coe_ne_zero.mpr hp)
  · exact Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- For `0 < p < ∞`, lattice-disjoint elements of `Lp ℝ p μ` satisfy
`|f + g|ᵖ = |f|ᵖ + |g|ᵖ` almost everywhere. -/
private lemma ae_norm_add_rpow_eq_of_isVLDisjoint
    {p : ℝ≥0} (hp : p ≠ 0)
    {f g : Lp ℝ (p : ENNReal) μ} (hfg : IsVLDisjoint f g) :
    (fun x ↦ ‖(f + g) x‖ ^ (p : ℝ)) =ᵐ[μ]
      fun x ↦ ‖f x‖ ^ (p : ℝ) + ‖g x‖ ^ (p : ℝ) := by
  have heq : |f| ⊓ |g| = 0 := hfg
  have hzero : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0 := by
    filter_upwards [Lp.coeFn_inf |f| |g|, Lp.coeFn_abs f,
      Lp.coeFn_abs g, Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hinf hf hg hzero
    rw [heq, hzero] at hinf
    change (0 : ℝ) = min ((|f| : Lp ℝ (p : ENNReal) μ) x)
      ((|g| : Lp ℝ (p : ENNReal) μ) x) at hinf
    rw [hf, hg] at hinf
    rcases le_total |f x| |g x| with hle | hle
    · left
      exact abs_eq_zero.mp ((min_eq_left hle ▸ hinf).symm)
    · right
      exact abs_eq_zero.mp ((min_eq_right hle ▸ hinf).symm)
  filter_upwards [Lp.coeFn_add f g, hzero] with x hadd hx
  rw [hadd]
  rcases hx with hf | hg
  · simp [hf, Real.zero_rpow (NNReal.coe_ne_zero.mpr hp)]
  · simp [hg, Real.zero_rpow (NNReal.coe_ne_zero.mpr hp)]

/-- For `0 < p < ∞`, the `p`-th power of the `Lp` quasi-norm
is additive on lattice-disjoint real functions. -/
lemma norm_add_rpow_eq_of_isVLDisjoint
    {p : ℝ≥0} (hp : p ≠ 0) {f g : Lp ℝ (p : ENNReal) μ}
    (hfg : IsVLDisjoint f g) :
    ‖f + g‖ ^ (p : ℝ) = ‖f‖ ^ (p : ℝ) + ‖g‖ ^ (p : ℝ) := by
  rw [norm_rpow_eq_integral_norm_rpow hp, norm_rpow_eq_integral_norm_rpow hp,
    norm_rpow_eq_integral_norm_rpow hp,
    integral_congr_ae (ae_norm_add_rpow_eq_of_isVLDisjoint hp hfg)]
  exact integral_add ((Lp.memLp f).integrable_norm_rpow
    (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)
    ((Lp.memLp g).integrable_norm_rpow (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)

end MeasureTheory.Lp

/-! ### Quasi-norms for positive exponents and completeness for `0 < p < 1` -/

namespace MeasureTheory.Lp

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [Fact (0 < p)]

private lemma one_le_toReal_LpAddConst :
    1 ≤ (ENNReal.LpAddConst p).toReal := by
  by_cases hp : p < 1
  · rw [ENNReal.LpAddConst, ite_eq_left ⟨(Fact.out : 0 < p), hp⟩,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
    apply Real.one_le_rpow (by norm_num)
    have hp_real_le : p.toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp.le
    have hp_real_pos : 0 < p.toReal :=
      ENNReal.toReal_pos (Fact.out : 0 < p).ne' (hp.trans ENNReal.one_lt_top).ne
    rw [one_div]
    exact sub_nonneg.mpr ((one_le_inv₀ hp_real_pos).2 hp_real_le)
  · simp only [ENNReal.LpAddConst_of_one_le (le_of_not_gt hp), ENNReal.toReal_one, le_refl]

/-- For `0 < p ≤ ∞`, the usual norm functional on `Lp E p μ` is a quasi-norm. -/
instance instIsQuasiNorm : IsQuasiNorm (Lp E p μ) where
  norm_zero := MeasureTheory.Lp.norm_zero
  norm_nonneg := fun _ ↦ ENNReal.toReal_nonneg
  norm_neg := MeasureTheory.Lp.norm_neg
  exists_quasi_triangle_constant :=
    ⟨(ENNReal.LpAddConst p).toReal, one_le_toReal_LpAddConst, norm_add_le_LpAddConst⟩
  eq_zero_of_norm_eq_zero := fun _ ↦ (norm_eq_zero_iff (Fact.out : 0 < p)).mp

/-- For `0 < p ≤ ∞`, `Lp E p μ` is a quasi-normed space. -/
noncomputable instance instQuasiNormedSpace
    [NormedField 𝕜] [NormedSpace 𝕜 E] :
    QuasiNormedSpace 𝕜 (Lp E p μ) where
  toModule := MeasureTheory.Lp.instModule
  norm_smul c f := by
    rw [norm_def, eLpNorm_congr_ae (coeFn_smul c f), eLpNorm_const_smul,
      ENNReal.toReal_mul, toReal_enorm, norm_def]

/-- For `0 < p ≤ ∞`, `Lp ℝ p μ` is a quasi-normed vector lattice. -/
noncomputable instance instQuasiNormedVectorLattice :
    QuasiNormedVectorLattice (Lp ℝ p μ) where
  toVectorLattice := instVectorLatticeLp
  solid f g hfg := by
    apply norm_le_norm_of_ae_le
    rw [← coeFn_le] at hfg
    filter_upwards [coeFn_abs f, coeFn_abs g, hfg] with x hf hg hle
    simpa only [Real.norm_eq_abs, hf, hg] using hle
  norm_smul := norm_smul

section BelowOne

variable [Fact (p < 1)]

/-- For `0 < p < 1`, a sequence of almost-everywhere strongly measurable functions
with `‖dₙ‖ₚ < 2⁻ⁿ` has an integrable sum of `p`-th powers of norms. -/
private lemma lintegral_tsum_rpow_lt_top_of_geometric_eLpNorm
    {d : ℕ → α → E} (hd_meas : ∀ n, AEStronglyMeasurable (d n) μ)
    (hd_norm : ∀ n, eLpNorm (d n) p μ < ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) :
    ∫⁻ x, ∑' n, ‖d n x‖ₑ ^ p.toReal ∂μ < ∞ := by
  have hp_real_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (Fact.out : 0 < p).ne' ((Fact.out : p < 1).trans (by simp)).ne
  rw [lintegral_tsum fun n ↦ (hd_meas n).enorm.pow_const _]
  have hsum_le : (∑' n, ∫⁻ x, ‖d n x‖ₑ ^ p.toReal ∂μ) ≤
      ∑' n, (ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ p.toReal := by
    apply ENNReal.tsum_le_tsum
    intro n
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp_real_pos,
      ← eLpNorm_eq_eLpNorm' (Fact.out : 0 < p).ne'
        ((Fact.out : p < 1).trans (by simp)).ne (hd_meas n)]
    exact (ENNReal.rpow_lt_rpow (hd_norm n) hp_real_pos).le
  refine hsum_le.trans_lt ?_
  have hratio : (ENNReal.ofReal (1 / 2 : ℝ)) ^ p.toReal < 1 :=
      ENNReal.rpow_lt_one (by norm_num) hp_real_pos
  have heq (n : ℕ) : (ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ p.toReal =
      ((ENNReal.ofReal (1 / 2 : ℝ)) ^ p.toReal) ^ n := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm (n : ℝ) p.toReal,
      ENNReal.rpow_mul, ENNReal.rpow_natCast]
  simp_rw [heq]
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hratio)

/-- For `0 < p < 1`, let `d n` be almost-everywhere strongly measurable functions.
If `x ↦ ∑' n, |dₙ(x)| ^ p` has finite integral, then the sequence
`n ↦ ‖d n x‖` is summable for almost every `x`. -/
private lemma ae_summable_norm_of_lintegral_tsum_rpow_lt_top
    {d : ℕ → α → E} (hd_meas : ∀ n, AEStronglyMeasurable (d n) μ)
    (h_integral_tsum : ∫⁻ x, ∑' n, ‖d n x‖ₑ ^ p.toReal ∂μ < ∞) :
    ∀ᵐ x ∂μ, Summable fun n ↦ ‖d n x‖ := by
  have h_power_sum : ∀ᵐ x ∂μ, ∑' n, ‖d n x‖ₑ ^ p.toReal < ∞ := by
    exact ae_lt_top' (AEMeasurable.tsum fun n ↦ (hd_meas n).enorm.pow_const _) h_integral_tsum.ne
  filter_upwards [h_power_sum] with x hx
  let a : ℕ → NNReal := fun n ↦ ‖d n x‖₊
  have hp_real_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (Fact.out : 0 < p).ne' ((Fact.out : p < 1).trans (by simp)).ne
  have ha_power : Summable fun n ↦ a n ^ p.toReal := by
    apply ENNReal.tsum_coe_ne_top_iff_summable.mp
    simpa only [a, ENNReal.coe_rpow_of_nonneg _ hp_real_pos.le, enorm_eq_nnnorm] using hx.ne
  have ha_power_real : Summable fun n ↦ (a n : ℝ) ^ p.toReal := by
    simpa only [NNReal.coe_rpow] using (NNReal.summable_coe.2 ha_power)
  have hm : Memℓp (fun n ↦ ‖d n x‖) (ENNReal.ofReal p.toReal) :=
    memℓp_gen (by
      simpa only [Real.norm_of_nonneg (norm_nonneg _),
        ENNReal.toReal_ofReal ENNReal.toReal_nonneg, a, coe_nnnorm] using ha_power_real)
  exact (hm.of_exponent_ge (by
    simpa only [ENNReal.ofReal_toReal (ne_of_lt ((Fact.out : p < 1).trans
      ENNReal.one_lt_top))] using (Fact.out : p < 1).le)).summable_of_one

/-- For `0 < p < 1` and complete `E`, a Cauchy sequence in `Lp E p μ`
has a subsequence converging almost everywhere. -/
private lemma exists_ae_tendsto_subseq [CompleteSpace E] (u : ℕ → Lp E p μ)
    (hu : @CauchySeq (Lp E p μ) ℕ (IsQuasiSeminorm.uniformSpace (Lp E p μ)) _ u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : α → E, ∀ᵐ x ∂μ,
        Tendsto (fun n ↦ u (φ n) x) atTop (nhds (f x)) := by
  let r : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  have hr (n : ℕ) : 0 < r n := pow_pos (by norm_num) n
  let : UniformSpace (Lp E p μ) := IsQuasiSeminorm.uniformSpace (Lp E p μ)
  obtain ⟨φ, hφ_mono, hφ⟩ := hu.subseq_mem
    (V := fun n ↦ {z : Lp E p μ × Lp E p μ | ‖z.2 - z.1‖ < r n}) fun n ↦
      (IsQuasiSeminorm.uniformity_hasBasis (E := Lp E p μ)).mem_iff.2
        ⟨r n, hr n, Set.Subset.rfl⟩
  let d : ℕ → α → E := fun n x ↦ u (φ (n + 1)) x - u (φ n) x
  have hd_meas (n : ℕ) : AEStronglyMeasurable (d n) μ :=
    (MeasureTheory.Lp.aestronglyMeasurable (u (φ (n + 1)))).sub
      (MeasureTheory.Lp.aestronglyMeasurable (u (φ n)))
  have hd_norm (n : ℕ) : eLpNorm (d n) p μ < ENNReal.ofReal (r n) := by
    have hnorm : ‖u (φ (n + 1)) - u (φ n)‖ < r n := by
      rw [IsQuasiSeminorm.norm_sub_rev]
      exact hφ n
    rw [norm_def, eLpNorm_congr_ae
      (MeasureTheory.Lp.coeFn_sub (u (φ (n + 1))) (u (φ n)))] at hnorm
    rw [ENNReal.lt_ofReal_iff_toReal_lt]
    · exact hnorm
    · rw [show d n = ⇑(u (φ (n + 1))) - ⇑(u (φ n)) by rfl,
        ← eLpNorm_congr_ae
          (MeasureTheory.Lp.coeFn_sub (u (φ (n + 1))) (u (φ n)))]
      exact MeasureTheory.Lp.eLpNorm_ne_top (u (φ (n + 1)) - u (φ n))
  have h_norm_sum : ∀ᵐ x ∂μ, Summable fun n ↦ ‖d n x‖ :=
    ae_summable_norm_of_lintegral_tsum_rpow_lt_top hd_meas
      (lintegral_tsum_rpow_lt_top_of_geometric_eLpNorm hd_meas hd_norm)
  let f : α → E := fun x ↦ (∑' n, d n x) + u (φ 0) x
  refine ⟨φ, hφ_mono, f, h_norm_sum.mono fun x hx ↦ ?_⟩
  have hd_sum : Summable fun n ↦ d n x := Summable.of_norm hx
  have h_telescope : (fun n ↦ ∑ i ∈ Finset.range n, d i x) =
      fun n ↦ u (φ n) x - u (φ 0) x := by
    ext n
    exact Finset.sum_range_sub (fun n ↦ u (φ n) x) n
  have hlim := hd_sum.hasSum.tendsto_sum_nat
  rw [h_telescope] at hlim
  have := Filter.Tendsto.add_const (u (φ 0) x) hlim
  simpa only [sub_add_cancel, f] using this

omit [Fact (p < 1)] in
/-- For `0 < p ≤ ∞`, an almost-everywhere limit of a subsequence of a quasi-norm
Cauchy sequence `u` in `Lp E p μ` satisfies `‖u n - f‖ₚ → 0` for the entire sequence. -/
private lemma tendsto_eLpNorm_of_cauchy_ae_tendsto (u : ℕ → Lp E p μ)
    (hu : @CauchySeq (Lp E p μ) ℕ (IsQuasiSeminorm.uniformSpace (Lp E p μ)) _ u)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : α → E}
    (hf : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u (φ n) x) atTop (nhds (f x))) :
    Tendsto (fun n ↦ eLpNorm (⇑(u n) - f) p μ) atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  let δ : ℝ≥0∞ := min ε 1
  have hδ_pos : 0 < δ := lt_min hε zero_lt_one
  have hδ_top : δ ≠ ∞ := ne_of_lt (lt_of_le_of_lt (min_le_right ε 1) ENNReal.one_lt_top)
  let r : ℝ := δ.toReal / 2
  have hr : 0 < r := div_pos (ENNReal.toReal_pos hδ_pos.ne' hδ_top) (by norm_num)
  obtain ⟨N, hN⟩ := (IsQuasiSeminorm.cauchySeq_iff.mp hu) r hr
  refine ⟨N, fun n hn ↦ ?_⟩
  have h_lim : eLpNorm (⇑(u n) - f) p μ ≤
      Filter.atTop.liminf fun m ↦ eLpNorm (⇑(u n) - ⇑(u (φ m))) p μ := by
    refine eLpNorm_lim_le_liminf_eLpNorm
      (fun m ↦ (MeasureTheory.Lp.aestronglyMeasurable (u n)).sub
        (MeasureTheory.Lp.aestronglyMeasurable (u (φ m)))) (⇑(u n) - f)
      ((Lp.aestronglyMeasurable (u n)).sub
        (aestronglyMeasurable_of_tendsto_ae atTop
          (fun m ↦ Lp.aestronglyMeasurable (u (φ m))) hf)) ?_
    filter_upwards [hf] with x hx
    exact Filter.Tendsto.sub tendsto_const_nhds hx
  have h_liminf : Filter.atTop.liminf
      (fun m ↦ eLpNorm (⇑(u n) - ⇑(u (φ m))) p μ) ≤ ENNReal.ofReal r := by
    apply Filter.liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop N)] with m hm
    have hnorm : ‖u n - u (φ m)‖ < r := by
      rw [IsQuasiSeminorm.norm_sub_rev]
      exact hN n hn (φ m) hm
    rw [norm_def, eLpNorm_congr_ae
      (MeasureTheory.Lp.coeFn_sub (u n) (u (φ m)))] at hnorm
    have htop : eLpNorm (⇑(u n) - ⇑(u (φ m))) p μ ≠ ∞ := by
      rw [← eLpNorm_congr_ae (MeasureTheory.Lp.coeFn_sub (u n) (u (φ m)))]
      exact MeasureTheory.Lp.eLpNorm_ne_top (u n - u (φ m))
    exact (ENNReal.lt_ofReal_iff_toReal_lt htop).2 hnorm |>.le
  refine h_lim.trans (h_liminf.trans ?_)
  exact ((ENNReal.ofReal_le_iff_le_toReal hδ_top).2
      (by simpa only [r] using div_le_self (ENNReal.toReal_nonneg) (by norm_num))).trans
        (min_le_left ε 1)

private lemma quasiSeminormCompleteSpace_of_lt_one [CompleteSpace E] :
    QuasiSeminormCompleteSpace (Lp E p μ) := by
  apply IsQuasiSeminorm.quasiSeminormCompleteSpace_of_cauchySeq_tendsto
  intro u hu
  have hu' : @CauchySeq (Lp E p μ) ℕ (IsQuasiSeminorm.uniformSpace (Lp E p μ)) _ u :=
    IsQuasiSeminorm.cauchySeq_iff.mpr hu
  obtain ⟨φ, hφ, f, hf⟩ := exists_ae_tendsto_subseq u hu'
  have ht : Filter.Tendsto (fun n ↦ eLpNorm (⇑(u n) - f) p μ) Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_of_cauchy_ae_tendsto u hu' hφ hf
  have hf_mem : MemLp f p μ := by
    change eLpNorm f p μ < ∞
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp ht 1 zero_lt_one
    have hdiff : eLpNorm (⇑(u N) - f) p μ < ∞ :=
      (hN N le_rfl).trans_lt ENNReal.one_lt_top
    have heq : f = -(⇑(u N) - f) + ⇑(u N) := by
      funext x
      simp
    rw [heq]
    refine lt_of_le_of_lt
      (eLpNorm_add_le' p) ?_
    exact ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top p)
      (ENNReal.add_lt_top.mpr
        ⟨by simpa only [eLpNorm_neg] using hdiff,
          (MeasureTheory.Lp.eLpNorm_ne_top (u N)).lt_top⟩)
  let fLp : Lp E p μ := hf_mem.toLp f
  refine ⟨fLp, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp ht (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hε))
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun _ hn ↦ hN _ hn⟩] with n hn
  have hae : ⇑(u n - fLp) =ᵐ[μ] ⇑(u n) - f := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub (u n) fLp, hf_mem.coeFn_toLp] with x hsub hcoe
    change fLp x = f x at hcoe
    exact hsub.trans (congrArg (fun y ↦ u n x - y) hcoe)
  rw [norm_def, eLpNorm_congr_ae hae]
  calc
    (eLpNorm (⇑(u n) - f) p μ).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
    _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
    _ < ε := half_lt_self hε

end BelowOne

/-- For `0 < p ≤ ∞`, `Lp E p μ` is complete for its quasi-norm uniformity
when `E` is complete. -/
noncomputable instance instQuasiSeminormCompleteSpace [CompleteSpace E] :
    QuasiSeminormCompleteSpace (Lp E p μ) := by
  by_cases hp : p < 1
  · let : Fact (p < 1) := ⟨hp⟩
    exact quasiSeminormCompleteSpace_of_lt_one
  · let : Fact (1 ≤ p) := ⟨le_of_not_gt hp⟩
    exact IsQuasiSeminorm.instQuasiSeminormCompleteSpaceOfCompleteSpace (Lp E p μ)

/-- For `0 < p ≤ ∞`, `Lp E p μ` is a quasi-Banach space when `E` is complete. -/
noncomputable instance instQuasiBanachSpace
    [NormedField 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E] :
    QuasiBanachSpace 𝕜 (Lp E p μ) where
  toQuasiNormedSpace := instQuasiNormedSpace
  toCompleteSpace := instQuasiSeminormCompleteSpace

/-- For `0 < p ≤ ∞`, `Lp ℝ p μ` is a quasi-Banach lattice. -/
noncomputable instance instQuasiBanachLattice :
    QuasiBanachLattice (Lp ℝ p μ) where
  toQuasiNormedVectorLattice := instQuasiNormedVectorLattice
  toCompleteSpace := instQuasiSeminormCompleteSpace

end MeasureTheory.Lp

section Normed

variable [Fact (1 ≤ p)]

/-! ### Normed vector lattice -/

/-- For `1 ≤ p ≤ ∞`, `Lp ℝ p μ` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeLp :
    NormedVectorLattice (Lp ℝ p μ) where

/-! ### Banach lattice structure for `1 ≤ p ≤ ∞` -/

/-- For `1 ≤ p ≤ ∞`, `Lp ℝ p μ` is a Banach lattice. -/
noncomputable instance instBanachLatticeLp : BanachLattice (Lp ℝ p μ) where

end Normed

/-! ### Lₚ(μ) spaces are ALₚ-spaces -/

section ALpSpace

variable {p : ℝ≥0} [Fact (1 ≤ p)]

private instance instFactOneLEENNRealALp :
    Fact (1 ≤ (p : ENNReal)) :=
  ⟨by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)⟩

/-- For `1 ≤ p < ∞`, `Lp ℝ p μ` is an ALₚ-space. -/
noncomputable instance instALpSpaceLp :
    ALpSpace p (Lp ℝ (p : ENNReal) μ) where
  norm_add_rpow_eq_of_isVLDisjoint :=
    Lp.norm_add_rpow_eq_of_isVLDisjoint
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
end ALpSpace

/-! ### AL-space -/

/-- `Lp ℝ 1 μ` is an AL-space with order-continuous norm. -/
noncomputable instance instALSpaceL1 : ALSpace (Lp ℝ 1 μ) :=
  instALpSpaceLp (p := (1 : NNReal))
