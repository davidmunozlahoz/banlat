/-
Authors: David Muñoz-Lahoz, Jesús Illescas-Fiorito
-/

import BanLat.ALSpace.Basic
import BanLat.ALpSpace.Basic
import BanLat.Normed
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lᵖ` spaces as Banach lattices

For a measure space `(α, μ)` and `1 ≤ p ≤ ∞`, the space `Lᵖ(μ; ℝ)` of real-valued
`Lᵖ` functions is a Banach lattice under the pointwise order and the `Lᵖ` norm.

Some simple properties about indicator functions in `Lᵖ(μ; ℝ)` are deduced.
Extension by zero embeds `Lᵖ` over a restricted measure into the original space,
preserving distances and order.

Moreover:
* `L¹` is an AL-space.
* `Lᵖ` is an ALₚ-space for `1 ≤ p < ∞`.
-/

open MeasureTheory Filter

open scoped NNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Lattice and order structure

Mathlib provides `Lattice (Lp ℝ p μ)`, `IsOrderedAddMonoid (Lp ℝ p μ)`,
`HasSolidNorm (Lp ℝ p μ)`, `NormedAddCommGroup (Lp ℝ p μ)`, and
`CompleteSpace (Lp ℝ p μ)` via `MeasureTheory.Lp.instLattice`,
`MeasureTheory.Lp.instHasSolidNorm`, and
`MeasureTheory.Lp.instCompleteSpace`.
-/

/-! ### Vector lattice -/

/-- `Lᵖ(μ; ℝ)` is a vector lattice. -/
noncomputable instance instVectorLatticeLp : VectorLattice (Lp ℝ p μ) where
  smul_le_smul_of_nonneg_left a ha x y hxy := by
    rw [← Lp.coeFn_le] at hxy ⊢
    filter_upwards [Lp.coeFn_smul a x, Lp.coeFn_smul a y, hxy] with i h1 h2 h3
    rw [h1, h2]
    exact smul_le_smul_of_nonneg_left h3 ha

/-! ### Normed vector lattice -/

/-- `Lᵖ(μ; ℝ)` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeLp :
    NormedVectorLattice (Lp ℝ p μ) where

/-! ### Banach lattice -/

/-- `Lᵖ(μ; ℝ)` is a Banach lattice. -/
noncomputable instance instBanachLatticeLp : BanachLattice (Lp ℝ p μ) where

/-! ### p-th power of the `Lᵖ` norm formula -/

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E]

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module

omit [Fact (1 ≤ p)] in
/-- The `Lᵖ` (quasi-)norm is homogeneous under real scalar multiplication for every
exponent. -/
theorem norm_smul (r : ℝ) (f : Lp ℝ p μ) :
    ‖r • f‖ = |r| * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_smul r f),
    eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
    Lp.norm_def]

/-- The `p`-th power of the `Lᵖ`-norm as an integral. -/
lemma norm_rpow_eq_integral_norm_rpow
    {p : ℝ≥0} (hp : p ≠ 0) (f : Lp E (p : ENNReal) μ) :
    ‖f‖ ^ (p : ℝ) = ∫ x, ‖f x‖ ^ (p : ℝ) ∂μ := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
    (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top]
  rw [ENNReal.toReal_ofReal]
  · exact Real.rpow_inv_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (NNReal.coe_ne_zero.mpr hp)
  · exact Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-! ### Extension by zero -/

omit [Fact (1 ≤ p)] in
/-- Extends a class in `Lᵖ(μ.restrict s)` by zero outside `s` to a class in `Lᵖ(μ)`. -/
noncomputable def extendRestricted {s : Set α} (hs : MeasurableSet s)
    (g : Lp ℝ p (μ.restrict s)) : Lp ℝ p μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp g)).toLp (s.indicator g)

omit [Fact (1 ≤ p)] in
/-- Extension by zero is represented almost everywhere by `s.indicator g`. -/
theorem extendRestricted_coeFn {s : Set α} (hs : MeasurableSet s)
    (g : Lp ℝ p (μ.restrict s)) :
    ⇑(extendRestricted hs g) =ᵐ[μ] s.indicator g :=
  MemLp.coeFn_toLp _

/-- Extending by zero preserves the distance between restricted `Lᵖ` classes. -/
theorem isometry_extendRestricted {s : Set α} (hs : MeasurableSet s) :
    Isometry (extendRestricted (p := p) (μ := μ) hs) := by
  intro f g
  rw [extendRestricted, extendRestricted, Lp.edist_toLp_toLp, ← Set.indicator_sub',
    eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.edist_def]

omit [Fact (1 ≤ p)] in
/-- Extension by zero preserves and reflects the order on restricted `Lᵖ` classes. -/
theorem extendRestricted_le_iff {s : Set α} (hs : MeasurableSet s)
    (f g : Lp ℝ p (μ.restrict s)) :
    extendRestricted hs f ≤ extendRestricted hs g ↔ f ≤ g := by
  rw [← Lp.coeFn_le, ← Lp.coeFn_le]
  change (∀ᵐ x ∂μ, extendRestricted hs f x ≤ extendRestricted hs g x) ↔
    ∀ᵐ x ∂μ.restrict s, f x ≤ g x
  rw [ae_restrict_iff' hs]
  refine Filter.eventually_congr ?_
  filter_upwards [extendRestricted_coeFn hs f, extendRestricted_coeFn hs g] with x hfx hgx
  by_cases hx : x ∈ s <;> simp [hfx, hgx, hx]

omit [Fact (1 ≤ p)] in
/-- Extension by zero sends the zero class to the zero class. -/
theorem extendRestricted_zero {s : Set α} (hs : MeasurableSet s) :
    extendRestricted (p := p) (μ := μ) hs 0 = 0 := by
  apply Lp.ext
  exact (extendRestricted_coeFn hs 0).trans
    ((indicator_ae_eq_zero_of_restrict_ae_eq_zero hs (Lp.coeFn_zero ℝ p
      (μ.restrict s))).trans (Lp.coeFn_zero ℝ p μ).symm)

omit [Fact (1 ≤ p)] in
/-- Restricting a class that vanishes almost everywhere outside `s`, then extending
it by zero, recovers the original class. -/
theorem extendRestricted_restrict {s : Set α} (hs : MeasurableSet s)
    (f : Lp ℝ p μ) (hf : s.indicator (f : α → ℝ) =ᵐ[μ] f) :
    extendRestricted hs (((Lp.memLp f).restrict s).toLp f) = f := by
  apply Lp.ext
  exact (extendRestricted_coeFn hs _).trans
    (((ae_eq_restrict_iff_indicator_ae_eq hs).mp
      ((Lp.memLp f).restrict s).coeFn_toLp).trans hf)

/-! ### Constant indicators -/

omit [Fact (1 ≤ p)] in
/-- The indicators of a union and intersection sum to the indicators of the two sets. -/
theorem indicatorConstLp_union_add_inter {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ⊤) (hμt : μ t ≠ ⊤) (c : E) :
    indicatorConstLp p (hs.union ht) (by finiteness) c +
        indicatorConstLp p (hs.inter ht) (by finiteness) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, Set.indicator_union_add_inter]

omit [Fact (1 ≤ p)] in
/-- A real-valued constant indicator is a scalar multiple of the indicator with value one. -/
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

omit [Fact (1 ≤ p)] in
/-- Scalar multiplication can be moved into the value of a real constant indicator. -/
theorem smul_indicatorConstLp {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (r c : ℝ) :
    r • indicatorConstLp p hs hμs c = indicatorConstLp p hs hμs (r * c) := by
  rw [indicatorConstLp_eq_smul hs hμs c,
    indicatorConstLp_eq_smul hs hμs (r * c), smul_smul]

omit [Fact (1 ≤ p)] in
/-- A real constant indicator is nonnegative when its value is nonnegative. -/
theorem indicatorConstLp_nonneg {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ indicatorConstLp p hs hμs c := by
  exact (Lp.coeFn_nonneg _).mp <|
    (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)).mono
      (fun x hx ↦ hx.symm ▸ Set.indicator_nonneg (fun _ _ ↦ hc) x)

omit [Fact (1 ≤ p)] in
/-- The absolute value of a real constant indicator is obtained by taking the absolute value of
its value. -/
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

omit [Fact (1 ≤ p)] in
/-- Constant indicators of disjoint measurable sets are lattice-disjoint in real `Lᵖ`. -/
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

omit [Fact (1 ≤ p)] in
/-- A real-valued simple constant indicator is a scalar multiple of the indicator with value
one. -/
theorem simpleFunc.indicatorConst_eq_smul {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    Lp.simpleFunc.indicatorConst p hs hμs c =
      c • Lp.simpleFunc.indicatorConst p hs hμs (1 : ℝ) := by
  apply Subtype.ext
  change indicatorConstLp p hs hμs c = c • indicatorConstLp p hs hμs (1 : ℝ)
  exact indicatorConstLp_eq_smul hs hμs c

omit [Fact (1 ≤ p)] in
/-- Over a finite measure, a simple function in `Lᵖ` is the sum of its constant fiber indicators. -/
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

omit [Fact (1 ≤ p)] in
/-- Simple functions with disjoint supports define lattice-disjoint elements of real `Lᵖ`. -/
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

/-! ### Lᵖ(μ) spaces are ALₚ-spaces -/

section ALpSpace

variable {p : ℝ≥0} [Fact (1 ≤ p)]

private instance instFactOneLEENNRealALp :
    Fact (1 ≤ (p : ENNReal)) :=
  ⟨by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)⟩

/-- If `f ⟂ g`, `|f+g|ᵖ = |f|ᵖ + |g|ᵖ` a.e. -/
private lemma ae_norm_add_rpow_eq_of_isVLDisjoint
    {f g : Lp ℝ (p : ENNReal) μ} (hfg : IsVLDisjoint f g) :
    (fun x ↦ ‖(f + g) x‖ ^ (p : ℝ)) =ᵐ[μ]
      fun x ↦ ‖f x‖ ^ (p : ℝ) + ‖g x‖ ^ (p : ℝ) := by
  have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
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

/-- For every `1 ≤ p < ∞`, the real space `Lᵖ(μ)` is an ALₚ-space -/
noncomputable instance instALpSpaceLp :
    ALpSpace p (Lp ℝ (p : ENNReal) μ) where
  norm_add_rpow_eq_of_isVLDisjoint {f g} hfg := by
    have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
    rw [Lp.norm_rpow_eq_integral_norm_rpow hp, Lp.norm_rpow_eq_integral_norm_rpow hp,
      Lp.norm_rpow_eq_integral_norm_rpow hp,
      integral_congr_ae (ae_norm_add_rpow_eq_of_isVLDisjoint hfg)]
    exact integral_add ((Lp.memLp f).integrable_norm_rpow
      (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)
      ((Lp.memLp g).integrable_norm_rpow
        (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)

end ALpSpace

/-! ### AL-space -/

/-- The `L¹` norm is additive on non-negative elements, so `L¹(μ)` is an AL-space; in
particular the norm of `L¹(μ)` is order continuous. -/
noncomputable instance instALSpaceL1 : ALSpace (Lp ℝ 1 μ) :=
  instALpSpaceLp (p := (1 : NNReal))
