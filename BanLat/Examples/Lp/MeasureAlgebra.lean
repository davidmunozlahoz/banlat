/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.OfMeasure
import BanLat.Examples.Lp.Basic
import BanLat.Operators.Hom
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.FinMeasAdditive

/-!
# Measure algebras and `Lᵖ` spaces

For a finite measure `μ` and `1 ≤ p < ∞`, every element `[A]` of the measure algebra induced by
`μ` defines a constant indicator in `Lᵖ(μ)`, independently of its measurable representative. The
map `[A] ↦ 1_A` is a uniform embedding of the measure algebra into `Lᵖ(μ)`.

An equivalence between the measure algebras induced by finite measures `μ` and `ν` extends from
simple functions to a lattice isometry between `Lᵖ(μ)` and `Lᵖ(ν)`. Moreover, this isometry maps
each constant indicator to the indicator associated with the image of its measure-algebra element.
-/

open scoped ENNReal NNReal

universe u v

/-! ## Indicators of measure-algebra elements -/

namespace MeasureTheory.Lp

variable {α : Type u} [MeasurableSpace α]
variable {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0}

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module Lp.simpleFunc.normedSpace

/-- The constant indicator in the simple-function subspace of `Lᵖ(μ)` associated with an element
of the measure algebra of `μ`, independent of the choice of measurable representative. -/
noncomputable def indicatorSimpleFunc
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    Lp.simpleFunc ℝ (p : ENNReal) μ := by
  refine Quotient.liftOn a
    (fun s : MeasuredSets μ ↦
      Lp.simpleFunc.indicatorConst (p : ENNReal) s.property (measure_ne_top μ s) c) ?_
  exact fun s t h ↦ Subtype.ext <| MemLp.toLp_congr
    (memLp_indicator_const (p : ENNReal) s.property c (Or.inr (measure_ne_top μ s)))
    (memLp_indicator_const (p : ENNReal) t.property c (Or.inr (measure_ne_top μ t))) <|
    indicator_ae_eq_of_ae_eq_set <| measure_symmDiff_eq_zero_iff.mp <|
      (MeasureAlgebra.InducedBooleanAlgebra.mk_eq_mk μ s t).mp (Quotient.sound h)

/-- For a measurable representative of an element of the measure algebra of `μ`, the abstract
indicator in `Lᵖ(μ)` agrees with `Lp.simpleFunc.indicatorConst`. -/
theorem indicatorSimpleFunc_mk
    (s : MeasuredSets μ) (c : ℝ) :
    indicatorSimpleFunc (p := p) (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) c =
      Lp.simpleFunc.indicatorConst (p : ENNReal) s.property (measure_ne_top μ s) c := by
  rfl

/-- The indicator in `Lᵖ(μ)` of the bottom element of the measure algebra of `μ` is zero. -/
theorem indicatorSimpleFunc_bot (c : ℝ) :
    indicatorSimpleFunc (μ := μ) (p := p) ⊥ c = 0 := by
  exact Subtype.ext indicatorConstLp_empty

/-- In `Lᵖ(μ)`, a constant indicator is its value times the indicator with value one. -/
theorem indicatorSimpleFunc_smul
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    indicatorSimpleFunc (p := p) a c = c • indicatorSimpleFunc a 1 := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  exact Subtype.ext (Lp.indicatorConstLp_eq_smul s.property (measure_ne_top μ s) c)

/-- Constant indicators in `Lᵖ(μ)` satisfy the valuation identity for Boolean suprema and
infima in the measure algebra of `μ`. -/
theorem indicatorSimpleFunc_valuation
    (a b : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    indicatorSimpleFunc (p := p) (a ⊔ b) c + indicatorSimpleFunc (a ⊓ b) c =
      indicatorSimpleFunc a c + indicatorSimpleFunc b c := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  obtain ⟨t, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ b
  rw [← MeasureAlgebra.InducedBooleanAlgebra.mk_sup,
    ← MeasureAlgebra.InducedBooleanAlgebra.mk_inf, indicatorSimpleFunc_mk,
    indicatorSimpleFunc_mk, indicatorSimpleFunc_mk, indicatorSimpleFunc_mk]
  exact Subtype.ext <| Lp.indicatorConstLp_union_add_inter s.property t.property
    (measure_ne_top μ s) (measure_ne_top μ t) c

/-- An abstract constant indicator in `Lᵖ(μ)` with a nonnegative value is nonnegative. -/
theorem indicatorSimpleFunc_nonneg
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ indicatorSimpleFunc (p := p) a c := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  exact Lp.indicatorConstLp_nonneg s.property (measure_ne_top μ s) hc

/-- In `Lᵖ(μ)`, constant indicators of disjoint elements of the measure algebra of `μ` are
lattice disjoint. -/
theorem indicatorSimpleFunc_isVLDisjoint
    (a b : MeasureAlgebra.InducedBooleanAlgebra μ) (hab : Disjoint a b) (c d : ℝ) :
    IsVLDisjoint (indicatorSimpleFunc (p := p) a c : Lp ℝ (p : ENNReal) μ)
      (indicatorSimpleFunc (p := p) b d : Lp ℝ (p : ENNReal) μ) := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  obtain ⟨t, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ b
  have ht : MeasureAlgebra.InducedBooleanAlgebra.mk μ (t \ s) =
      MeasureAlgebra.InducedBooleanAlgebra.mk μ t :=
    (MeasureAlgebra.InducedBooleanAlgebra.mk_sdiff μ t s).trans hab.symm.sdiff_eq_left
  rw [← ht, indicatorSimpleFunc_mk, indicatorSimpleFunc_mk]
  exact Lp.indicatorConstLp_isVLDisjoint s.property (t.property.diff s.property)
    (measure_ne_top μ s) (measure_ne_top μ (t \ s)) Set.disjoint_sdiff_right c d

/-! ### Norms and decomposition into indicators -/

/-- The `p`-norm in `Lᵖ(μ)` of an abstract constant indicator from the measure algebra of `μ`. -/
theorem norm_indicatorSimpleFunc [Fact (1 ≤ p)]
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    ‖indicatorSimpleFunc (p := p) a c‖ =
      ‖c‖ * ((MeasureAlgebra.ofMeasure μ) a).toReal ^ (1 / (p : ℝ)) := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  change ‖indicatorConstLp (p : ENNReal) s.property (measure_ne_top μ s.val) c‖ =
    ‖c‖ * (μ s.val).toReal ^ (1 / (p : ℝ))
  simpa only [ENNReal.coe_toReal, Measure.real] using
    (norm_indicatorConstLp (p := (p : ENNReal)) (hs := s.property)
      (hμs := measure_ne_top μ s.val) (c := c)
      (ENNReal.coe_ne_zero.mpr ((lt_of_lt_of_le zero_lt_one Fact.out).ne'))
      ENNReal.coe_ne_top)

/-- A simple function in `Lᵖ(μ)` decomposes as the sum of the constant indicators of its level
sets in the measure algebra of `μ`. -/
theorem simpleFunc_sum_indicators (f : SimpleFunc α ℝ) :
    (∑ c ∈ f.range, (indicatorSimpleFunc (p := p)
      (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨f ⁻¹' {c}, f.measurableSet_fiber c⟩) c :
        Lp ℝ (p : ENNReal) μ)) = (f.memLp_of_isFiniteMeasure (p : ENNReal) μ).toLp f := by
  simpa only [indicatorSimpleFunc_mk, Lp.simpleFunc.coe_indicatorConst] using
    Lp.sum_indicatorConstLp (p := (p : ENNReal)) (μ := μ) f

/-! ## Uniform embedding into `Lᵖ` -/

/-- The indicator with value one of an element of the measure algebra of `μ`,
viewed in `Lᵖ(μ)`. -/
noncomputable def algebraIndicator
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) : Lp ℝ (p : ENNReal) μ :=
  indicatorSimpleFunc (p := p) a 1

/-- In `Lᵖ(μ)`, the distance between indicators is the `μ`-measure of their symmetric difference
to the power `1/p`: `‖1_A-1_B‖ₚ = μ(A ∆ B)^{1/p}`. -/
theorem dist_algebraIndicator [Fact (1 ≤ p)]
    (a b : MeasureAlgebra.InducedBooleanAlgebra μ) :
    dist (algebraIndicator (p := p) a) (algebraIndicator b) =
      ((MeasureAlgebra.ofMeasure μ) (symmDiff a b)).toReal ^ (1 / (p : ℝ)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro s t
  have hp0 : (p : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0) ≤ p)))
  change dist (indicatorConstLp (p : ENNReal) s.property (measure_ne_top μ s) (1 : ℝ))
      (indicatorConstLp (p : ENNReal) t.property (measure_ne_top μ t) (1 : ℝ)) =
    ((MeasureAlgebra.ofMeasure μ) (symmDiff
      (MeasureAlgebra.InducedBooleanAlgebra.mk μ s)
      (MeasureAlgebra.InducedBooleanAlgebra.mk μ t))).toReal ^ (1 / (p : ℝ))
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp0 ENNReal.coe_ne_top,
    norm_one, one_mul, ENNReal.coe_toReal, symmDiff_def,
    ← MeasureAlgebra.InducedBooleanAlgebra.mk_sdiff,
    ← MeasureAlgebra.InducedBooleanAlgebra.mk_sup, MeasureAlgebra.ofMeasure_mk]
  rfl

/-- The indicator map uniformly embeds the measure algebra induced by `μ` into `Lᵖ(μ)`. -/
theorem isUniformEmbedding_algebraIndicator [Fact (1 ≤ p)] :
    letI := (MeasureAlgebra.ofMeasure μ).toMetricSpace
    IsUniformEmbedding (algebraIndicator (μ := μ) (p := p)) := by
  letI := (MeasureAlgebra.ofMeasure μ).toMetricSpace
  have hp : 0 < (p : ℝ) := NNReal.coe_pos.mpr
    (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0) ≤ p))
  refine Metric.isUniformEmbedding_iff'.2 ⟨?_, ?_⟩
  · intro ε hε
    refine ⟨ε ^ (p : ℝ), Real.rpow_pos_of_pos hε _, ?_⟩
    intro a b hab
    simpa only [dist_algebraIndicator,
      ← MeasureAlgebra.dist_eq_measure_symmDiff, one_div] using
      (Real.rpow_inv_lt_iff_of_pos (dist_nonneg : 0 ≤ dist a b) hε.le hp).2 hab
  · intro ε hε
    refine ⟨ε ^ (1 / (p : ℝ)), Real.rpow_pos_of_pos hε _, ?_⟩
    intro a b hab
    exact (Real.rpow_lt_rpow_iff (dist_nonneg : 0 ≤ dist a b) hε.le
      (one_div_pos.mpr hp)).mp
        (by simpa only [dist_algebraIndicator,
          ← MeasureAlgebra.dist_eq_measure_symmDiff] using hab)

end MeasureTheory.Lp

/-! ## Measure-algebra equivalences -/

open MeasureTheory MeasureTheory.Lp

namespace MeasureAlgebraEquiv

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {p : ℝ≥0} [Fact (1 ≤ p)]

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module Lp.simpleFunc.normedSpace

/-! ### Transport of indicators -/

/-- For a measurable set `s`, the linear operator sending `c ∈ ℝ` to the indicator in `Lᵖ(ν)`
with value `c` on the image under `e` of the `μ`-class of `s`. It is zero for nonmeasurable
sets. -/
private noncomputable def indicatorOperator
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (s : Set α) : ℝ →L[ℝ] Lp.simpleFunc ℝ (p : ENNReal) ν := by
  classical
  exact if hs : MeasurableSet s then
    (1 : ℝ →L[ℝ] ℝ).smulRight
      (indicatorSimpleFunc (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩)) 1)
    else 0

/-- On a `μ`-measurable set, the indicator operator evaluates to the abstract indicator in
`Lᵖ(ν)` of its image under the measure-algebra equivalence `e`. -/
private theorem indicatorOperator_apply
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    indicatorOperator (p := p) e s c =
      indicatorSimpleFunc (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩)) c := by
  simpa only [indicatorOperator, dif_pos hs, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self] using
    (indicatorSimpleFunc_smul (p := p)
      (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩)) c).symm

/-- The indicator operator into `Lᵖ(ν)` vanishes on every measurable `μ`-null set. -/
private theorem indicatorOperator_null
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s = 0) :
    indicatorOperator (p := p) e s = 0 := by
  refine ContinuousLinearMap.ext (fun c ↦ ?_)
  have hbot : MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩ = ⊥ :=
    ((MeasureAlgebra.ofMeasure μ).measure_eq_zero_iff _).mp
      ((MeasureAlgebra.ofMeasure_mk μ ⟨s, hs⟩).trans hμs)
  simp only [indicatorOperator_apply e hs, hbot,
    show e ⊥ = ⊥ from OrderIso.map_bot e.toRelIso, indicatorSimpleFunc_bot, zero_apply]

/-- The indicator operator into `Lᵖ(ν)` is additive on disjoint `μ`-measurable sets of finite
`μ`-measure. -/
private theorem indicatorOperator_finMeasAdditive
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    FinMeasAdditive μ (indicatorOperator (p := p) e) := by
  intro s t hs ht _ _ hst
  refine ContinuousLinearMap.ext (fun c ↦ ?_)
  have hi : e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) ⊓
      e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨t, ht⟩) = ⊥ :=
    ((MeasureAlgebra.InducedBooleanAlgebra.mk_disjoint μ ⟨s, hs⟩ ⟨t, ht⟩ hst).map_orderIso
      e.toRelIso).eq_bot
  simp only [add_apply, indicatorOperator_apply e (hs.union ht),
    indicatorOperator_apply e hs, indicatorOperator_apply e ht]
  have hu : e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s ∪ t, hs.union ht⟩) =
      e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) ⊔
        e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨t, ht⟩) :=
    (congrArg e (MeasureAlgebra.InducedBooleanAlgebra.mk_sup μ ⟨s, hs⟩ ⟨t, ht⟩)).trans
      (OrderIso.map_sup e.toRelIso _ _)
  simpa only [← hu, hi, indicatorSimpleFunc_bot, add_zero] using
    indicatorSimpleFunc_valuation (p := p)
      (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩))
      (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨t, ht⟩)) c

/-! ### Transport of simple functions -/

/-- The linear transport from simple functions in `Lᵖ(μ)` to simple functions in `Lᵖ(ν)`,
obtained by transporting their level sets through the measure-algebra equivalence `e`. -/
private noncomputable def simpleFuncMap
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Lp.simpleFunc ℝ (p : ENNReal) μ →ₗ[ℝ] Lp.simpleFunc ℝ (p : ENNReal) ν := by
  refine
    { toFun := fun f ↦ (Lp.simpleFunc.toSimpleFunc f).setToSimpleFunc (indicatorOperator (p := p) e)
      map_add' := ?_
      map_smul' := ?_ }
  · exact fun f g ↦
      (SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
        (fun _ hs hμs ↦ indicatorOperator_null (p := p) e hs hμs)
        (indicatorOperator_finMeasAdditive (p := p) e)
        (Lp.simpleFunc.toSimpleFunc (f + g)).integrable_of_isFiniteMeasure
        (Lp.simpleFunc.add_toSimpleFunc f g)).trans
      (SimpleFunc.setToSimpleFunc_add (indicatorOperator (p := p) e)
        (indicatorOperator_finMeasAdditive (p := p) e)
        (Lp.simpleFunc.toSimpleFunc f).integrable_of_isFiniteMeasure
        (Lp.simpleFunc.toSimpleFunc g).integrable_of_isFiniteMeasure)
  · exact fun c f ↦
      (SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
        (fun _ hs hμs ↦ indicatorOperator_null (p := p) e hs hμs)
        (indicatorOperator_finMeasAdditive (p := p) e)
        (Lp.simpleFunc.toSimpleFunc (c • f)).integrable_of_isFiniteMeasure
        (Lp.simpleFunc.smul_toSimpleFunc c f)).trans
      (SimpleFunc.setToSimpleFunc_smul_real (indicatorOperator (p := p) e)
        (indicatorOperator_finMeasAdditive (p := p) e) c
        (Lp.simpleFunc.toSimpleFunc f).integrable_of_isFiniteMeasure)

/-- Simple-function transport from `Lᵖ(μ)` to `Lᵖ(ν)` sends the indicator of `a` to the indicator
of `e a` with the same constant value. -/
private theorem simpleFuncMap_indicatorSimpleFunc
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    simpleFuncMap (p := p) e (indicatorSimpleFunc a c) =
      indicatorSimpleFunc (e a) c := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  exact
    (SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
      (fun _ hs hμs ↦ indicatorOperator_null (p := p) e hs hμs)
      (indicatorOperator_finMeasAdditive (p := p) e)
      (Lp.simpleFunc.toSimpleFunc (indicatorSimpleFunc (p := p)
        (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) c)).integrable_of_isFiniteMeasure
      (Lp.simpleFunc.toSimpleFunc_indicatorConst s.property (measure_ne_top μ s) c)).trans
    ((SimpleFunc.setToSimpleFunc_indicator (indicatorOperator (p := p) e)
      (indicatorOperator_null e MeasurableSet.empty (measure_empty)) s.property c).trans
      (indicatorOperator_apply e s.property c))

/-- Simple-function transport from `Lᵖ(μ)` to `Lᵖ(ν)` preserves nonnegativity. -/
private theorem simpleFuncMap_nonneg
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) (hf : 0 ≤ f) :
    0 ≤ simpleFuncMap e f := by
  obtain ⟨g, hg, hfg⟩ := Lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq hf
  rw [show simpleFuncMap e f = g.setToSimpleFunc (indicatorOperator (p := p) e) from
    SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
      (fun _ hs hμs ↦ indicatorOperator_null (p := p) e hs hμs)
      (indicatorOperator_finMeasAdditive (p := p) e)
      (Lp.simpleFunc.toSimpleFunc f).integrable_of_isFiniteMeasure
      ((Lp.simpleFunc.toSimpleFunc_eq_toFun f).trans hfg)]
  exact SimpleFunc.setToSimpleFunc_nonneg' (μ := μ) (indicatorOperator (p := p) e)
    (fun s hs _ c hc ↦ (indicatorOperator_apply (p := p) e hs c).symm ▸
      indicatorSimpleFunc_nonneg (p := p) (μ := ν)
        (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩)) c hc)
    g hg g.integrable_of_isFiniteMeasure

/-- Simple-function transport from `Lᵖ(μ)` to `Lᵖ(ν)` is monotone. -/
private theorem simpleFuncMap_mono
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Monotone (simpleFuncMap (p := p) e) := by
  exact fun f g h ↦ sub_nonneg.mp <| (map_sub (simpleFuncMap e) g f) ▸
    simpleFuncMap_nonneg e (g - f) (sub_nonneg.mpr h)

/-- On simple functions in `Lᵖ(μ)`, transport to `Lᵖ(ν)` followed by transport through the
inverse measure-algebra equivalence is the identity. -/
private theorem simpleFuncMap_symm_apply
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    simpleFuncMap e.symm (simpleFuncMap e f) = f := by
  refine Lp.simpleFunc.induction (p := (p : ENNReal))
    (ENNReal.coe_ne_zero.mpr ((lt_of_lt_of_le zero_lt_one Fact.out).ne'))
    ENNReal.coe_ne_top ?_ ?_ f
  · exact fun c s hs _ ↦
      (congrArg (simpleFuncMap (p := p) e.symm)
        (simpleFuncMap_indicatorSimpleFunc e
          (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) c)).trans
      ((simpleFuncMap_indicatorSimpleFunc e.symm _ c).trans
        (congrArg (fun a ↦ indicatorSimpleFunc (p := p) a c) (e.left_inv _)))
  · exact fun _ _ _ _ _ hf hg ↦ by
      simpa only [map_add] using congrArg₂ (· + ·) hf hg

/-- Simple-function transport between `Lᵖ(μ)` and `Lᵖ(ν)` preserves and reflects the order. -/
private theorem simpleFuncMap_le_iff
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f g : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    simpleFuncMap e f ≤ simpleFuncMap e g ↔ f ≤ g := by
  exact ⟨fun h ↦ by
    simpa only [simpleFuncMap_symm_apply] using (simpleFuncMap_mono e.symm h),
    fun h ↦ simpleFuncMap_mono e h⟩

/-! ### Simple-function equivalence and norm preservation -/

/-- The linear equivalence between the simple-function subspaces of `Lᵖ(μ)` and `Lᵖ(ν)`, with
inverse given by transport through the inverse measure-algebra equivalence. -/
private noncomputable def simpleFuncLinearEquiv
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Lp.simpleFunc ℝ (p : ENNReal) μ ≃ₗ[ℝ] Lp.simpleFunc ℝ (p : ENNReal) ν := by
  exact
    { simpleFuncMap e with
      invFun := simpleFuncMap e.symm
      left_inv := simpleFuncMap_symm_apply e
      right_inv := simpleFuncMap_symm_apply e.symm }

/-- The underlying map from the simple-function subspace of `Lᵖ(μ)` to that of `Lᵖ(ν)` is
`simpleFuncMap`. -/
private theorem simpleFuncLinearEquiv_apply
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    simpleFuncLinearEquiv e f = simpleFuncMap e f := by
  rfl

/-- Transport from `Lᵖ(μ)` to `Lᵖ(ν)` preserves the norm of a finite sum of constant indicators
whose supports in the measure algebra of `μ` are pairwise disjoint. -/
private theorem norm_sum_indicatorSimpleFunc
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {ι : Type*} (s : Finset ι) (a : ι → MeasureAlgebra.InducedBooleanAlgebra μ)
    (c : ι → ℝ) (ha : (s : Set ι).Pairwise fun i j ↦ Disjoint (a i) (a j)) :
    ‖∑ i ∈ s, (indicatorSimpleFunc (p := p) (e (a i)) (c i) : Lp ℝ (p : ENNReal) ν)‖ =
      ‖∑ i ∈ s, (indicatorSimpleFunc (p := p) (a i) (c i) : Lp ℝ (p : ENNReal) μ)‖ := by
  apply (Real.rpow_left_inj (z := (p : ℝ)) (norm_nonneg _) (norm_nonneg _)
    (NNReal.coe_ne_zero.mpr ((lt_of_lt_of_le zero_lt_one Fact.out).ne'))).mp
  rw [ALpSpace.norm_sum_rpow_eq_sum_norm_rpow_of_pairwise_isVLDisjoint (p := p) s
      (fun i ↦ (indicatorSimpleFunc (p := p) (e (a i)) (c i) : Lp ℝ (p : ENNReal) ν))
      (fun i hi j hj hij ↦ indicatorSimpleFunc_isVLDisjoint (p := p) _ _
        ((ha hi hj hij).map_orderIso e.toRelIso) (c i) (c j)),
    ALpSpace.norm_sum_rpow_eq_sum_norm_rpow_of_pairwise_isVLDisjoint (p := p) s
      (fun i ↦ (indicatorSimpleFunc (p := p) (a i) (c i) : Lp ℝ (p : ENNReal) μ))
      (fun i hi j hj hij ↦ indicatorSimpleFunc_isVLDisjoint (p := p) _ _
        (ha hi hj hij) (c i) (c j))]
  simp only [AddSubgroup.norm_coe, norm_indicatorSimpleFunc,
    show ∀ b, (MeasureAlgebra.ofMeasure ν) (e b) = (MeasureAlgebra.ofMeasure μ) b from
      fun b ↦ e.map_measure b]

/-- `simpleFuncMap` preserves the norm from the simple-function subspace of `Lᵖ(μ)`
to that of `Lᵖ(ν)`. -/
private theorem norm_simpleFuncMap
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    ‖simpleFuncMap e f‖ = ‖f‖ := by
  classical
  let g := Lp.simpleFunc.toSimpleFunc f
  change ‖(Lp.simpleFunc.coeToLp β ℝ ℝ)
      (g.setToSimpleFunc (indicatorOperator (p := p) e))‖ = ‖(f : Lp ℝ (p : ENNReal) μ)‖
  simp only [SimpleFunc.setToSimpleFunc, map_sum,
    indicatorOperator_apply e (g.measurableSet_fiber _)]
  have hd : (g.range : Set ℝ).Pairwise fun c d ↦
      Disjoint (MeasureAlgebra.InducedBooleanAlgebra.mk μ
        ⟨g ⁻¹' {c}, g.measurableSet_fiber c⟩)
        (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨g ⁻¹' {d}, g.measurableSet_fiber d⟩) :=
    fun c _ d _ hcd ↦ MeasureAlgebra.InducedBooleanAlgebra.mk_disjoint μ _ _
      ((Set.disjoint_singleton.mpr hcd).preimage g)
  refine (norm_sum_indicatorSimpleFunc (p := p) e g.range
    (fun c ↦ MeasureAlgebra.InducedBooleanAlgebra.mk μ
      ⟨g ⁻¹' {c}, g.measurableSet_fiber c⟩) id hd).trans ?_
  exact congrArg norm <| (simpleFunc_sum_indicators (μ := μ) (p := p) g).trans
    (congrArg (fun h : Lp.simpleFunc ℝ (p : ENNReal) μ ↦ (h : Lp ℝ (p : ENNReal) μ))
      (Lp.simpleFunc.toLp_toSimpleFunc f))

/-! ### Extension from simple functions to `Lᵖ` -/

/-- The linear isometric equivalence obtained by extending transport from the dense
simple-function subspaces to `Lᵖ(μ)` and `Lᵖ(ν)`. -/
private noncomputable def lpLinearIsometryEquiv
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Lp ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ] Lp ℝ (p : ENNReal) ν := by
  refine (simpleFuncLinearEquiv (p := p) e).extendOfIsometry
    (Lp.simpleFunc.coeToLp α ℝ ℝ (p := (p : ENNReal)) (μ := μ))
    (Lp.simpleFunc.coeToLp β ℝ ℝ (p := (p : ENNReal)) (μ := ν))
    (Lp.simpleFunc.denseRange ENNReal.coe_ne_top)
    (Lp.simpleFunc.denseRange ENNReal.coe_ne_top) (fun f ↦ ?_)
  change ‖(simpleFuncLinearEquiv e f : Lp ℝ (p : ENNReal) ν)‖ =
    ‖(f : Lp ℝ (p : ENNReal) μ)‖
  simpa only [simpleFuncLinearEquiv_apply, AddSubgroup.norm_coe] using norm_simpleFuncMap e f

/-- The extended linear isometry from `Lᵖ(μ)` to `Lᵖ(ν)` agrees with simple-function transport
on the dense simple-function subspace of `Lᵖ(μ)`. -/
private theorem lpLinearIsometryEquiv_apply_simpleFunc
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    lpLinearIsometryEquiv e (f : Lp ℝ (p : ENNReal) μ) =
      (simpleFuncMap e f : Lp ℝ (p : ENNReal) ν) := by
  unfold lpLinearIsometryEquiv
  erw [LinearEquiv.extendOfIsometry_eq]
  rfl

/-- The extension from `Lᵖ(ν)` to `Lᵖ(μ)` of transport through the inverse measure-algebra
equivalence is a left inverse of the extended transport from `Lᵖ(μ)` to `Lᵖ(ν)`. -/
private theorem lpLinearIsometryEquiv_symm_apply
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp ℝ (p : ENNReal) μ) :
    lpLinearIsometryEquiv e.symm (lpLinearIsometryEquiv e f) = f := by
  refine (Lp.simpleFunc.denseRange (E := ℝ) (p := (p : ENNReal)) (μ := μ)
    ENNReal.coe_ne_top).induction_on
    (p := fun g ↦ lpLinearIsometryEquiv e.symm (lpLinearIsometryEquiv e g) = g) f
    (isClosed_eq ((lpLinearIsometryEquiv e.symm).continuous.comp
      (lpLinearIsometryEquiv e).continuous) continuous_id) ?_
  exact fun g ↦ by
    simp only [lpLinearIsometryEquiv_apply_simpleFunc, simpleFuncMap_symm_apply]

/-- The extended linear isometry from `Lᵖ(μ)` to `Lᵖ(ν)` preserves nonnegativity, by density of
the nonnegative simple functions in `Lᵖ(μ)`. -/
private theorem lpLinearIsometryEquiv_nonneg
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp ℝ (p : ENNReal) μ) (hf : 0 ≤ f) :
    0 ≤ lpLinearIsometryEquiv e f := by
  refine (Lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg
    (p : ENNReal) μ ℝ ENNReal.coe_ne_top).induction_on
    (p := fun g ↦ 0 ≤ lpLinearIsometryEquiv e g.val) ⟨f, hf⟩
    (isClosed_le continuous_const
      ((lpLinearIsometryEquiv e).continuous.comp continuous_subtype_val)) ?_
  exact fun g ↦ (lpLinearIsometryEquiv_apply_simpleFunc e g.val).symm ▸
    (show (0 : Lp ℝ (p : ENNReal) ν) ≤ (simpleFuncMap e g.val : Lp ℝ (p : ENNReal) ν) from
      simpleFuncMap_nonneg e g.val g.property)

/-- The extended linear isometry from `Lᵖ(μ)` to `Lᵖ(ν)` is monotone. -/
private theorem lpLinearIsometryEquiv_mono
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Monotone (lpLinearIsometryEquiv (p := p) e) := by
  exact fun f g h ↦ sub_nonneg.mp <| (map_sub (lpLinearIsometryEquiv e) g f) ▸
    lpLinearIsometryEquiv_nonneg e (g - f) (sub_nonneg.mpr h)

/-- The extended linear isometry between `Lᵖ(μ)` and `Lᵖ(ν)` preserves and reflects the order. -/
private theorem lpLinearIsometryEquiv_le_iff
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f g : Lp ℝ (p : ENNReal) μ) :
    lpLinearIsometryEquiv e f ≤ lpLinearIsometryEquiv e g ↔ f ≤ g := by
  exact ⟨fun h ↦ by
    simpa only [lpLinearIsometryEquiv_symm_apply] using
      (lpLinearIsometryEquiv_mono e.symm h), fun h ↦ lpLinearIsometryEquiv_mono e h⟩

/-- The extended linear isometry from `Lᵖ(μ)` to `Lᵖ(ν)` preserves suprema. -/
private theorem lpLinearIsometryEquiv_map_sup
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f g : Lp ℝ (p : ENNReal) μ) :
    lpLinearIsometryEquiv e (f ⊔ g) =
      lpLinearIsometryEquiv e f ⊔ lpLinearIsometryEquiv e g := by
  exact OrderIso.map_sup
    { toEquiv := (lpLinearIsometryEquiv (p := p) e).toEquiv
      map_rel_iff' := fun {f g} ↦ lpLinearIsometryEquiv_le_iff e f g } f g

/-- The extended linear isometry from `Lᵖ(μ)` to `Lᵖ(ν)` preserves infima. -/
private theorem lpLinearIsometryEquiv_map_inf
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f g : Lp ℝ (p : ENNReal) μ) :
    lpLinearIsometryEquiv e (f ⊓ g) =
      lpLinearIsometryEquiv e f ⊓ lpLinearIsometryEquiv e g := by
  exact OrderIso.map_inf
    { toEquiv := (lpLinearIsometryEquiv (p := p) e).toEquiv
      map_rel_iff' := fun {f g} ↦ lpLinearIsometryEquiv_le_iff e f g } f g

/-! ### Induced lattice isometry -/

/-- A measure-algebra equivalence for finite measures `μ` and `ν` induces a lattice isometry
between `Lᵖ(μ)` and `Lᵖ(ν)` for `1 ≤ p < ∞`. -/
noncomputable def lpEquiv (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ)
    (MeasureAlgebra.ofMeasure ν)) :
    BanachLatEquiv (Lp ℝ (p : ENNReal) μ) (Lp ℝ (p : ENNReal) ν) := by
  exact
    { toLinearIsometryEquiv := lpLinearIsometryEquiv e
      map_sup' := lpLinearIsometryEquiv_map_sup e
      map_inf' := lpLinearIsometryEquiv_map_inf e }

/-- The induced lattice isometry from `Lᵖ(μ)` to `Lᵖ(ν)` sends a constant indicator to the
constant indicator of any `ν`-measurable set representing the image of its `μ`-measure-algebra
element. -/
theorem lpEquiv_indicatorConstLp
    (e : MeasureAlgebraEquiv (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : e (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) =
      MeasureAlgebra.InducedBooleanAlgebra.mk ν ⟨t, ht⟩) (c : ℝ) :
    e.lpEquiv (p := p)
        (indicatorConstLp (p : ENNReal) hs (measure_ne_top μ s) c) =
      indicatorConstLp (p : ENNReal) ht (measure_ne_top ν t) c := by
  change lpLinearIsometryEquiv e
    (indicatorConstLp (p : ENNReal) hs (measure_ne_top μ s) c) =
      indicatorConstLp (p : ENNReal) ht (measure_ne_top ν t) c
  have h := lpLinearIsometryEquiv_apply_simpleFunc e
    (indicatorSimpleFunc (p := p) (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) c)
  rw [simpleFuncMap_indicatorSimpleFunc, hst] at h
  simpa only [indicatorSimpleFunc_mk, Lp.simpleFunc.coe_indicatorConst] using h

end MeasureAlgebraEquiv
