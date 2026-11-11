/-
Authors: Pedro Tradacete
-/

import BanLat.Examples.Lp.MeasureAlgebra.Indicators

/-!
# Measure-algebra maps induced by lattice homomorphisms

For `1 ≤ p < ∞`, a lattice homomorphism between finite-measure `Lᵖ` spaces that preserves
the constant one function induces a Boolean homomorphism on their measure algebras.
If the original map is isometric, the Boolean homomorphism also preserves measure,
since the measure of a Boolean element is the `p`-th power of its indicator's norm.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

universe u v

namespace MeasureTheory.Lp

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

variable {p : ℝ≥0} (T : VecLatHom (Lp ℝ (p : ℝ≥0∞) μ) (Lp ℝ (p : ℝ≥0∞) ν))
  (hT : T (Lp.const p μ (1 : ℝ)) = Lp.const p ν (1 : ℝ))

include hT

private lemma map_indicator_component (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    T (algebraIndicator (p := p) a) ⊓
      (Lp.const p ν (1 : ℝ) - T (algebraIndicator (p := p) a)) = 0 := by
  simpa only [map_inf, map_sub, hT, map_zero] using
    congrArg T (algebraIndicator_inf_sub (p := p) a)

private def indicatorMap (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    MeasureAlgebra.InducedBooleanAlgebra ν :=
  (exists_algebraIndicator_eq _ (map_indicator_component T hT a)).choose

private lemma algebraIndicator_indicatorMap (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    algebraIndicator (p := p) (indicatorMap T hT a) = T (algebraIndicator (p := p) a) :=
  (exists_algebraIndicator_eq _ (map_indicator_component T hT a)).choose_spec

variable [Fact (1 ≤ p)]

/-- For `1 ≤ p < ∞`, a lattice homomorphism between finite-measure `Lᵖ` spaces preserving
the constant one function induces a Boolean homomorphism by its action on indicators. -/
def toMeasureAlgebraHom :
    BoundedLatticeHom (MeasureAlgebra.InducedBooleanAlgebra μ)
      (MeasureAlgebra.InducedBooleanAlgebra ν) := by
  refine
    { toFun := indicatorMap T hT
      map_sup' := fun a b ↦ ?_
      map_inf' := fun a b ↦ ?_
      map_top' := ?_
      map_bot' := ?_ }
  all_goals apply algebraIndicator_injective (p := p)
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_sup, map_sup]
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_inf, map_inf]
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_top, hT]
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_bot, map_zero]

/-- The induced Boolean homomorphism describes the original map on indicators. -/
@[simp]
theorem map_algebraIndicator (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    T (algebraIndicator (p := p) a) =
      algebraIndicator (p := p) (toMeasureAlgebraHom T hT a) :=
  (algebraIndicator_indicatorMap T hT a).symm

/-- For `1 ≤ p < ∞`, an isometric lattice homomorphism between finite-measure `Lᵖ` spaces
preserving the constant one function induces a measure-preserving Boolean homomorphism. -/
theorem measure_toMeasureAlgebraHom (hiso : Isometry T)
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    (MeasureAlgebra.ofMeasure ν) (toMeasureAlgebraHom T hT a) =
      (MeasureAlgebra.ofMeasure μ) a := by
  apply (ENNReal.toReal_eq_toReal_iff'
    ((MeasureAlgebra.ofMeasure ν).measure_ne_top _)
    ((MeasureAlgebra.ofMeasure μ).measure_ne_top _)).mp
  apply (Real.rpow_left_inj (z := 1 / (p : ℝ)) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (one_div_ne_zero (NNReal.coe_ne_zero.mpr ((lt_of_lt_of_le zero_lt_one Fact.out).ne')))).mp
  simpa only [norm_algebraIndicator (p := p)] using
    (congrArg norm (map_algebraIndicator T hT a)).symm.trans
      (hiso.norm_map_of_map_zero (map_zero T) (algebraIndicator (p := p) a))

/-- The induced Boolean homomorphism transports constant indicators with any real value. -/
theorem map_indicatorSimpleFunc (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    T (indicatorSimpleFunc (p := p) a c) =
      (indicatorSimpleFunc (p := p) (toMeasureAlgebraHom T hT a) c : Lp ℝ (p : ℝ≥0∞) ν) := by
  rw [indicatorSimpleFunc_smul a c, indicatorSimpleFunc_smul (toMeasureAlgebraHom T hT a) c]
  exact (map_smul T c (algebraIndicator (p := p) a)).trans
    (congrArg (c • ·) (map_algebraIndicator T hT a))

end MeasureTheory.Lp
