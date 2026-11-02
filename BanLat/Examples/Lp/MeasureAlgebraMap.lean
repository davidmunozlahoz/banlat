/-
Authors: Pedro Tradacete
-/

import BanLat.Examples.Lp.Indicators

/-!
# Measure-algebra maps induced by lattice homomorphisms

A lattice homomorphism between finite-measure `L¹` spaces that preserves the constant
function one induces a Boolean homomorphism on their measure algebras. If the original
map is isometric, the Boolean homomorphism also preserves measure.
-/

noncomputable section

open MeasureTheory

universe u v

namespace MeasureTheory.Lp

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (T : VecLatHom (Lp ℝ 1 μ) (Lp ℝ 1 ν)) (hT : T (Lp.const 1 μ (1 : ℝ)) = Lp.const 1 ν (1 : ℝ))

include hT

private lemma map_indicator_component (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    T (algebraIndicator (p := 1) a) ⊓
      (Lp.const 1 ν (1 : ℝ) - T (algebraIndicator (p := 1) a)) = 0 := by
  rw [← hT, ← map_sub, ← map_inf, algebraIndicator_inf_sub, map_zero]

private def indicatorMap (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    MeasureAlgebra.InducedBooleanAlgebra ν :=
  (exists_algebraIndicator_eq _ (map_indicator_component T hT a)).choose

private lemma algebraIndicator_indicatorMap (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    algebraIndicator (p := 1) (indicatorMap T hT a) = T (algebraIndicator (p := 1) a) :=
  (exists_algebraIndicator_eq _ (map_indicator_component T hT a)).choose_spec

/-- A lattice homomorphism preserving the constant function one induces a Boolean
homomorphism by its action on indicators. -/
def toMeasureAlgebraHom :
    BoundedLatticeHom (MeasureAlgebra.InducedBooleanAlgebra μ)
      (MeasureAlgebra.InducedBooleanAlgebra ν) := by
  refine
    { toFun := indicatorMap T hT
      map_sup' := fun a b ↦ ?_
      map_inf' := fun a b ↦ ?_
      map_top' := ?_
      map_bot' := ?_ }
  all_goals apply algebraIndicator_injective
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_sup, map_sup]
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_inf, map_inf]
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_top, hT]
  · simp only [algebraIndicator_indicatorMap, algebraIndicator_bot, map_zero]

/-- The induced Boolean homomorphism describes the original map on indicators. -/
@[simp]
theorem map_algebraIndicator (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    T (algebraIndicator (p := 1) a) =
      algebraIndicator (p := 1) (toMeasureAlgebraHom T hT a) :=
  (algebraIndicator_indicatorMap T hT a).symm

/-- An isometric lattice homomorphism preserving one induces a measure-preserving
Boolean homomorphism. -/
theorem measure_toMeasureAlgebraHom (hiso : Isometry T)
    (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    (MeasureAlgebra.ofMeasure ν) (toMeasureAlgebraHom T hT a) =
      (MeasureAlgebra.ofMeasure μ) a := by
  apply (ENNReal.toReal_eq_toReal_iff'
    ((MeasureAlgebra.ofMeasure ν).measure_ne_top _)
    ((MeasureAlgebra.ofMeasure μ).measure_ne_top _)).mp
  rw [← norm_algebraIndicator, ← map_algebraIndicator,
    hiso.norm_map_of_map_zero (map_zero T), norm_algebraIndicator]

/-- The induced Boolean homomorphism transports constant indicators with any real value. -/
theorem map_indicatorSimpleFunc (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ) :
    T (indicatorSimpleFunc (p := 1) a c) =
      (indicatorSimpleFunc (p := 1) (toMeasureAlgebraHom T hT a) c : Lp ℝ 1 ν) := by
  rw [indicatorSimpleFunc_smul a c, indicatorSimpleFunc_smul (toMeasureAlgebraHom T hT a) c]
  exact (map_smul T c (algebraIndicator (p := 1) a)).trans
    (congrArg (c • ·) (map_algebraIndicator T hT a))

end MeasureTheory.Lp
