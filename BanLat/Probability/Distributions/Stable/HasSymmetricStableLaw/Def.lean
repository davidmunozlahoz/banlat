/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Probability.Distributions.Stable.Def

/-!
# Symmetric `q`-stable random variables

This file defines the predicate that a real random variable has a **symmetric `q`-stable law.**
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A real random variable has a symmetric `q`-stable law with scale parameter `c` if it is almost
everywhere measurable and its distribution is symmetric `q`-stable with that scale parameter. -/
@[fun_prop]
structure HasSymmetricStableLaw {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (q : ℝ) (c : ℝ≥0) (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected isSymmetricStable_map : IsSymmetricStable (P.map X) q c

attribute [fun_prop] HasSymmetricStableLaw.aemeasurable

end ProbabilityTheory
