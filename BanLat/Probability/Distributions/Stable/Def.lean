import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Symmetric `q`-stable measuress

This file defines centered symmetric `q`-stable probability measures on `ℝ` through their
characteristic functions.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Let `c ≥ 0, 0 < q ≤ 2`. A probability measure on `ℝ` is symmetric `q`-stable with scale
parameter `c` if its characteristic function is `t ↦ exp (-c * |t| ^ q)`. -/
structure IsSymmetricStable (μ : Measure ℝ) (q : ℝ) (c : ℝ≥0) : Prop where
  protected index_pos : 0 < q
  protected index_le_two : q ≤ 2
  protected isProbabilityMeasure : IsProbabilityMeasure μ
  protected charFun_eq (t : ℝ) :
    charFun μ t = Complex.exp ((-(c : ℝ) * |t| ^ q : ℝ) : ℂ)

end ProbabilityTheory
