import BanLat.Normed
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# `Lp` spaces as Banach lattices

For a measure space `(α, μ)` and `1 ≤ p`, the space `Lp ℝ p μ` of real-valued
`Lp` functions is a Banach lattice under the pointwise order and the `Lp` norm.
-/

open MeasureTheory Filter

open scoped Topology

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

/-- `Lp ℝ p μ` is a vector lattice: a real module whose positive cone is
closed under scalar multiplication by non-negative reals. -/
noncomputable instance instVectorLatticeLp : VectorLattice (Lp ℝ p μ) where
  smul_le_smul_of_nonneg_left a ha x y hxy := by
    rw [← Lp.coeFn_le] at hxy ⊢
    filter_upwards [Lp.coeFn_smul a x, Lp.coeFn_smul a y, hxy] with i h1 h2 h3
    rw [h1, h2]
    exact smul_le_smul_of_nonneg_left h3 ha

/-! ### Normed vector lattice -/

/-- `Lp ℝ p μ` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeLp :
    NormedVectorLattice (Lp ℝ p μ) where

/-! ### Banach lattice -/

/-- `Lp ℝ p μ` is a Banach lattice: a complete normed vector lattice. -/
noncomputable instance instBanachLatticeLp : BanachLattice (Lp ℝ p μ) where
