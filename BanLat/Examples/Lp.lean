import BanLat.AMSpace
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Lp spaces as Banach lattices

For a measure space `(α, μ)` and `1 ≤ p`, the space `Lp ℝ p μ` of real-valued
Lp functions is a Banach lattice under the pointwise order and the Lp norm.
When `p = 1` the norm is additive on the positive cone, making `L₁(μ)` an
AL-space. For `1 ≤ p < ∞` the space has no strong units.
-/

open MeasureTheory

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
instance instVectorLatticeLp : VectorLattice (Lp ℝ p μ) :=
  sorry

/-! ### Normed vector lattice -/

/-- `Lp ℝ p μ` is a normed vector lattice. -/
instance instNormedVectorLatticeLp :
    NormedVectorLattice (Lp ℝ p μ) :=
  sorry

/-! ### Banach lattice -/

/-- `Lp ℝ p μ` is a Banach lattice: a complete normed vector lattice. -/
instance instBanachLatticeLp : BanachLattice (Lp ℝ p μ) :=
  sorry

/-! ### AL-space structure of L₁

The `L₁` norm is additive on the positive cone:
`‖f + g‖ = ‖f‖ + ‖g‖` for `f, g ≥ 0`. This makes `L₁(μ)` an AL-space.
-/

/-- The `L₁` norm is additive on the positive cone: `‖f + g‖₁ = ‖f‖₁ + ‖g‖₁`
whenever `0 ≤ f` and `0 ≤ g`. -/
theorem Lp.norm_add_of_nonneg {f g : Lp ℝ 1 μ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    ‖f + g‖ = ‖f‖ + ‖g‖ :=
  sorry

/-- `L₁(μ)` is an AL-space: the norm satisfies `‖f + g‖ = ‖f‖ + ‖g‖`
for all non-negative `f` and `g`. -/
instance instALSpaceLp1 : ALSpace (Lp ℝ 1 μ) :=
  sorry

/-! ### No strong units

For `1 ≤ p < ∞` the positive cone of `Lp ℝ p μ` has empty interior, so
there are no strong units. Intuitively, any positive function can be perturbed
on a set of arbitrarily small measure to lose positivity.
-/

/-- `Lp ℝ p μ` has no strong units when `1 ≤ p < ∞`. That is, for every
`0 < e` in `Lp ℝ p μ`, there exists `x` with `|x| ≰ r • e` for all
`r > 0`. -/
theorem Lp.no_strongUnit (hp : p ≠ ⊤)
    (e : Lp ℝ p μ) (he : (0 : Lp ℝ p μ) < e) :
    ¬ IsStrongUnit (Lp ℝ p μ) e :=
  sorry
