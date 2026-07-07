import BanLat.ALSpace.Basic
import BanLat.Normed
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-! ### AL-space -/

/-- The `L¹` norm is additive on non-negative elements, so `L¹(μ)` is an AL-space; in
particular the norm of `L¹(μ)` is order continuous. -/
noncomputable instance instALSpaceL1 : ALSpace (Lp ℝ 1 μ) where
  norm_add_eq_of_inf_eq_zero {f g} hfg := by
    have hf : (0 : Lp ℝ 1 μ) ≤ f := by rw [← hfg]; exact _root_.inf_le_left
    have hg : (0 : Lp ℝ 1 μ) ≤ g := by rw [← hfg]; exact _root_.inf_le_right
    have hf_ae : (0 : α → ℝ) ≤ᵐ[μ] f := (Lp.coeFn_nonneg f).mpr hf
    have hg_ae : (0 : α → ℝ) ≤ᵐ[μ] g := (Lp.coeFn_nonneg g).mpr hg
    have h1 : (fun ω => ‖(f + g : Lp ℝ 1 μ) ω‖) =ᵐ[μ] fun ω => ‖f ω‖ + ‖g ω‖ := by
      filter_upwards [Lp.coeFn_add f g, hf_ae, hg_ae] with ω hω hfω hgω
      rw [hω, Pi.add_apply, Real.norm_of_nonneg hfω, Real.norm_of_nonneg hgω,
        Real.norm_of_nonneg (add_nonneg hfω hgω)]
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
      integral_congr_ae h1]
    exact integral_add (L1.integrable_coeFn f).norm (L1.integrable_coeFn g).norm
