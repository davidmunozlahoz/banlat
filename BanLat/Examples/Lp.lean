import BanLat.ALSpace
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

/-! ### AL-space structure of L₁

The `L₁` norm is additive on the positive cone:
`‖f + g‖ = ‖f‖ + ‖g‖` for `f, g ≥ 0`. This makes `L₁(μ)` an AL-space.
-/

/-- The `L₁` norm is additive on the positive cone: `‖f + g‖₁ = ‖f‖₁ + ‖g‖₁`
whenever `0 ≤ f` and `0 ≤ g`. -/
theorem Lp.norm_add_of_nonneg {f g : Lp ℝ 1 μ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    ‖f + g‖ = ‖f‖ + ‖g‖ := by
  have hfae : 0 ≤ᵐ[μ] ⇑f := (Lp.coeFn_nonneg f).mpr hf
  have hgae : 0 ≤ᵐ[μ] ⇑g := (Lp.coeFn_nonneg g).mpr hg
  have hf_int : ∫⁻ x, ‖f x‖ₑ ∂μ = ENNReal.ofReal ‖f‖ := by
    rw [Lp.norm_def, ← eLpNorm_one_eq_lintegral_enorm,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  have hg_int : ∫⁻ x, ‖g x‖ₑ ∂μ = ENNReal.ofReal ‖g‖ := by
    rw [Lp.norm_def, ← eLpNorm_one_eq_lintegral_enorm,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)]
  have hfg_int : ∫⁻ x, ‖(f + g) x‖ₑ ∂μ = ENNReal.ofReal ‖f + g‖ := by
    rw [Lp.norm_def, ← eLpNorm_one_eq_lintegral_enorm,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (f + g))]
  have hfm : AEMeasurable (fun x => ‖f x‖ₑ) μ := (Lp.aestronglyMeasurable f).enorm
  have hsum : ∫⁻ x, ‖(f + g) x‖ₑ ∂μ
      = (∫⁻ x, ‖f x‖ₑ ∂μ) + ∫⁻ x, ‖g x‖ₑ ∂μ := by
    rw [← lintegral_add_left' hfm]
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g, hfae, hgae] with x hx hxf hxg
    rw [hx, Pi.add_apply, Real.enorm_of_nonneg hxf, Real.enorm_of_nonneg hxg,
      Real.enorm_of_nonneg (add_nonneg hxf hxg), ENNReal.ofReal_add hxf hxg]
  rw [hfg_int, hf_int, hg_int, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] at hsum
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsum

/-- `L₁(μ)` is an AL-space: the norm satisfies `‖f + g‖ = ‖f‖ + ‖g‖`
for all non-negative `f` and `g`. -/
noncomputable instance instALSpaceLp1 : ALSpace (Lp ℝ 1 μ) where
  norm_add_eq_of_nonneg hf hg := Lp.norm_add_of_nonneg hf hg

