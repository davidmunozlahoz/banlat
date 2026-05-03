import BanLat.ALSpace
import BanLat.Examples.Lp.Basic
import BanLat.Examples.Lp.Sublattice

/-!
# Further structure on `Lp` spaces

For a measure space `(α, μ)` and `1 ≤ p`, the space `Lp ℝ p μ` of real-valued
`Lp` functions is a Banach lattice under the pointwise order and the `Lp`
norm; that basic structure is packaged in `BanLat.Examples.Lp.Basic`. This
file reexports the closed-sublattice representation from
`BanLat.Examples.Lp.Sublattice` and adds one further result: when `p = 1`,
the norm is additive on the positive cone, making `L₁(μ)` an AL-space.
-/

open MeasureTheory Filter

open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

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
