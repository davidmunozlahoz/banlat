import BanLat.ALSpace.Basic
import BanLat.ALpSpace.Basic
import BanLat.Normed
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lp` spaces as Banach lattices

For a measure space `(α, μ)` and `1 ≤ p ≤ ∞`, the space `Lp ℝ p μ` of real-valued
`Lp` functions is a Banach lattice under the pointwise order and the `Lp` norm.
Moreover:
  · `L₁` is an AL-space.
  · `Lₚ` is an ALₚ-space for `1 ≤ p < ∞`.
-/

open MeasureTheory Filter

open scoped NNReal Topology

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

/-- `Lp ℝ p μ` is a vector lattice. -/
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

/-- `Lp ℝ p μ` is a Banach lattice. -/
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

/-! ### p-th power of the `L^p` norm formula -/

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E]

/-- The `p`-th power of the `L^p`-norm as an integral. -/
lemma norm_rpow_eq_integral_norm_rpow
    {p : ℝ≥0} (hp : p ≠ 0) (f : Lp E (p : ENNReal) μ) :
    ‖f‖ ^ (p : ℝ) = ∫ x, ‖f x‖ ^ (p : ℝ) ∂μ := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
    (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top]
  rw [ENNReal.toReal_ofReal]
  · exact Real.rpow_inv_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (NNReal.coe_ne_zero.mpr hp)
  · exact Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

end MeasureTheory.Lp

/-! ### Lₚ(μ) spaces are ALₚ-spaces -/
section ALpSpace

variable {p : ℝ≥0} [Fact (1 ≤ p)]

private instance instFactOneLEENNRealALp :
    Fact (1 ≤ (p : ENNReal)) :=
  ⟨by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)⟩

/-- If `f ⟂ g`, `|f+g|ᵖ = |f|ᵖ + |g|ᵖ` a.e. -/
private lemma ae_norm_add_rpow_eq_of_isVLDisjoint
    {f g : Lp ℝ (p : ENNReal) μ} (hfg : IsVLDisjoint f g) :
    (fun x ↦ ‖(f + g) x‖ ^ (p : ℝ)) =ᵐ[μ]
      fun x ↦ ‖f x‖ ^ (p : ℝ) + ‖g x‖ ^ (p : ℝ) := by
  have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
  have heq : |f| ⊓ |g| = 0 := hfg
  have hzero : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0 := by
    filter_upwards [Lp.coeFn_inf |f| |g|, Lp.coeFn_abs f,
      Lp.coeFn_abs g, Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hinf hf hg hzero
    rw [heq, hzero] at hinf
    change (0 : ℝ) = min ((|f| : Lp ℝ (p : ENNReal) μ) x)
      ((|g| : Lp ℝ (p : ENNReal) μ) x) at hinf
    rw [hf, hg] at hinf
    rcases le_total |f x| |g x| with hle | hle
    · left
      exact abs_eq_zero.mp ((min_eq_left hle ▸ hinf).symm)
    · right
      exact abs_eq_zero.mp ((min_eq_right hle ▸ hinf).symm)
  filter_upwards [Lp.coeFn_add f g, hzero] with x hadd hx
  rw [hadd]
  rcases hx with hf | hg
  · simp [hf, Real.zero_rpow (NNReal.coe_ne_zero.mpr hp)]
  · simp [hg, Real.zero_rpow (NNReal.coe_ne_zero.mpr hp)]

/-- For every `1 ≤ p < ∞`, the real space `L^p(μ)` is an ALₚ-space -/
noncomputable instance instALpSpaceLp :
    ALpSpace p (Lp ℝ (p : ENNReal) μ) where
  norm_add_rpow_eq_of_isVLDisjoint {f g} hfg := by
    have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
    rw [Lp.norm_rpow_eq_integral_norm_rpow hp, Lp.norm_rpow_eq_integral_norm_rpow hp,
      Lp.norm_rpow_eq_integral_norm_rpow hp,
      integral_congr_ae (ae_norm_add_rpow_eq_of_isVLDisjoint hfg)]
    exact integral_add ((Lp.memLp f).integrable_norm_rpow
      (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)
      ((Lp.memLp g).integrable_norm_rpow
        (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)

end ALpSpace
