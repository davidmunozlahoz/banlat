/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Dual

/-!
# Positive extensions of continuous functionals

The positive Hahn–Banach theorem extends a positive continuous real functional on a vector
sublattice of a normed vector lattice to a positive continuous functional with the same norm.
The sublattice has its inherited norm; no completeness or closedness is required.
-/

namespace StrongDual

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [NormedVectorLattice X]

private lemma norm_posPart_add_le (x y : X) : ‖(x + y)⁺‖ ≤ ‖x⁺‖ + ‖y⁺‖ := by
  have h : |(x + y)⁺| ≤ |x⁺ + y⁺| := by
    rw [abs_of_nonneg (posPart_nonneg _),
      abs_of_nonneg (add_nonneg (posPart_nonneg _) (posPart_nonneg _))]
    exact posPart_add_le x y
  exact (norm_le_norm_of_abs_le_abs h).trans (norm_add_le _ _)

private lemma exists_dominated_extension (Y : VectorSublattice X)
    (f : StrongDual ℝ Y) (hf : 0 ≤ f) :
    ∃ g : X →ₗ[ℝ] ℝ, (∀ y : Y, g y = f y) ∧
      ∀ x, g x ≤ ‖f‖ * ‖x⁺‖ := by
  let p : X → ℝ := fun x ↦ ‖f‖ * ‖x⁺‖
  apply exists_extension_of_le_sublinear (⟨Y.toSubmodule, f.toLinearMap⟩ : X →ₗ.[ℝ] ℝ) p
  · intro c hc x
    simp [p, posPart_smul_nonneg hc.le, norm_smul, Real.norm_of_nonneg hc.le,
      mul_left_comm]
  · intro x y
    exact (mul_le_mul_of_nonneg_left (norm_posPart_add_le x y) (norm_nonneg f)).trans_eq
      (mul_add _ _ _)
  · intro y
    let z : Y := y
    change f z ≤ p z
    calc f z ≤ f z⁺ := apply_le_apply_of_nonneg hf (le_posPart z)
      _ ≤ ‖f z⁺‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖z⁺‖ := f.le_opNorm _
      _ = p y := rfl

private lemma positive_of_le_norm_posPart {g : X →ₗ[ℝ] ℝ} {C : ℝ}
    (hg : ∀ x, g x ≤ C * ‖x⁺‖) : Positive g := by
  intro x hx
  have h := hg (-x)
  simpa [map_neg, posPart_eq_zero.mpr (neg_nonpos.mpr hx)] using h

private lemma norm_le_of_le_norm_posPart {g : X →ₗ[ℝ] ℝ} {C : ℝ}
    (hg : ∀ x, g x ≤ C * ‖x⁺‖) (x : X) : ‖g x‖ ≤ C * ‖x‖ := by
  calc ‖g x‖ = |g x| := Real.norm_eq_abs _
    _ ≤ g |x| := Positive.abs_le_map_abs (positive_of_le_norm_posPart hg) x
    _ ≤ C * ‖(|x|)⁺‖ := hg |x|
    _ = C * ‖x‖ := by rw [posPart_of_nonneg (abs_nonneg _), norm_abs_eq_norm]

/-- The positive Hahn–Banach theorem: a positive continuous functional on a vector sublattice
extends to a positive continuous functional on the ambient normed vector lattice,
preserving its norm. -/
theorem exists_positive_extension_norm_eq (Y : VectorSublattice X)
    (f : StrongDual ℝ Y) (hf : 0 ≤ f) :
    ∃ g : StrongDual ℝ X, 0 ≤ g ∧ (∀ y : Y, g y = f y) ∧ ‖g‖ = ‖f‖ := by
  obtain ⟨g, hext, hg⟩ := exists_dominated_extension Y f hf
  have hbound := norm_le_of_le_norm_posPart hg
  let G : StrongDual ℝ X := g.mkContinuous ‖f‖ hbound
  refine ⟨G, nonneg_iff.mpr (positive_of_le_norm_posPart hg), hext, le_antisymm ?_ ?_⟩
  · exact g.mkContinuous_norm_le (norm_nonneg f) hbound
  · exact f.opNorm_le_bound (norm_nonneg G) fun y ↦ by
      change ‖f y‖ ≤ ‖G‖ * ‖(y : X)‖
      rw [← hext y]
      exact G.le_opNorm (y : X)

end StrongDual
