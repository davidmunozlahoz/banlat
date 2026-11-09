/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Operators.Extension.HahnBanach
import BanLat.Majorizing
import BanLat.Operators.Positive

/-!
# Kantorovich's extension theorem

Kantorovich's extension theorem states that a positive linear map from a majorizing vector
sublattice of a real vector lattice into a Dedekind complete real vector lattice admits a
positive linear extension to the whole space. The sublinear bound is the envelope
`p(x) = inf {T y | y ∈ Y, x ≤ y}`. Majorization makes this set nonempty, and positivity
makes it bounded below, so Dedekind completeness supplies its infimum.
-/

open Set

namespace VectorSublattice

variable {X Z : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] [AddCommGroup Z] [ConditionallyCompleteLattice Z]
  [IsOrderedAddMonoid Z] [VectorLattice Z]

/-- If `Y` is majorizing in `X`, then for every `x ∈ X`, the set of values `T y`
over all `y ∈ Y` satisfying `x ≤ y` is nonempty. -/
private lemma majorant_values_nonempty (Y : VectorSublattice X) (hY : Y.IsMajorizing)
    (T : Y →ₗ[ℝ] Z) (x : X) : (T '' {y : Y | x ≤ (y : X)}).Nonempty := by
  obtain ⟨y, hy, hxy⟩ := hY x
  exact ⟨T ⟨y, hy⟩, ⟨⟨y, hy⟩, hxy, rfl⟩⟩

/-- If `Y` is majorizing in `X` and `T` is positive, then for every `x ∈ X`,
the set of values `T y` over all `y ∈ Y` satisfying `x ≤ y` is bounded below in `Z`. -/
private lemma majorant_values_bddBelow (Y : VectorSublattice X) (hY : Y.IsMajorizing)
    (T : Y →ₗ[ℝ] Z) (hT : Positive T) (x : X) :
    BddBelow (T '' {y : Y | x ≤ (y : X)}) := by
  obtain ⟨v, hv, hxv⟩ := hY (-x)
  refine ⟨T ⟨-v, Y.neg_mem hv⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (Positive.monotone_iff.mpr hT) ((neg_le.mp hxv).trans hy)

/-- If `Y` is majorizing in `X` and `T` is positive, then for every `y ∈ Y`,
the infimum in `Z` of the values `T w` over all `w ∈ Y` satisfying `y ≤ w`
is exactly `T y`. -/
private lemma majorant_inf_eq (Y : VectorSublattice X) (hY : Y.IsMajorizing)
    (T : Y →ₗ[ℝ] Z) (hT : Positive T) (y : Y) :
    sInf (T '' {w : Y | (y : X) ≤ (w : X)}) = T y := by
  apply le_antisymm
  · exact csInf_le (majorant_values_bddBelow Y hY T hT y) ⟨y, le_rfl, rfl⟩
  · apply le_csInf (majorant_values_nonempty Y hY T y)
    rintro _ ⟨w, hw, rfl⟩
    exact (Positive.monotone_iff.mpr hT) hw

/-- If `Y` is majorizing in `X` and `T` is positive, the function assigning to each
`x ∈ X` the infimum in `Z` of `T w` over all `w ∈ Y` with `x ≤ w` is subadditive. -/
private lemma majorant_inf_add_le (Y : VectorSublattice X) (hY : Y.IsMajorizing)
    (T : Y →ₗ[ℝ] Z) (hT : Positive T) (x y : X) :
    sInf (T '' {w : Y | x + y ≤ (w : X)}) ≤
      sInf (T '' {w : Y | x ≤ (w : X)}) + sInf (T '' {w : Y | y ≤ (w : X)}) := by
  -- Use the greatest-lower-bound property twice; the infima need not be attained.
  apply sub_le_iff_le_add.mp
  apply le_csInf (majorant_values_nonempty Y hY T x)
  rintro _ ⟨u, hu, rfl⟩
  rw [sub_le_iff_le_add, add_comm (T u), ← sub_le_iff_le_add]
  apply le_csInf (majorant_values_nonempty Y hY T y)
  rintro _ ⟨v, hv, rfl⟩
  rw [sub_le_iff_le_add, add_comm (T v), ← T.map_add]
  exact csInf_le (majorant_values_bddBelow Y hY T hT (x + y))
    ⟨u + v, add_le_add hu hv, rfl⟩

/-- For any `x ∈ X` and positive real `r`, the set of values `T w` over
`w ∈ Y` satisfying `r • x ≤ w` equals the set of values `r • T v` over
`v ∈ Y` satisfying `x ≤ v`. -/
private lemma majorant_values_smul (Y : VectorSublattice X) (T : Y →ₗ[ℝ] Z)
    (x : X) {r : ℝ} (hr : 0 < r) :
    T '' {w : Y | r • x ≤ (w : X)} =
      (fun z : Z ↦ r • z) '' (T '' {w : Y | x ≤ (w : X)}) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hx : x ≤ ((r⁻¹ • w : Y) : X) := by
      simpa [smul_smul, hr.ne'] using
        smul_le_smul_of_nonneg_left hw (inv_pos.mpr hr).le
    exact ⟨T (r⁻¹ • w), ⟨r⁻¹ • w, hx, rfl⟩,
      by simp [map_smul, smul_smul, hr.ne']⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨r • w, smul_le_smul_of_nonneg_left hw hr.le, T.map_smul r w⟩

/-- If `Y` is majorizing in `X` and `T` is positive, then for every positive real `r`,
the infimum in `Z` of `T w` over `w ∈ Y` satisfying `r • x ≤ w` equals
`r` times the infimum of `T w` over `w ∈ Y` satisfying `x ≤ w`. -/
private lemma majorant_inf_smul (Y : VectorSublattice X) (hY : Y.IsMajorizing)
    (T : Y →ₗ[ℝ] Z) (hT : Positive T) (r : ℝ) (hr : 0 < r) (x : X) :
    sInf (T '' {w : Y | r • x ≤ (w : X)}) =
      r • sInf (T '' {w : Y | x ≤ (w : X)}) := by
  rw [majorant_values_smul Y T x hr]
  exact ((OrderIso.smulRight hr).map_csInf'
    (majorant_values_nonempty Y hY T x) (majorant_values_bddBelow Y hY T hT x)).symm

/-- **Kantorovich's extension theorem**: a positive linear map from a majorizing vector
sublattice of a real vector lattice into a Dedekind complete real vector lattice admits a
positive linear extension to the whole space. -/
theorem exists_positive_extension (Y : VectorSublattice X) (hY : Y.IsMajorizing)
    (T : Y →ₗ[ℝ] Z) (hT : Positive T) :
    ∃ S : X →ₗ[ℝ] Z, Positive S ∧ ∀ y : Y, S y = T y := by
  let p : X → Z := fun x ↦ sInf (T '' {y : Y | x ≤ (y : X)})
  obtain ⟨S, hext, hS⟩ := LinearMap.exists_extension_of_le_sublinear Y.toSubmodule T p
    (majorant_inf_smul Y hY T hT) (majorant_inf_add_le Y hY T hT)
    (fun y ↦ (majorant_inf_eq Y hY T hT y).ge)
  refine ⟨S, ?_, hext⟩
  intro x hx
  have hp : p (-x) ≤ 0 := calc
    p (-x) ≤ T 0 := csInf_le (majorant_values_bddBelow Y hY T hT (-x))
      ⟨0, neg_nonpos.mpr hx, rfl⟩
    _ = 0 := T.map_zero
  have h := (hS (-x)).trans hp
  simpa only [map_neg, neg_nonpos] using h

end VectorSublattice
