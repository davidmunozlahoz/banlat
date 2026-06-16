import BanLat.LocallySolid.Basic
import BanLat.RieszDec
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Locally convex-solid vector lattices

This file defines locally convex-solid vector lattices as locally solid vector lattices whose
topology is locally convex.
-/

open scoped Topology

/-- A locally convex-solid vector lattice is a locally solid vector lattice whose topology is
locally convex. -/
class IsLocallyConvexSolidVectorLattice (E : Type*) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [VectorLattice E] [TopologicalSpace E] : Prop
    extends IsLocallySolidVectorLattice E, LocallyConvexSpace ℝ E

namespace IsLocallyConvexSolidVectorLattice

variable {E : Type*} [AddCommGroup E] [Lattice E]

private def solidInterior (s : Set E) : Set E := {x | ∀ ⦃y : E⦄, |y| ≤ |x| → y ∈ s}

private theorem solidInterior_subset (s : Set E) : solidInterior s ⊆ s := fun _ hx => hx le_rfl

private theorem isSolid_solidInterior (s : Set E) :
    LatticeOrderedAddCommGroup.IsSolid (solidInterior s) := by
  intro x hx y hy z hz
  exact hx (hz.trans hy)

variable [IsOrderedAddMonoid E] [VectorLattice E]

private theorem convex_solidInterior {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (solidInterior s) := by
  intro x hx y hy a b ha hb hab z hz
  by_cases ha_zero : a = 0
  · subst a
    have hb_one : b = 1 := by linarith
    rw [zero_smul, zero_add, hb_one, one_smul] at hz
    exact hy hz
  by_cases hb_zero : b = 0
  · subst b
    have ha_one : a = 1 := by linarith
    rw [zero_smul, add_zero, ha_one, one_smul] at hz
    exact hx hz
  let v : Fin 2 → E := ![a • |x|, b • |y|]
  have hv_nonneg : ∀ i, 0 ≤ v i := by
    intro i
    fin_cases i <;> simp [v, smul_nonneg, ha, hb, abs_nonneg]
  have hz_le_sum : |z| ≤ ∑ i, v i := by
    calc
      |z| ≤ |a • x + b • y| := hz
      _ ≤ |a • x| + |b • y| := abs_add_le _ _
      _ = a • |x| + b • |y| := by
        rw [abs_smul', abs_smul', abs_of_nonneg ha, abs_of_nonneg hb]
      _ = ∑ i, v i := by simp [v, Fin.sum_univ_two]
  obtain ⟨w, hw_sum, hw_abs⟩ := riesz_decomposition_abs z v hv_nonneg hz_le_sum
  have hw0_le : |w 0| ≤ a • |x| := by
    have := hw_abs 0
    simpa [v] using this.trans inf_le_right
  have hw1_le : |w 1| ≤ b • |y| := by
    have := hw_abs 1
    simpa [v] using this.trans inf_le_right
  have hc0 : a⁻¹ • w 0 ∈ s := by
    apply hx
    rw [abs_smul', abs_of_nonneg (inv_nonneg.mpr ha)]
    have h := smul_le_smul_of_nonneg_left hw0_le (inv_nonneg.mpr ha)
    rwa [smul_smul, inv_mul_cancel₀ ha_zero, one_smul] at h
  have hc1 : b⁻¹ • w 1 ∈ s := by
    apply hy
    rw [abs_smul', abs_of_nonneg (inv_nonneg.mpr hb)]
    have h := smul_le_smul_of_nonneg_left hw1_le (inv_nonneg.mpr hb)
    rwa [smul_smul, inv_mul_cancel₀ hb_zero, one_smul] at h
  have hz_mem : a • (a⁻¹ • w 0) + b • (b⁻¹ • w 1) ∈ s :=
    hs hc0 hc1 ha hb hab
  convert hz_mem using 1
  rw [smul_smul, smul_smul, mul_inv_cancel₀ ha_zero, mul_inv_cancel₀ hb_zero,
    one_smul, one_smul]
  rw [Fin.sum_univ_two] at hw_sum
  exact hw_sum

variable [TopologicalSpace E] [IsLocallyConvexSolidVectorLattice E]

/-- In a locally convex-solid vector lattice, zero has a neighborhood basis consisting of sets
that are both convex and solid. -/
theorem hasBasis_convex_solid :
    (𝓝 (0 : E)).HasBasis
      (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ Convex ℝ s ∧
        LatticeOrderedAddCommGroup.IsSolid s) id := by
  rw [Filter.hasBasis_self]
  intro U hU
  rcases IsLocallySolidVectorLattice.hasBasis_solid.mem_iff.mp hU with ⟨S, hS, hSU⟩
  rcases (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.mp hS.1 with ⟨C, hC, hCS⟩
  rcases IsLocallySolidVectorLattice.hasBasis_solid.mem_iff.mp hC.1 with ⟨V, hV, hVC⟩
  refine ⟨solidInterior C, ?_, ⟨convex_solidInterior hC.2, isSolid_solidInterior C⟩, ?_⟩
  · exact Filter.mem_of_superset hV.1 fun x hx y hy => hVC (hV.2 hx hy)
  · exact fun x hx => hSU (hCS (solidInterior_subset C hx))

end IsLocallyConvexSolidVectorLattice
