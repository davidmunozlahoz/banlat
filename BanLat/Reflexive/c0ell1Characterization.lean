/-
Authors: Pedro Tradacete
-/

import BanLat.KBSpace.C0
import BanLat.OrderContinuous.DualOrderContinuous
import BanLat.Reflexive.SequenceSpaces

/-!
# Reflexivity of Banach lattices

A Banach lattice is a reflexive Banach space if and only if it does not contain closed
vector sublattices isomorphic to `c₀` nor `ℓ¹`. This is also equivalent to not
containing closed subspaces isomorphic to  `c₀` nor `ℓ¹`.
-/

noncomputable section

open Set
open scoped ZeroAtInfty lp

namespace BidualSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- If the dual norm is order continuous, a positive functional on the bidual dominated
by evaluation at a dual vector is zero whenever it vanishes on the canonical image. -/
private lemma eq_zero_of_le_inclusion_of_vanishes [IsOrderContinuousNorm (StrongDual ℝ X)]
    {F : StrongDual ℝ (BidualSpace X)} {φ : StrongDual ℝ X} (hF : 0 ≤ F)
    (hle : F ≤ inclusion φ) (hvanish : ∀ x : X, F (inclusion x) = 0) : F = 0 := by
  obtain ⟨J, hJ⟩ := isOrderContinuousNorm_iff_range_inclusion_eq_orderIdeal.mp
    (inferInstance : IsOrderContinuousNorm (StrongDual ℝ X))
  obtain ⟨ψ, rfl⟩ := (show F ∈ range (inclusion (X := StrongDual ℝ X)) from
    hJ.symm ▸ (show F ∈ (J : Set (BidualSpace (StrongDual ℝ X))) from
      J.solid (show inclusion φ ∈ (J : Set (BidualSpace (StrongDual ℝ X))) from
        hJ ▸ mem_range_self φ) hF hle))
  exact (congrArg (inclusion (X := StrongDual ℝ X))
    (show ψ = 0 from ContinuousLinearMap.ext hvanish)).trans (map_zero _)

/-- A positive operator on the bidual dominated by the identity and vanishing on the canonical
image of the original space in the bidual is annihilated by every positive evaluation functional. -/
private lemma evaluation_comp_eq_zero [IsOrderContinuousNorm (StrongDual ℝ X)]
    (T : BidualSpace X →L[ℝ] BidualSpace X)
    (hT : ∀ z, 0 ≤ z → 0 ≤ T z) (hle : ∀ z, 0 ≤ z → T z ≤ z)
    (hvanish : ∀ x : X, T (inclusion x) = 0)
    {φ : StrongDual ℝ X} (hφ : 0 ≤ φ) : (inclusion φ).comp T = 0 := by
  refine eq_zero_of_le_inclusion_of_vanishes (φ := φ) ?_ ?_ ?_
  · exact StrongDual.le_iff.mpr fun z hz ↦ StrongDual.le_iff.mp (hT z hz) φ hφ
  · exact StrongDual.le_iff.mpr fun z hz ↦ StrongDual.le_iff.mp (hle z hz) φ hφ
  · exact fun x ↦ (congrArg (inclusion φ) (hvanish x)).trans (map_zero _)

/-- With order continuous dual norm, a positive operator below the identity on the bidual
which vanishes on the canonical image of the original space in the bidual is zero. -/
private lemma operator_eq_zero_of_vanishes [IsOrderContinuousNorm (StrongDual ℝ X)]
    (T : BidualSpace X →L[ℝ] BidualSpace X)
    (hT : ∀ z, 0 ≤ z → 0 ≤ T z) (hle : ∀ z, 0 ≤ z → T z ≤ z)
    (hvanish : ∀ x : X, T (inclusion x) = 0) : T = 0 := by
  have heval (z : BidualSpace X) (φ : StrongDual ℝ X) (hφ : 0 ≤ φ) : (T z) φ = 0 :=
    congrArg (fun F : StrongDual ℝ (BidualSpace X) ↦ F z)
      (evaluation_comp_eq_zero T hT hle hvanish hφ)
  exact ContinuousLinearMap.ext fun z ↦ le_antisymm
    (StrongDual.le_iff.mpr fun φ hφ ↦ (heval z φ hφ).le)
    (StrongDual.nonneg_iff.mpr fun φ hφ ↦ (heval z φ hφ).ge)

/-- A KB-space with order continuous dual norm is reflexive. -/
theorem isReflexiveBanachSpace_of_isKbSpace_of_dual_isOrderContinuousNorm
    [IsKbSpace X] [IsOrderContinuousNorm (StrongDual ℝ X)] :
    IsReflexiveBanachSpace ℝ X := by
  obtain ⟨B, hB⟩ := IsKbSpace.exists_band_range_inclusion (X := X)
  obtain ⟨P, hP⟩ := HasProjectionProperty.exists_projectionBand B
  have hQ : Positive (LinearMap.id - P.bandProjection) :=
    fun z hz ↦ sub_nonneg.mpr (Positive.le_iff.mp P.bandProjection_le_id z hz)
  let Q : BidualSpace X →L[ℝ] BidualSpace X :=
    ⟨LinearMap.id - P.bandProjection, Positive.continuous hQ⟩
  have hzero : Q = 0 := operator_eq_zero_of_vanishes Q hQ
    (fun z hz ↦ sub_le_self z (Positive.zero_le_iff.mp P.bandProjection_nonneg z hz))
    (fun x ↦ sub_eq_zero.mpr (P.bandProjection_eq_of_mem
      (show inclusion x ∈ (P : Set (BidualSpace X)) from
        (hB.trans hP.symm) ▸ mem_range_self x)).symm)
  intro z
  have hz : z = P.bandProjection z :=
    sub_eq_zero.mp (congrArg (fun T : BidualSpace X →L[ℝ] BidualSpace X ↦ T z) hzero)
  exact (show z ∈ range (inclusion (X := X)) from
    (hB.trans hP.symm).symm ▸ (show z ∈ (P : Set (BidualSpace X)) from
      hz ▸ P.bandProjection_mem z))

/-- A closed subspace isomorphic to a nonreflexive space contradicts reflexivity. -/
private lemma not_exists_closedSubspace_continuousLinearEquiv {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hY : ¬ IsReflexiveBanachSpace ℝ Y) (hX : IsReflexiveBanachSpace ℝ X) :
    ¬ ∃ S : Submodule ℝ X, IsClosed (S : Set X) ∧ Nonempty (Y ≃L[ℝ] S) := by
  rintro ⟨S, hS, ⟨e⟩⟩
  exact hY (IsReflexiveBanachSpace.of_continuousLinearEquiv e.symm
    (IsReflexiveBanachSpace.closedSubmodule S hS hX))

/-- Every closed lattice copy is also a closed linear copy. -/
private lemma not_containsLatticeCopy_of_no_closed_subspace {Y : Type*}
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (h : ¬ ∃ S : Submodule ℝ X, IsClosed (S : Set X) ∧ Nonempty (Y ≃L[ℝ] S)) :
    ¬ ContainsLatticeCopy X Y := by
  rintro ⟨Z, hZ, ⟨e⟩⟩
  let := Z.banachLatticeCoe hZ
  exact h ⟨Z.toSubmodule, hZ, ⟨e.toContinuousLinearEquiv⟩⟩

/-- Excluding the two classical sequence sublattices gives reflexivity. -/
private lemma isReflexiveBanachSpace_of_not_containsLatticeCopy
    (hc0 : ¬ ContainsLatticeCopy X C₀(ℕ, ℝ))
    (h1 : ¬ ContainsLatticeCopy X ℓ¹(ℕ, ℝ)) :
    IsReflexiveBanachSpace ℝ X := by
  let := BanachLattice.isKbSpace_of_not_containsLatticeCopy_c0 hc0
  let := BanachLattice.dual_isOrderContinuousNorm_of_not_containsLatticeCopy_ell1 h1
  exact isReflexiveBanachSpace_of_isKbSpace_of_dual_isOrderContinuousNorm

/-- A real Banach lattice is reflexive exactly when it contains neither a closed
linear subspace isomorphic to `C₀(ℕ, ℝ)` nor one isomorphic to `ℓ¹(ℕ, ℝ)`. -/
theorem isReflexiveBanachSpace_iff_no_closed_subspace_c0_ell1 :
    IsReflexiveBanachSpace ℝ X ↔
      (¬ ∃ S : Submodule ℝ X, IsClosed (S : Set X) ∧ Nonempty (C₀(ℕ, ℝ) ≃L[ℝ] S)) ∧
      (¬ ∃ S : Submodule ℝ X, IsClosed (S : Set X) ∧ Nonempty (ℓ¹(ℕ, ℝ) ≃L[ℝ] S)) := by
  constructor
  · exact fun h ↦ ⟨not_exists_closedSubspace_continuousLinearEquiv
      ZeroAtInftyContinuousMap.not_isReflexiveBanachSpace h,
      not_exists_closedSubspace_continuousLinearEquiv
        lp.not_isReflexiveBanachSpace_ell1 h⟩
  · exact fun ⟨hc0, h1⟩ ↦ isReflexiveBanachSpace_of_not_containsLatticeCopy
      (not_containsLatticeCopy_of_no_closed_subspace hc0)
      (not_containsLatticeCopy_of_no_closed_subspace h1)

/-- A real Banach lattice is reflexive exactly when it contains neither a closed
vector sublattice isomorphic to `C₀(ℕ, ℝ)` nor one isomorphic to `ℓ¹(ℕ, ℝ)`. -/
theorem isReflexiveBanachSpace_iff_not_containsLatticeCopy_c0_ell1 :
    IsReflexiveBanachSpace ℝ X ↔
      ¬ ContainsLatticeCopy X C₀(ℕ, ℝ) ∧ ¬ ContainsLatticeCopy X ℓ¹(ℕ, ℝ) := by
  constructor
  · intro h
    obtain ⟨hc0, h1⟩ := isReflexiveBanachSpace_iff_no_closed_subspace_c0_ell1.mp h
    exact ⟨not_containsLatticeCopy_of_no_closed_subspace hc0,
      not_containsLatticeCopy_of_no_closed_subspace h1⟩
  · exact fun ⟨hc0, h1⟩ ↦ isReflexiveBanachSpace_of_not_containsLatticeCopy hc0 h1

end BidualSpace
