/-
Authors: Pedro Tradacete
-/

import BanLat.Dual
import BanLat.OrderContinuous.MeyerNieberg
import BanLat.SequenceCopies
import BanLat.Operators.Carrier
import BanLat.Substructures.Band.BandProjection.Complete

/-!
# The summable-sequence obstruction to dual order continuity

For an order-continuous Banach lattice, failure of order continuity in the dual
produces a closed vector sublattice isomorphic to `ℓ¹`.
-/

noncomputable section

open Set
open scoped lp

namespace BanachLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X] [IsOrderContinuousNorm X]

/-- Projection onto the carrier of a positive functional preserves its value
on positive vectors and removes the part in its null band. -/
private lemma exists_carrier_projection (φ : StrongDual ℝ X) (hφ : 0 ≤ φ) :
    ∃ P : ProjectionBand X,
      (P : Set X) = (OrderBoundedHom.carrier (StrongDual.toOrderDualSpace φ) : Set X) ∧
      ∀ x : X, 0 ≤ x → φ (P.bandProjection x) = φ x := by
  let := conditionallyCompleteLatticeOfIsOrderContinuousNorm (X := X)
  obtain ⟨P, hP⟩ := HasProjectionProperty.exists_projectionBand
    (OrderBoundedHom.carrier (StrongDual.toOrderDualSpace φ))
  obtain ⟨B, hB⟩ := OrderBoundedHom.exists_band_coe_eq_null_of_orderContinuous
    (StrongDual.toOrderDualSpace φ)
    (OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm _)
  have hdc : (P : Set X)ᵈ = (OrderBoundedHom.null (StrongDual.toOrderDualSpace φ) : Set X) := by
    rw [hP]
    change ((OrderBoundedHom.null (StrongDual.toOrderDualSpace φ) : Set X)ᵈ)ᵈ = _
    rw [← hB, Band.eq_disjointComplement_disjointComplement]
  refine ⟨P, hP, fun x hx ↦ ?_⟩
  have hz := P.id_sub_bandProjection_mem x
  rw [hdc] at hz
  have hzero := OrderBoundedHom.mem_null.mp hz
  rw [abs_of_nonneg (show 0 ≤ StrongDual.toOrderDualSpace φ from hφ),
    abs_of_nonneg (sub_nonneg.mpr (show P.bandProjection x ≤ x from
      Positive.le_iff.mp P.bandProjection_le_id x hx))] at hzero
  exact (sub_eq_zero.mp (show φ x - φ (P.bandProjection x) = 0 from
    (map_sub φ x (P.bandProjection x)).symm.trans hzero)).symm

omit [IsOrderContinuousNorm X] in
/-- A positive functional with norm at least `ε > 0` takes a value at least
`ε / 2` on some positive vector in the closed unit ball. -/
private lemma exists_positive_large_apply {φ : StrongDual ℝ X} (hφ : 0 ≤ φ)
    {ε : ℝ} (hε : 0 < ε) (hn : ε ≤ ‖φ‖) :
    ∃ x : X, 0 ≤ x ∧ ‖x‖ ≤ 1 ∧ ε / 2 ≤ φ x := by
  obtain ⟨_, ⟨x, ⟨hx, hp⟩, rfl⟩, hlarge⟩ := exists_lt_of_lt_csSup
    (s := φ '' ({x | ‖x‖ ≤ 1} ∩ {x | 0 ≤ x}))
    ⟨0, 0, ⟨by simp, le_rfl⟩, map_zero φ⟩
    ((half_lt_self hε).trans_le (hn.trans_eq (StrongDual.norm_of_nonneg hφ)))
  exact ⟨x, hp, hx, hlarge.le⟩

/-- A positive functional with norm at least `ε > 0` takes a value at least
`ε / 2` on some positive vector in the unit-ball lying in its own carrier. -/
private lemma exists_positive_mem_carrier_large {φ : StrongDual ℝ X} (hφ : 0 ≤ φ)
    {ε : ℝ} (hε : 0 < ε) (hn : ε ≤ ‖φ‖) :
    ∃ x : X, 0 ≤ x ∧ ‖x‖ ≤ 1 ∧
      x ∈ OrderBoundedHom.carrier (StrongDual.toOrderDualSpace φ) ∧ ε / 2 ≤ φ x := by
  obtain ⟨x, hx, hnorm, hlarge⟩ := exists_positive_large_apply hφ hε hn
  obtain ⟨P, hP, heval⟩ := exists_carrier_projection φ hφ
  have hp : 0 ≤ P.bandProjection x := Positive.zero_le_iff.mp P.bandProjection_nonneg x hx
  refine ⟨P.bandProjection x, hp, ?_, ?_, (heval x hx).symm ▸ hlarge⟩
  · refine (norm_le_norm_of_abs_le_abs ?_).trans hnorm
    simpa only [abs_of_nonneg hp, abs_of_nonneg hx] using
      (show P.bandProjection x ≤ x from Positive.le_iff.mp P.bandProjection_le_id x hx)
  · exact (show P.bandProjection x ∈ (OrderBoundedHom.carrier
      (StrongDual.toOrderDualSpace φ) : Set X) from hP ▸ P.bandProjection_mem x)

/-- Vectors in the carriers of disjoint positive continuous functionals are
disjoint. -/
private lemma disjoint_of_mem_carriers {φ ψ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ) (h : IsVLDisjoint φ ψ) {x y : X}
    (hx : x ∈ OrderBoundedHom.carrier (StrongDual.toOrderDualSpace φ))
    (hy : y ∈ OrderBoundedHom.carrier (StrongDual.toOrderDualSpace ψ)) : IsVLDisjoint x y := by
  let e : StrongDual ℝ X ≃o OrderDualSpace X :=
    { StrongDual.equivOrderDualSpace.toEquiv with map_rel_iff' := Iff.rfl }
  have hd : IsVLDisjoint (StrongDual.toOrderDualSpace φ) (StrongDual.toOrderDualSpace ψ) :=
    isVLDisjoint_of_inf_eq_zero ((e.map_inf φ ψ).symm.trans
      ((congrArg e (inf_eq_zero_of_isVLDisjoint hφ hψ h)).trans rfl))
  have hs : (OrderBoundedHom.carrier (StrongDual.toOrderDualSpace φ) : Set X) ⊆
      (OrderBoundedHom.carrier (StrongDual.toOrderDualSpace ψ) : Set X)ᵈ :=
    ((OrderBoundedHom.nakano_theorem (StrongDual.toOrderDualSpace φ)
      (StrongDual.toOrderDualSpace ψ)
      (OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm _)
      (OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm _)).out 1 4).mp hd
  exact hs hx y hy

/-- In an order-continuous Banach lattice, the absence of a closed `ℓ¹` sublattice
forces the continuous dual to have order-continuous norm. -/
theorem dual_isOrderContinuousNorm_of_not_containsLatticeCopy_ell1
    (h : ¬ ContainsLatticeCopy X ℓ¹(ℕ, ℝ)) : IsOrderContinuousNorm (StrongDual ℝ X) := by
  by_contra hn
  obtain ⟨φ, ψ, ε, hε, hp, hd, hle, hnorm⟩ :=
    exists_disjoint_norm_ge_of_not_isOrderContinuousNorm hn
  choose x hx hxn hxc hlarge using fun n ↦ exists_positive_mem_carrier_large (hp n) hε (hnorm n)
  refine h (containsLatticeCopy_ell1_of_disjoint hx (fun n m hnm ↦
    disjoint_of_mem_carriers (hp n) (hp m) (hd hnm) (hxc n) (hxc m))
    hxn ψ (half_pos hε) fun n ↦ ?_)
  exact (hlarge n).trans (StrongDual.le_iff.mp (hle n) (x n) (hx n))

end BanachLattice
