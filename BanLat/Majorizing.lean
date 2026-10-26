/-
Authors: Pedro Tradacete
-/

import BanLat.OrderDense

/-!
# Majorizing vector sublattices

A vector sublattice `Y` of a vector lattice `X` is **majorizing** when every element of `X` lies
below some element of `Y`. In a conditionally complete vector lattice, every element is the
supremum of the elements of an order-dense majorizing vector sublattice below it, and the
infimum of those above it.
-/

open Set

namespace VectorSublattice

section Majorizing

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]

/-- A vector sublattice is **majorizing** when every element lies below one of its elements. -/
abbrev IsMajorizing (Y : VectorSublattice X) : Prop :=
  IsCofinal (Y : Set X)

end Majorizing

variable {X : Type*} [AddCommGroup X] [ConditionallyCompleteLattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] {Y : VectorSublattice X}

/-- A least upper bound of the elements of an order-dense sublattice below `x` lies above `x`. -/
private lemma le_of_isLUB_inter_Iic (hd : Y.IsOrderDense) {x s : X}
    (hs : IsLUB ((Y : Set X) ∩ Iic x) s) : x ≤ s := by
  have hsx : s ≤ x := hs.2 fun _ hz ↦ hz.2
  by_contra h
  obtain ⟨w, hw, hw0, hwx⟩ := hd (sub_pos.mpr (hsx.lt_of_not_ge h))
  have hub : s - w ∈ upperBounds ((Y : Set X) ∩ Iic x) := fun z hz ↦
    le_sub_iff_add_le.mpr <| hs.1 ⟨add_mem hz.1 hw,
      (add_le_add (hs.1 hz) hwx).trans_eq (add_sub_cancel s x)⟩
  exact hw0.not_ge ((le_sub_self_iff s).mp (hs.2 hub))

/-- Every element is the supremum of the elements of an order-dense majorizing vector
sublattice below it. -/
theorem isLUB_inter_Iic (hd : Y.IsOrderDense) (hm : Y.IsMajorizing) (x : X) :
    IsLUB ((Y : Set X) ∩ Iic x) x := by
  obtain ⟨w, hw, hxw⟩ := hm (-x)
  have hs := isLUB_csSup (s := (Y : Set X) ∩ Iic x) ⟨-w, neg_mem hw, neg_le.mp hxw⟩
    ⟨x, fun _ hz ↦ hz.2⟩
  exact ⟨fun _ hz ↦ hz.2, fun _ hub ↦ (le_of_isLUB_inter_Iic hd hs).trans (hs.2 hub)⟩

/-- Every element is the infimum of the elements of an order-dense majorizing vector
sublattice above it. -/
theorem isGLB_inter_Ici (hd : Y.IsOrderDense) (hm : Y.IsMajorizing) (x : X) :
    IsGLB ((Y : Set X) ∩ Ici x) x := by
  have h : -((Y : Set X) ∩ Ici x) = (Y : Set X) ∩ Iic (-x) := by
    ext z
    simp
  rw [← isLUB_neg', h]
  exact isLUB_inter_Iic hd hm (-x)

end VectorSublattice
