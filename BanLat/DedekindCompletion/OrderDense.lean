/-
Authors: Pedro Tradacete
-/

import BanLat.OrderComplete
import BanLat.OrderDense
import BanLat.Operators.Hom

/-!
# Order-dense majorizing vector-lattice embeddings

Every element of a conditionally complete vector lattice is the supremum
of the elements of an order-dense majorizing sublattice below it, and the
infimum of those above it.
-/

open Set

namespace DedekindCompletion

universe u v

variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid Y]
  [VectorLattice Y]

/-- The least upper bound of image elements below `y` lies above `y`. -/
private lemma le_of_isLUB_range_below (j : VecLatHom X Y)
    (hd : IsOrderDense (range j)) (y s : Y)
    (hs : IsLUB {z : Y | z ∈ range j ∧ z ≤ y} s) : y ≤ s := by
  let A : Set Y := {z | z ∈ range j ∧ z ≤ y}
  have hsy : s ≤ y := hs.2 (fun _ hz ↦ hz.2)
  by_contra h
  have hlt : s < y := lt_of_le_of_ne hsy (by
    intro heq
    exact h heq.symm.le)
  obtain ⟨w, ⟨x, rfl⟩, hxpos, hxle⟩ := hd (sub_pos.mpr hlt)
  have hub : s - j x ∈ upperBounds A := by
    intro z hz
    obtain ⟨a, rfl⟩ := hz.1
    have hza : j a ≤ s := hs.1 hz
    have hnew : j (a + x) ∈ A := by
      refine ⟨⟨a + x, rfl⟩, ?_⟩
      calc
        j (a + x) = j a + j x := map_add j a x
        _ ≤ s + (y - s) := add_le_add hza hxle
        _ = y := by abel
    have hle : j a + j x ≤ s := by
      simpa only [map_add] using hs.1 hnew
    exact le_sub_iff_add_le.mpr hle
  have hnonpos : j x ≤ 0 := by
    have hle := hs.2 hub
    have hle' : s + j x ≤ s := le_sub_iff_add_le.mp hle
    exact (add_le_add_iff_left (s)).mp (by simpa only [add_zero] using hle')
  exact (not_le_of_gt hxpos) hnonpos

/-- Every element is the supremum of the elements of an order-dense
majorizing vector sublattice below it. -/
theorem isLUB_range_below (j : VecLatHom X Y)
    (hd : IsOrderDense (range j))
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) :
    IsLUB {z : Y | z ∈ range j ∧ z ≤ y} y := by
  let A : Set Y := {z | z ∈ range j ∧ z ≤ y}
  have hne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hm (-y)
    refine ⟨j (-x), ⟨-x, rfl⟩, ?_⟩
    simpa only [map_neg, neg_le] using hx
  have hs : IsLUB A (sSup A) := isLUB_csSup hne ⟨y, fun _ hz ↦ hz.2⟩
  exact ⟨fun _ hz ↦ hz.2, fun _ hub ↦
    (le_of_isLUB_range_below j hd y (sSup A) hs).trans (hs.2 hub)⟩

/-- Every element is the supremum of the embedded elements below it. -/
theorem isLUB_image_below (j : VecLatHom X Y)
    (hd : IsOrderDense (range j))
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) :
    IsLUB (j '' {x : X | j x ≤ y}) y := by
  convert isLUB_range_below j hd hm y using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

/-- The greatest lower bound of image elements above `y` lies below `y`. -/
private lemma le_of_isGLB_range_above (j : VecLatHom X Y)
    (hd : IsOrderDense (range j)) (y s : Y)
    (hs : IsGLB {z : Y | z ∈ range j ∧ y ≤ z} s) : s ≤ y := by
  let A : Set Y := {z | z ∈ range j ∧ y ≤ z}
  have hys : y ≤ s := hs.2 (fun _ hz ↦ hz.2)
  by_contra h
  have hlt : y < s := lt_of_le_of_ne hys (by
    intro heq
    exact h heq.symm.le)
  obtain ⟨w, ⟨x, rfl⟩, hxpos, hxle⟩ := hd (sub_pos.mpr hlt)
  have hlb : s + j x ∈ lowerBounds A := by
    intro z hz
    obtain ⟨a, rfl⟩ := hz.1
    have hza : s ≤ j a := hs.1 hz
    have hnew : j (a - x) ∈ A := by
      refine ⟨⟨a - x, rfl⟩, ?_⟩
      have hyax : y ≤ j a - j x := by
        have hle : j x ≤ j a - y :=
          hxle.trans (sub_le_sub_right hza _)
        exact le_sub_iff_add_le.mpr (by
          have := add_le_add_left hle y
          simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using this)
      simpa only [map_sub] using hyax
    have hle : s ≤ j a - j x := by
      simpa only [map_sub] using hs.1 hnew
    exact le_sub_iff_add_le.mp hle
  have hnonpos : j x ≤ 0 := by
    have hle := hs.2 hlb
    have hle' : s + j x ≤ s := hle
    exact (add_le_add_iff_left (s)).mp (by simpa only [add_zero] using hle')
  exact (not_le_of_gt hxpos) hnonpos

/-- Every element is the infimum of the elements of an order-dense
majorizing vector sublattice above it. -/
theorem isGLB_range_above (j : VecLatHom X Y)
    (hd : IsOrderDense (range j))
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) :
    IsGLB {z : Y | z ∈ range j ∧ y ≤ z} y := by
  let A : Set Y := {z | z ∈ range j ∧ y ≤ z}
  obtain ⟨x, hx⟩ := hm y
  have hs : IsGLB A (sInf A) :=
    isGLB_csInf ⟨j x, ⟨x, rfl⟩, hx⟩ ⟨y, fun _ hz ↦ hz.2⟩
  exact ⟨fun _ hz ↦ hz.2, fun _ hlb ↦
    (hs.2 hlb).trans (le_of_isGLB_range_above j hd y (sInf A) hs)⟩

end DedekindCompletion
