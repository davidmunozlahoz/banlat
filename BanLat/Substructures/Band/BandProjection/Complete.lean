/-
Authors: Pedro Tradacete
-/

import BanLat.Substructures.Band.BandProjection.Lattice

/-!
# Covering families of projection bands

A family of projection bands is covering when its supremum is the whole space.
In a vector lattice with the projection property, the band projections associated
with a covering family separate points.
-/

namespace ProjectionBand

variable {D : Type*} [AddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [VectorLattice D]
  [HasProjectionProperty D]

/-- The band projections associated with a covering family separate points.
This is the uniqueness principle behind restriction of local sections. -/
theorem eq_of_bandProjection_eq_on_cover (A : Set (ProjectionBand D))
    (hA : sSup A = ⊤) {x y : D}
    (hxy : ∀ B ∈ A, B.bandProjection x = B.bandProjection y) : x = y := by
  let z := x - y
  let C : Band D := Band.disjointComplement ({z} : Set D)
  have hBC : ∀ B ∈ A, B ≤ ofBand C := by
    intro B hB v hv
    have hBz : B.bandProjection z = 0 := by
      dsimp [z]
      rw [map_sub, hxy B hB, sub_self]
    have hzBd : z ∈ disjointComplement (B : Set D) := by
      simpa only [hBz, sub_zero] using B.id_sub_bandProjection_mem z
    change v ∈ (ofBand C).toBand
    rw [toBand_ofBand]
    change ∀ a ∈ ({z} : Set D), IsVLDisjoint v a
    intro a ha
    have haz : a = z := ha
    subst a
    exact isVLDisjoint_comm.mp (hzBd v hv)
  have htopC : (⊤ : ProjectionBand D) ≤ ofBand C := by
    rw [← hA]
    exact sSup_le hBC
  have hzC : z ∈ C := by
    have hzTop : z ∈ (⊤ : ProjectionBand D) := ProjectionBand.mem_top
    have := htopC hzTop
    change z ∈ (ofBand C).toBand at this
    rwa [toBand_ofBand] at this
  have hz0 : z = 0 :=
    Set.mem_singleton_iff.mp
      (disjointComplement_inter_eq_zero ({z} : Set D) ⟨rfl, hzC⟩)
  exact sub_eq_zero.mp hz0

end ProjectionBand
