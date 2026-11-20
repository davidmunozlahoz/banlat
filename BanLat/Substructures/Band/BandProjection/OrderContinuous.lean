/-
Authors: Pedro Tradacete, David Muñoz-Lahoz
-/

import BanLat.Substructures.Band.BandProjection.Basic
import BanLat.Operators.OrderContinuous

/-!
# Order continuity of band projections

Band projections are order continuous operators and preserve existing suprema.
-/

namespace ProjectionBand

variable {D : Type*} [AddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [VectorLattice D]

/-- A band projection is order continuous. -/
theorem isOrderContinuousOp_bandProjection (B : ProjectionBand D) :
    IsOrderContinuousOp B.bandProjection := by
  have hpos : Positive B.bandProjection := Positive.zero_le_iff.mp B.bandProjection_nonneg
  rintro ι _ _ _ x a ⟨κ, _, _, _, r, hr, hrnn, hrglb, hrevent⟩
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hr, hrnn, hrglb,
    fun k ↦ (hrevent k).mono fun i hi ↦ ?_⟩
  rw [← map_sub]
  exact (hpos.abs_le_map_abs _).trans
    ((Positive.le_iff.mp B.bandProjection_le_id _ (abs_nonneg _)).trans hi)

/-- A band projection sends an existing supremum to the supremum of the
projected family. This is a consequence of band projections being order continuous
lattice homomorphisms. -/
theorem isLUB_bandProjection_image (B : ProjectionBand D) {S : Set D} {s : D}
    (hs : IsLUB S s) :
    IsLUB (B.bandProjection '' S) (B.bandProjection s) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact (Positive.monotone_iff.mpr
      (Positive.zero_le_iff.mp B.bandProjection_nonneg)) (hs.1 hx)
  · intro u hu
    have hbound : ∀ x ∈ S, x ≤ u + Bᶜ.bandProjection s := by
      intro x hx
      have hPx : B.bandProjection x ≤ u := hu ⟨x, hx, rfl⟩
      have hQx : Bᶜ.bandProjection x ≤ Bᶜ.bandProjection s :=
        (Positive.monotone_iff.mpr
          (Positive.zero_le_iff.mp Bᶜ.bandProjection_nonneg)) (hs.1 hx)
      have hdecomp_x : x = B.bandProjection x + Bᶜ.bandProjection x := by
        rw [ProjectionBand.bandProjection_compl]
        simp
      rw [hdecomp_x]
      exact add_le_add hPx hQx
    have hsu : s ≤ u + Bᶜ.bandProjection s := hs.2 hbound
    have hdecomp_s : s = B.bandProjection s + Bᶜ.bandProjection s := by
      rw [ProjectionBand.bandProjection_compl]
      simp
    have hsu' : B.bandProjection s + Bᶜ.bandProjection s ≤
        u + Bᶜ.bandProjection s := hdecomp_s.symm.le.trans hsu
    exact (add_le_add_iff_right _).mp hsu'

end ProjectionBand
