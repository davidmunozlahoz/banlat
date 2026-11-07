/-
Authors: Pedro Tradacete
-/

import BanLat.Substructures.Band.BandProjection.PPP
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# The complete Boolean algebra of projection bands

In a vector lattice with the projection property, every band is a projection band.
Transporting arbitrary suprema and infima from the complete lattice of bands, the
Boolean algebra of projection bands becomes a complete Boolean algebra.
-/

noncomputable section

namespace ProjectionBand

variable {D : Type*} [AddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [VectorLattice D]

variable [HasProjectionProperty D]

/-- The projection band corresponding to a band when the projection property holds. -/
def ofBand (B : Band D) : ProjectionBand D :=
  Classical.choose (HasProjectionProperty.exists_projectionBand B)

/-- Converting a band to a projection band preserves its underlying band. -/
@[simp] theorem toBand_ofBand (B : Band D) :
    (ofBand B).toBand = B := by
  apply SetLike.ext'
  exact Classical.choose_spec (HasProjectionProperty.exists_projectionBand B)

/-- Supremum of projection bands, transported from bands. -/
noncomputable instance : SupSet (ProjectionBand D) where
  sSup S := ofBand (sSup (ProjectionBand.toBand '' S))

/-- Infimum of projection bands, transported from bands. -/
noncomputable instance : InfSet (ProjectionBand D) where
  sInf S := ofBand (sInf (ProjectionBand.toBand '' S))

/-- The existing finite Boolean operations on projection bands extend to a
complete lattice via the order equivalence with all bands. -/
noncomputable instance : CompleteLattice (ProjectionBand D) :=
  toBand_injective.completeLattice ProjectionBand.toBand
    (by intro P Q; rfl)
    (by intro P Q; rfl)
    (by intro P Q; exact ProjectionBand.sup_toBand P Q)
    (by intro P Q; exact ProjectionBand.inf_toBand P Q)
    (by intro S
        change (ofBand (sSup (ProjectionBand.toBand '' S))).toBand = _
        rw [toBand_ofBand, sSup_image])
    (by intro S
        change (ofBand (sInf (ProjectionBand.toBand '' S))).toBand = _
        rw [toBand_ofBand, sInf_image])
    (by rfl)
    (by rfl)

/-- Under the projection property, projection bands form a complete Boolean algebra. -/
noncomputable instance : CompleteBooleanAlgebra (ProjectionBand D) where
  __ := (inferInstance : CompleteLattice (ProjectionBand D))
  __ := (inferInstance : BooleanAlgebra (ProjectionBand D))

end ProjectionBand
