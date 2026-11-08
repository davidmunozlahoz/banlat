/-
Authors: David Muñoz-Lahoz, Pedro Tradacete
-/

import BanLat.ALSpace.Basic
import BanLat.Substructures.Band.Generated

/-!
# Closed sublattices and bands of AL-spaces

Closed vector sublattices of an AL-space are AL-spaces with the induced lattice operations
and subspace norm. In particular, every band inherits an AL-space structure.
-/

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

/-- A closed vector sublattice of an AL-space, equipped with the subspace norm
and induced lattice operations, is an AL-space. -/
@[reducible]
noncomputable def ofClosedSublattice (Y : VectorSublattice X)
    (hclosed : IsClosed (Y : Set X)) : ALSpace Y where
  toBanachLattice := Y.banachLatticeCoe hclosed
  norm_add_rpow_eq_of_isVLDisjoint := by
    simp only [NNReal.coe_one, Real.rpow_one]
    intro x y hxy
    change ‖x.1 + y.1‖ = ‖x.1‖ + ‖y.1‖
    simpa only [NNReal.coe_one, Real.rpow_one] using
      ALpSpace.norm_add_rpow_eq_of_isVLDisjoint (p := (1 : NNReal))
        (congrArg Subtype.val hxy)

end ALSpace

namespace Band

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

/-- A band of an AL-space, equipped with the induced lattice operations and subspace norm,
is an AL-space because it is a closed vector sublattice. -/
noncomputable instance instALSpaceCoe (B : Band X) : ALSpace B.toVectorSublattice :=
  ALSpace.ofClosedSublattice B.toVectorSublattice B.isClosed_coe

end Band
