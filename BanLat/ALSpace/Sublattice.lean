/-
Authors: David Muñoz-Lahoz
-/

import BanLat.ALSpace.Basic
import BanLat.Substructures.Sublattice

/-!
# Closed sublattices of AL-spaces

This file records that a closed vector sublattice of an AL-space is again an
AL-space, with the induced lattice operations and subspace norm.
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
