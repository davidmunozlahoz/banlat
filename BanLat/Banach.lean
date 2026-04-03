import BanLat.Normed
import BanLat.Hom
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Banach lattices

A **Banach lattice** is a normed vector lattice with a complete norm. The main structural
result stated here is that every vector lattice isomorphism between Banach lattices is
automatically a Banach space isomorphism: continuity of the inverse follows for free from
the lattice structure.
-/

/-- A Banach lattice is a normed vector lattice with a complete norm. -/
class BanachLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends NormedVectorLattice X, CompleteSpace X

namespace VecLatEquiv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- A vector lattice isomorphism between Banach lattices extends to a continuous linear
equivalence. -/
noncomputable def toContinuousLinearEquiv (e : VecLatEquiv X Y) : X ≃L[ℝ] Y := by
  sorry

end VecLatEquiv
