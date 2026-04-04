import BanLat.Normed
import BanLat.Hom
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Banach lattices

A **Banach lattice** is a normed vector lattice with a complete norm.
-/

/-- A Banach lattice is a normed vector lattice with a complete norm. -/
class BanachLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends NormedVectorLattice X, CompleteSpace X
