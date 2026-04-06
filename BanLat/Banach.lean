import BanLat.Normed
import BanLat.Operators.Hom
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Banach lattices

A **Banach lattice** is a normed vector lattice with a complete norm. This file
also introduces `BanachLatEquiv`, the type of Banach lattice isomorphisms: real
linear isometric equivalences that also preserve `⊔` and `⊓`.
-/

/-- A Banach lattice is a normed vector lattice with a complete norm. -/
class BanachLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends NormedVectorLattice X, CompleteSpace X

/-- A **Banach lattice isomorphism** between two Banach lattices: a real linear
isometric equivalence that also preserves the lattice operations `⊔` and `⊓`.
Such a map is automatically an order isomorphism. -/
structure BanachLatEquiv (X Y : Type*)
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [BanachLattice X] [BanachLattice Y]
    extends X ≃ₗᵢ[ℝ] Y, LatticeHom X Y

namespace BanachLatEquiv

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- The canonical `FunLike` instance, making `BanachLatEquiv X Y` a type of
functions `X → Y`. -/
instance instFunLike : FunLike (BanachLatEquiv X Y) X Y where
  coe e := e.toFun
  coe_injective' := by
    intro f g h
    cases f; cases g
    congr 1
    exact LinearIsometryEquiv.toLinearEquiv_injective
      (LinearEquiv.toEquiv_injective (Equiv.coe_inj.mp h))

/-- Coerce a `BanachLatEquiv` to a continuous linear equivalence. -/
noncomputable def toContinuousLinearEquiv (e : BanachLatEquiv X Y) : X ≃L[ℝ] Y :=
  e.toLinearIsometryEquiv.toContinuousLinearEquiv

/-- Coerce a `BanachLatEquiv` to a `VecLatEquiv`. -/
def toVecLatEquiv (e : BanachLatEquiv X Y) : VecLatEquiv X Y :=
  { e.toLinearIsometryEquiv.toLinearEquiv with
    map_sup' := e.map_sup'
    map_inf' := e.map_inf' }

end BanachLatEquiv
