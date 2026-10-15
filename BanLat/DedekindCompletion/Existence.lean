/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.Scalar
import BanLat.DedekindCompletion.Uniqueness

/-!
# Existence and uniqueness of Dedekind completion

Bounded Dedekind cuts give an order-dense majorizing embedding of every
Archimedean vector lattice into a conditionally complete vector lattice.
Any two such completions are vector-lattice isomorphic by an equivalence
that agrees with their embeddings of the original lattice.
-/

noncomputable section

open Set

universe u

/-- A conditionally complete vector lattice containing the original lattice
as an order-dense majorizing vector sublattice. -/
structure DedekindCompletion (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] where
  /-- The underlying type of the completion. -/
  carrier : Type u
  /-- The additive group structure on the completion. -/
  [group : AddCommGroup carrier]
  /-- The conditionally complete lattice structure on the completion. -/
  [lattice : ConditionallyCompleteLattice carrier]
  /-- Addition is compatible with the order. -/
  [ordered : IsOrderedAddMonoid carrier]
  /-- The real vector-lattice structure on the completion. -/
  [vector : VectorLattice carrier]
  /-- The vector-lattice embedding of the original lattice. -/
  inclusion : VecLatHom X carrier
  /-- The inclusion is injective. -/
  injective : Function.Injective inclusion
  /-- The image of the inclusion is order dense. -/
  dense : IsOrderDense (range inclusion)
  /-- Every completion element has a majorant in the image of the inclusion. -/
  majorizing : ∀ y : carrier, ∃ x : X, y ≤ inclusion x

attribute [instance] DedekindCompletion.group DedekindCompletion.lattice
  DedekindCompletion.ordered DedekindCompletion.vector

namespace DedekindCompletion

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- The bounded-cut completion is Archimedean by conditional completeness. -/
instance [IsVLArchimedean X] : IsVLArchimedean (BoundedCut X) :=
  IsVLArchimedean_of_sigmaConditionallyCompleteLattice

/-- The Dedekind completion of an Archimedean vector lattice, constructed from bounded cuts. -/
def ofBoundedCuts [IsVLArchimedean X] : DedekindCompletion X where
  carrier := BoundedCut X
  inclusion := BoundedCut.principalHom
  injective := BoundedCut.principal_injective
  dense := BoundedCut.principal_orderDense
  majorizing := BoundedCut.majorizing

/-- The canonical vector-lattice equivalence between two Dedekind completions. -/
def equiv (D D' : DedekindCompletion X) : VecLatEquiv D.carrier D'.carrier :=
  completionVecLatEquiv D.inclusion D'.inclusion
    D.injective D'.injective D.dense D'.dense D.majorizing D'.majorizing

/-- The canonical equivalence agrees with the embeddings of the original lattice. -/
@[simp]
theorem equiv_apply_inclusion (D D' : DedekindCompletion X) (x : X) :
    D.equiv D' (D.inclusion x) = D'.inclusion x :=
  completionVecLatEquiv_apply_principal D.inclusion D'.inclusion
    D.injective D'.injective D.dense D'.dense D.majorizing D'.majorizing x

end DedekindCompletion
end
