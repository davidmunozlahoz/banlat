import BanLat.Operators.OrderBounded
import BanLat.OrderComplete

/-!
# Regular operators

An operator between vector lattices is **regular** (`IsRegularOp`) if it can
be written as the difference of two positive operators. Every regular operator
is order bounded; when the codomain is order complete, the converse holds.
-/

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A linear map is **regular** if it is the difference of two positive
operators. -/
def IsRegularOp (f : X →ₗ[ℝ] Y) : Prop :=
  ∃ g h : X →ₗ[ℝ] Y, Positive g ∧ Positive h ∧ f = g - h

namespace IsRegularOp

/-- Every regular operator is order bounded. -/
theorem isOrderBounded {f : X →ₗ[ℝ] Y}
    (hf : IsRegularOp f) : IsOrderBounded f := by
  obtain ⟨g, h, hg, hh, rfl⟩ := hf
  exact IsOrderBounded.sub
    (Positive.isOrderBounded hg) (Positive.isOrderBounded hh)

end IsRegularOp
