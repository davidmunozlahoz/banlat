import BanLat.Operators.OrderBounded
import BanLat.Operators.RieszKantorovich
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

/-- When the codomain is order complete, every order bounded operator
is regular. -/
theorem IsOrderBounded.isRegularOp [IsOrderComplete Y]
    {f : X →ₗ[ℝ] Y} (hf : IsOrderBounded f) :
    IsRegularOp f := by
  let F : OrderBoundedHom X Y := ⟨f, hf⟩
  refine ⟨F⁺.toLinearMap, F⁻.toLinearMap, ?_, ?_, ?_⟩
  · intro x hx
    convert OrderBoundedHom.le_iff.mp (posPart_nonneg F) x hx using 1
  · intro x hx
    convert OrderBoundedHom.le_iff.mp (negPart_nonneg F) x hx using 1
  · exact (congrArg OrderBoundedHom.toLinearMap (posPart_sub_negPart F)).symm
