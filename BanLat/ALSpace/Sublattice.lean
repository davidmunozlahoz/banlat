import BanLat.ALSpace.Basic
import BanLat.Substructures.Ideal

/-!
# Closed sublattices of AL-spaces

This file records that a closed vector sublattice of an AL-space is again an
AL-space, with the induced lattice operations and subspace norm.
-/

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

private noncomputable def instLatticeClosedSublattice
    (Y : VectorSublattice X) : Lattice Y.toSubmodule where
  sup x y := ⟨x.1 ⊔ y.1, Y.sup_mem x.2 y.2⟩
  inf x y := ⟨x.1 ⊓ y.1, Y.inf_mem x.2 y.2⟩
  le_sup_left := fun x y => show x.1 ≤ x.1 ⊔ y.1 from le_sup_left
  le_sup_right := fun x y => show y.1 ≤ x.1 ⊔ y.1 from le_sup_right
  sup_le := fun x y z h1 h2 => show x.1 ⊔ y.1 ≤ z.1 from sup_le h1 h2
  inf_le_left := fun x y => show x.1 ⊓ y.1 ≤ x.1 from inf_le_left
  inf_le_right := fun x y => show x.1 ⊓ y.1 ≤ y.1 from inf_le_right
  le_inf := fun x y z h1 h2 =>
    show x.1 ≤ y.1 ⊓ z.1 from le_inf h1 h2

private instance instIsOrderedAddMonoidClosedSublattice
    (Y : VectorSublattice X) :
    @IsOrderedAddMonoid Y.toSubmodule inferInstance
      (instLatticeClosedSublattice Y).toPartialOrder where
  add_le_add_left := by
    intro a b (h : a.1 ≤ b.1) c
    exact add_le_add_left h c.1
  add_le_add_right := by
    intro a b (h : a.1 ≤ b.1) c
    exact add_le_add_right h c.1

/-- A closed vector sublattice of an AL-space, equipped with the subspace norm
and induced lattice operations, is an AL-space. -/
instance instALSpace_closedSublattice (Y : VectorSublattice X)
    (hclosed : IsClosed (Y : Set X)) :
    @ALSpace Y.toSubmodule Y.toSubmodule.normedAddCommGroup
      (instLatticeClosedSublattice Y)
      (instIsOrderedAddMonoidClosedSublattice Y) := by
  letI : NormedAddCommGroup Y.toSubmodule :=
    Y.toSubmodule.normedAddCommGroup
  letI : Lattice Y.toSubmodule := instLatticeClosedSublattice Y
  letI : IsOrderedAddMonoid Y.toSubmodule :=
    instIsOrderedAddMonoidClosedSublattice Y
  exact {
    toNormedVectorLattice := {
      toVectorLattice := {
        toModule := Y.toSubmodule.module
        smul_le_smul_of_nonneg_left := by
          intro c hc x y hxy
          change c • x.1 ≤ c • y.1
          exact smul_le_smul_of_nonneg_left hxy hc
      }
      solid := by
        intro x y h
        change ‖x.1‖ ≤ ‖y.1‖
        exact norm_le_norm_of_abs_le_abs h
      norm_smul := by
        intro r x
        change ‖r • x.1‖ = ‖r‖ * ‖x.1‖
        exact norm_smul r x.1
    }
    toCompleteSpace := by
      haveI : IsClosed (Y.toSubmodule : Set X) := hclosed
      infer_instance
    norm_add_eq_of_inf_eq_zero := by
      intro x y hxy
      change ‖x.1 + y.1‖ = ‖x.1‖ + ‖y.1‖
      exact ALSpace.norm_add_eq_of_inf_eq_zero (congrArg Subtype.val hxy)
  }

end ALSpace
