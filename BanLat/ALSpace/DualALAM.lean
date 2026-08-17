import BanLat.ALSpace.Dual
import BanLat.AMSpace.Dual
import BanLat.Bidual

/-!
# Dual AL/AM characterisations

This file records the converse duality facts: if the norm dual of a Banach
lattice is an AL-space, then the original space is an AM-space, and if the norm
dual is an AM-space, then the original space is an AL-space.
-/

noncomputable section

namespace StrongDual

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

@[reducible]
private def canonicalALSpace (hX' : ALSpace (StrongDual ℝ X)) :
    ALSpace (StrongDual ℝ X) :=
  { (StrongDual.instBanachLattice (X := X) : BanachLattice (StrongDual ℝ X)) with
    norm_add_eq_of_inf_eq_zero := fun {_ _} h => hX'.norm_add_eq_of_inf_eq_zero h }

@[reducible]
private def canonicalAMSpace (hX' : AMSpace (StrongDual ℝ X)) :
    AMSpace (StrongDual ℝ X) :=
  { (StrongDual.instBanachLattice (X := X) : BanachLattice (StrongDual ℝ X)) with
    norm_add_eq_max_of_inf_eq_zero := fun {_ _} h =>
      hX'.norm_add_eq_max_of_inf_eq_zero h }

@[reducible]
private def bidual_amSpace_of_dual_alSpace (hX' : ALSpace (StrongDual ℝ X)) :
    AMSpace (BidualSpace X) := by
  letI : ALSpace (StrongDual ℝ X) := canonicalALSpace (X := X) hX'
  change AMSpace (StrongDual ℝ (StrongDual ℝ X))
  exact ALSpace.StrongDual.instAMSpace_of_alSpace (X := StrongDual ℝ X)

@[reducible]
private def bidual_alSpace_of_dual_amSpace (hX' : AMSpace (StrongDual ℝ X)) :
    ALSpace (BidualSpace X) := by
  letI : AMSpace (StrongDual ℝ X) := canonicalAMSpace (X := X) hX'
  change ALSpace (StrongDual ℝ (StrongDual ℝ X))
  exact AMSpace.StrongDual.instALSpace_of_amSpace (X := StrongDual ℝ X)

/-- If the norm dual of a Banach lattice is an AL-space, then the Banach lattice
is an AM-space. -/
@[reducible]
def amSpaceOfDualALSpace (hX' : ALSpace (StrongDual ℝ X)) : AMSpace X where
  norm_add_eq_max_of_inf_eq_zero {x y} hxy := by
    haveI : AMSpace (BidualSpace X) := bidual_amSpace_of_dual_alSpace (X := X) hX'
    have hxy' :
        @min (BidualSpace X) SemilatticeInf.toMin
          (BidualSpace.inclusion x) (BidualSpace.inclusion y) = 0 := by
      rw [← BidualSpace.inclusion_inf, hxy]
      exact (BidualSpace.inclusion (X := X)).map_zero
    have h :=
      @AMSpace.norm_add_eq_max_of_inf_eq_zero (BidualSpace X)
        ContinuousLinearMap.toNormedAddCommGroup inferInstance inferInstance inferInstance
        (BidualSpace.inclusion x) (BidualSpace.inclusion y) hxy'
    rw [← (BidualSpace.inclusion (X := X)).map_add,
      BidualSpace.norm_inclusion (X := X) (x + y),
      BidualSpace.norm_inclusion (X := X) x,
      BidualSpace.norm_inclusion (X := X) y] at h
    exact h

/-- If the norm dual of a Banach lattice is an AM-space, then the Banach lattice
is an AL-space. -/
@[reducible]
def alSpaceOfDualAMSpace (hX' : AMSpace (StrongDual ℝ X)) : ALSpace X where
  norm_add_eq_of_inf_eq_zero {x y} hxy := by
    haveI : ALSpace (BidualSpace X) := bidual_alSpace_of_dual_amSpace (X := X) hX'
    have hxy' :
        @min (BidualSpace X) SemilatticeInf.toMin
          (BidualSpace.inclusion x) (BidualSpace.inclusion y) = 0 := by
      rw [← BidualSpace.inclusion_inf, hxy]
      exact (BidualSpace.inclusion (X := X)).map_zero
    have h :=
      @ALSpace.norm_add_eq_of_inf_eq_zero (BidualSpace X)
        ContinuousLinearMap.toNormedAddCommGroup inferInstance inferInstance inferInstance
        (BidualSpace.inclusion x) (BidualSpace.inclusion y) hxy'
    rw [← (BidualSpace.inclusion (X := X)).map_add,
      BidualSpace.norm_inclusion (X := X) (x + y),
      BidualSpace.norm_inclusion (X := X) x,
      BidualSpace.norm_inclusion (X := X) y] at h
    exact h

end StrongDual

end
