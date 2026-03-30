import BanLat.Basic
import BanLat.Hom

class NormedLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] extends NormedSpace ℝ X, PosSMulMono ℝ X where
    norm_lattice : ∀ x y : X, |x| ≤ |y| → ‖x‖ ≤ ‖y‖
    complete : CompleteSpace X

namespace BanachLattice

variable {X Y : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [BanachLattice Y]

instance : VectorLattice X where

theorem veclathom_cont
    (T : VecLatHom X Y) : Continuous T := by
  sorry

def toContinuousLinearEquiv
    (e : VecLatEquiv X Y) : X ≃L[ℝ] Y := by
  sorry

end BanachLattice
