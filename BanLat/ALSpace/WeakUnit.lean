/-
Authors: Pedro Tradacete
-/

import BanLat.ALSpace.Kakutani
import BanLat.Examples.Lp.CountableChainCondition
import BanLat.OrderUnit.CountableChainCondition

/-!
# Weak order units in non-closed sublattices of AL-spaces

Every Banach lattice that admits an injective lattice homomorphism into an AL-space
with a weak order unit also has a weak order unit.
-/

noncomputable section

open MeasureTheory

namespace ALSpace

variable {X Y : Type*}
  [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X]
  [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [ALSpace Y]

/-- A Banach lattice that admits an injective lattice homomorphism into an AL-space with
a weak order unit also has a weak order unit. -/
theorem exists_weakOrderUnit_of_injective (T : VecLatHom X Y)
    (hT : Function.Injective T) {e : Y} (he : WeakOrderUnit e) :
    ∃ u : X, WeakOrderUnit u := by
  obtain ⟨Ω, mΩ, μ, hμ, φ, _⟩ :=
    exists_L1_banachLatEquiv_isFiniteMeasure_of_weakOrderUnit he
  apply exists_weakOrderUnit_of_hasCountableChainCondition
  exact countableChainCondition_of_injective (φ.toVecLatEquiv.toVecLatHom.comp T)
    (φ.toLinearIsometryEquiv.injective.comp hT) Lp.hasCountableChainCondition

end ALSpace
