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

private lemma countableChainCondition_of_injective (T : VecLatHom X Y)
    (hT : Function.Injective T) (hY : HasCountableChainCondition Y) :
    HasCountableChainCondition X := by
  intro D hD
  have hTD : IsDisjointSet (T '' D) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, hx0⟩
      exact hD.1 ((hT (hx0.trans (map_zero T).symm)) ▸ hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have hd := congrArg T (hD.2 hx hy (fun h ↦ hxy (congrArg T h)))
      simpa only [IsVLDisjoint, map_inf, T.map_abs, map_zero] using hd
  exact Set.countable_of_injective_of_countable_image hT.injOn (hY _ hTD)

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
