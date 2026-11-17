/-
Authors: Pedro Tradacete
-/

import BanLat.Operators.Hom

/-!
# Push-outs of Banach lattices

A push-out with norm control is a commuting square of lattice homomorphisms whose
outgoing maps are contractions. Compatible maps into any Banach lattice factor
uniquely through the square, with operator norm bounded by the larger input norm.
-/

universe u₀ u₁ u₂ u₃ v

namespace BanachLattice

variable {X₀ : Type u₀} {X₁ : Type u₁} {X₂ : Type u₂} {P : Type u₃}
  [NormedAddCommGroup X₀] [Lattice X₀] [IsOrderedAddMonoid X₀] [BanachLattice X₀]
  [NormedAddCommGroup X₁] [Lattice X₁] [IsOrderedAddMonoid X₁] [BanachLattice X₁]
  [NormedAddCommGroup X₂] [Lattice X₂] [IsOrderedAddMonoid X₂] [BanachLattice X₂]
  [NormedAddCommGroup P] [Lattice P] [IsOrderedAddMonoid P] [BanachLattice P]

/-- A push-out of Banach lattices with contractive lattice homomorphisms and a
universal property with control of the norm. -/
structure IsPushout (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂)
    (S₁ : VecLatHom X₁ P) (S₂ : VecLatHom X₂ P) : Prop where
  commutes : S₁.comp T₁ = S₂.comp T₂
  norm_inl_le : ‖S₁.toContinuousLinearMap‖ ≤ 1
  norm_inr_le : ‖S₂.toContinuousLinearMap‖ ≤ 1
  exists_lift : ∀ (Y : Type v) [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] (R₁ : VecLatHom X₁ Y)
    (R₂ : VecLatHom X₂ Y), R₁.comp T₁ = R₂.comp T₂ →
    ∃ R : VecLatHom P Y, R.comp S₁ = R₁ ∧ R.comp S₂ = R₂ ∧
      ‖R.toContinuousLinearMap‖ ≤ max ‖R₁.toContinuousLinearMap‖ ‖R₂.toContinuousLinearMap‖ ∧
      ∀ R' : VecLatHom P Y, R'.comp S₁ = R₁ → R'.comp S₂ = R₂ → R' = R

namespace IsPushout

variable {T₁ : VecLatHom X₀ X₁} {T₂ : VecLatHom X₀ X₂}
  {S₁ : VecLatHom X₁ P} {S₂ : VecLatHom X₂ P}

/-- Interchanging the two input lattices preserves the push-out property. -/
theorem swap (h : IsPushout.{u₀, u₁, u₂, u₃, v} T₁ T₂ S₁ S₂) :
    IsPushout.{u₀, u₂, u₁, u₃, v} T₂ T₁ S₂ S₁ := by
  refine ⟨h.commutes.symm, h.norm_inr_le, h.norm_inl_le, ?_⟩
  intro Y _ _ _ _ R₁ R₂ hR
  obtain ⟨R, h₁, h₂, hnorm, huniq⟩ := h.exists_lift Y R₂ R₁ hR.symm
  exact ⟨R, h₂, h₁, hnorm.trans_eq (max_comm _ _), fun R' h₂' h₁' ↦ huniq R' h₁' h₂'⟩

variable (h : IsPushout.{u₀, u₁, u₂, u₃, v} T₁ T₂ S₁ S₂)
  {Y : Type v} [NormedAddCommGroup Y] [Lattice Y]
  [IsOrderedAddMonoid Y] [BanachLattice Y]

include h

/-- Maps out of a push-out are determined by their restrictions to its two inputs. -/
theorem hom_ext (R R' : VecLatHom P Y)
    (h₁ : R.comp S₁ = R'.comp S₁) (h₂ : R.comp S₂ = R'.comp S₂) : R = R' := by
  obtain ⟨L, _, _, _, huniq⟩ := h.exists_lift Y (R.comp S₁) (R.comp S₂)
    (DFunLike.ext _ _ fun x ↦ congrArg R (DFunLike.congr_fun h.commutes x))
  exact (huniq R rfl rfl).trans (huniq R' h₁.symm h₂.symm).symm

/-- The norm of a map out of a push-out is controlled by its two restrictions. -/
theorem norm_hom_le (R : VecLatHom P Y) :
    ‖R.toContinuousLinearMap‖ ≤
      max ‖(R.comp S₁).toContinuousLinearMap‖ ‖(R.comp S₂).toContinuousLinearMap‖ := by
  obtain ⟨L, _, _, hnorm, huniq⟩ := h.exists_lift Y (R.comp S₁) (R.comp S₂)
    (DFunLike.ext _ _ fun x ↦ congrArg R (DFunLike.congr_fun h.commutes x))
  exact (congrArg (fun f : VecLatHom P Y ↦ ‖f.toContinuousLinearMap‖)
    (huniq R rfl rfl)).trans_le hnorm

end IsPushout

end BanachLattice
