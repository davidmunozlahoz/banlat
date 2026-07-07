import BanLat.Normed

/-!
# AL-spaces

An **AL-space** is a Banach lattice whose norm satisfies the AL-axiom:
`‖x + y‖ = ‖x‖ + ‖y‖` for all `x, y` with `x ⊓ y = 0`.
-/

/-! ### AL-spaces -/

/-- An **AL-space** is a Banach lattice whose norm is additive on disjoint
elements: for all `x` and `y` with `x ⊓ y = 0`,
`‖x + y‖ = ‖x‖ + ‖y‖`. -/
class ALSpace (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends BanachLattice X where
  norm_add_eq_of_inf_eq_zero {x y : X} (hxy : x ⊓ y = 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

/-! #### Basic norm identities -/

/-- The norm of the positive part plus the norm of the negative part
equals the norm: `‖x⁺‖ + ‖x⁻‖ = ‖x‖`. -/
theorem norm_posPart_add_norm_negPart (x : X) :
    ‖x⁺‖ + ‖x⁻‖ = ‖x‖ := by
  rw [← norm_add_eq_of_inf_eq_zero (posPart_inf_negPart_eq_zero x), posPart_add_negPart]
  exact norm_abs_eq_norm x

open UniformSpace in
/-- The completion of a normed vector lattice whose norm is additive on disjoint elements
(the AL-norm condition) is an AL-space. -/
@[reducible]
noncomputable def completion {X : Type*} [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X]
    (hAL : ∀ x y : X, x ⊓ y = 0 → ‖x + y‖ = ‖x‖ + ‖y‖) :
    ALSpace (Completion X) where
  norm_add_eq_of_inf_eq_zero := by
    have coe_pp : ∀ x : X, ((x⁺ : X) : Completion X) = ((x : Completion X))⁺ := fun x => by
      rw [posPart_def, posPart_def, coe_sup_completion, Completion.coe_zero]
    have coe_np : ∀ x : X, ((x⁻ : X) : Completion X) = ((x : Completion X))⁻ := fun x => by
      rw [negPart_def, negPart_def, coe_sup_completion, Completion.coe_neg, Completion.coe_zero]
    have hAL' : ∀ w : X, ‖w‖ = ‖w⁺‖ + ‖w⁻‖ := fun w => by
      have h := hAL w⁺ w⁻ (posPart_inf_negPart_eq_zero w)
      rwa [posPart_add_negPart, norm_abs_eq_norm] at h
    have hParts : ∀ z : Completion X, ‖z‖ = ‖z⁺‖ + ‖z⁻‖ := by
      have hcont : Continuous fun z : Completion X => ‖z⁺‖ + ‖z⁻‖ :=
        (continuous_norm.comp continuous_posPart).add (continuous_norm.comp continuous_negPart)
      have heq : (fun z : Completion X => ‖z‖) ∘ ((↑) : X → Completion X)
          = (fun z : Completion X => ‖z⁺‖ + ‖z⁻‖) ∘ ((↑) : X → Completion X) := by
        funext x
        simp only [Function.comp_apply]
        rw [← coe_pp, ← coe_np, Completion.norm_coe, Completion.norm_coe, Completion.norm_coe]
        exact hAL' x
      exact fun z => congrFun (Completion.denseRange_coe.equalizer continuous_norm hcont heq) z
    intro a b hab
    have hpp : (a - b)⁺ = a := by rw [← sub_inf_eq_posPart, hab, sub_zero]
    have hnp : (a - b)⁻ = b := by
      rw [negPart_def, neg_sub, ← posPart_def, ← sub_inf_eq_posPart, inf_comm, hab, sub_zero]
    have habs : |a - b| = a + b := by rw [← posPart_add_negPart (a - b), hpp, hnp]
    calc ‖a + b‖ = ‖|a - b|‖ := by rw [habs]
      _ = ‖a - b‖ := norm_abs_eq_norm (a - b)
      _ = ‖(a - b)⁺‖ + ‖(a - b)⁻‖ := hParts (a - b)
      _ = ‖a‖ + ‖b‖ := by rw [hpp, hnp]

end ALSpace
