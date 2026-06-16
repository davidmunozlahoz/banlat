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

end ALSpace
