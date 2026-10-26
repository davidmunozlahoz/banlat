/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Complexification.Basic
import BanLat.ComplexBanachLattice.Hom
import BanLat.ComplexBanachLattice.Modulus.FunctionalCalculus

/-!
# Morphisms involving complexifications

This file constructs the complexification of vector lattice homomorphisms and Banach lattice
isometric equivalences. It also identifies morphisms between complex vector and Banach lattices
with the corresponding morphisms between their self-adjoint parts, and shows that every complex
Banach lattice is isometrically equivalent to the complexification of its self adjoint part.
-/

namespace Complexification

/-! ## Complexification of morphisms -/

open scoped ComplexStarModule

section Homomorphisms

variable {E F : Type*}
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [IsUniformlyCompleteVectorLattice E]
  [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [VectorLattice F] [IsUniformlyCompleteVectorLattice F]

/-- A vector lattice homomorphism between uniformly complete vector lattices
extends canonically to their complexifications. -/
noncomputable def homOfVecLatHom (T : VecLatHom E F) :
    ComplexVecLatHom (Complexification E) (Complexification F) := by
  refine
    { toLinearMap :=
        { toFun := fun z => ⟨T z.re, T z.im⟩
          map_add' := by
            intro z w
            ext <;> simp
          map_smul' := by
            intro c z
            ext <;> simp }
      map_modulus' := by
        intro z
        let w : Complexification F := ⟨T z.re, T z.im⟩
        change ⟨T ((ComplexVectorLattice.modulus z :
            selfAdjoint (Complexification E)) : Complexification E).re,
          T ((ComplexVectorLattice.modulus z :
            selfAdjoint (Complexification E)) : Complexification E).im⟩ =
          ((ComplexVectorLattice.modulus w :
            selfAdjoint (Complexification F)) : Complexification F)
        rw [coe_modulus z, coe_modulus w]
        ext
        · exact T.map_complexModulus z.re z.im
        · exact map_zero T
      }

/-- The complexification of a vector lattice homomorphism acts
coordinatewise. -/
@[simp]
theorem homOfVecLatHom_apply (T : VecLatHom E F)
    (z : Complexification E) :
    homOfVecLatHom T z = ⟨T z.re, T z.im⟩ := by
  rfl

/-- Complexification preserves the identity vector lattice homomorphism. -/
@[simp]
theorem homOfVecLatHom_id :
    homOfVecLatHom (VecLatHom.id : VecLatHom E E) =
      ComplexVecLatHom.id (Complexification E) := by
  apply ComplexVecLatHom.ext
  intro z
  rfl

/-- Complexification preserves composition of vector lattice homomorphisms. -/
@[simp]
theorem homOfVecLatHom_comp
    {G : Type*} [AddCommGroup G] [Lattice G] [IsOrderedAddMonoid G]
    [VectorLattice G] [IsUniformlyCompleteVectorLattice G]
    (S : VecLatHom F G) (T : VecLatHom E F) :
    homOfVecLatHom (S.comp T) =
      (homOfVecLatHom S).comp (homOfVecLatHom T) := by
  apply ComplexVecLatHom.ext
  intro z
  rfl

end Homomorphisms

section IsometricEquivalences

variable {E F : Type*}
  [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [BanachLattice E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [BanachLattice F]

/-- A Banach lattice isometric equivalence between two Banach lattices
extends canonically to their complexifications. -/
noncomputable def equivOfBanachLatEquiv (e : BanachLatEquiv E F) :
    ComplexBanachLatEquiv (Complexification E) (Complexification F) := by
  letI : IsUniformlyCompleteVectorLattice E :=
    isUniformlyCompleteVectorLattice_of_banachLattice E
  letI : IsUniformlyCompleteVectorLattice F :=
    isUniformlyCompleteVectorLattice_of_banachLattice F
  let T := homOfVecLatHom e.toVecLatEquiv.toVecLatHom
  let S := homOfVecLatHom e.symm.toVecLatEquiv.toVecLatHom
  let L : Complexification E ≃ₗ[ℂ] Complexification F :=
    { toFun := T
      invFun := S
      left_inv := by
        intro z
        apply Complexification.ext
        · exact e.toLinearIsometryEquiv.symm_apply_apply z.re
        · exact e.toLinearIsometryEquiv.symm_apply_apply z.im
      right_inv := by
        intro z
        apply Complexification.ext
        · exact e.toLinearIsometryEquiv.apply_symm_apply z.re
        · exact e.toLinearIsometryEquiv.apply_symm_apply z.im
      map_add' := T.map_add
      map_smul' := T.map_smul }
  exact
    { toLinearIsometryEquiv :=
        { toLinearEquiv := L
          norm_map' := by
            intro z
            rw [Complexification.norm_eq, Complexification.norm_eq]
            change ‖VectorLattice.complexModulus (e z.re) (e z.im)‖ =
              ‖VectorLattice.complexModulus z.re z.im‖
            calc
              ‖VectorLattice.complexModulus (e z.re) (e z.im)‖ =
                  ‖e (VectorLattice.complexModulus z.re z.im)‖ := by
                congr 1
                exact (e.toVecLatEquiv.map_complexModulus z.re z.im).symm
              _ = ‖VectorLattice.complexModulus z.re z.im‖ :=
                e.toLinearIsometryEquiv.norm_map _ }
      map_modulus' := T.map_modulus' }

/-- The complexification of a Banach lattice isometric equivalence acts
coordinatewise. -/
@[simp]
theorem equivOfBanachLatEquiv_apply (e : BanachLatEquiv E F)
    (z : Complexification E) :
    equivOfBanachLatEquiv e z = ⟨e z.re, e z.im⟩ := by
  rfl

/-- Complexification preserves the identity Banach lattice isometric equivalence. -/
@[simp]
theorem equivOfBanachLatEquiv_refl :
    equivOfBanachLatEquiv (BanachLatEquiv.refl E) =
      ComplexBanachLatEquiv.refl (Complexification E) := by
  apply ComplexBanachLatEquiv.ext
  intro z
  rfl

/-- Complexification preserves composition of Banach lattice isometric equivalences. -/
@[simp]
theorem equivOfBanachLatEquiv_trans
    {G : Type*} [NormedAddCommGroup G] [Lattice G] [IsOrderedAddMonoid G]
    [BanachLattice G]
    (e₁ : BanachLatEquiv E F) (e₂ : BanachLatEquiv F G) :
    equivOfBanachLatEquiv (e₁.trans e₂) =
      (equivOfBanachLatEquiv e₁).trans (equivOfBanachLatEquiv e₂) := by
  apply ComplexBanachLatEquiv.ext
  intro z
  rfl

/-- Complexification preserves inverses of Banach lattice isometric equivalences. -/
@[simp]
theorem equivOfBanachLatEquiv_symm (e : BanachLatEquiv E F) :
    equivOfBanachLatEquiv e.symm = (equivOfBanachLatEquiv e).symm := by
  apply ComplexBanachLatEquiv.ext
  intro z
  rfl

end IsometricEquivalences

end Complexification

/-! ## Extension of morphisms from self-adjoint parts -/

open scoped ComplexStarModule

namespace ComplexVecLatHom

variable {Z : Type*}
  [AddCommGroup Z] [Module ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexVectorLattice Z]
  [IsUniformlyCompleteVectorLattice (selfAdjoint Z)]

variable {W : Type*}
  [AddCommGroup W] [Module ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexVectorLattice W]
  [IsUniformlyCompleteVectorLattice (selfAdjoint W)]

/-!
The self-adjoint part has both the real scalar action inherited from the ambient complex module
and the action supplied by its vector lattice structure. The local instance below selects the
latter, for which `VecLatHom` is linear. The following lemmas relate this action to ambient scalar
multiplication using `ComplexVectorLattice.coe_smul`.
-/

/-- The real scalar action supplied by the vector lattice structure on the self-adjoint part. -/
local instance instSMulSelfAdjoint {V : Type*} [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexVectorLattice V] : SMul ℝ (selfAdjoint V) :=
  (ComplexVectorLattice.toVectorLattice (Z := V)).toModule.toSMul

omit [IsUniformlyCompleteVectorLattice (selfAdjoint Z)] in
private theorem realPart_smul_eq (c : ℂ) (z : Z) :
    ℜ (c • z) = c.re • ℜ z - c.im • ℑ z := by
  apply Subtype.ext
  simp only [realPart_smul, (selfAdjoint Z).coe_sub, selfAdjoint.val_smul,
    ComplexVectorLattice.coe_smul]

omit [IsUniformlyCompleteVectorLattice (selfAdjoint Z)] in
private theorem imaginaryPart_smul_eq (c : ℂ) (z : Z) :
    ℑ (c • z) = c.re • ℑ z + c.im • ℜ z := by
  apply Subtype.ext
  simp only [imaginaryPart_smul, (selfAdjoint Z).coe_add,
    selfAdjoint.val_smul, ComplexVectorLattice.coe_smul]

omit [IsUniformlyCompleteVectorLattice (selfAdjoint Z)]
  [IsUniformlyCompleteVectorLattice (selfAdjoint W)] in
private theorem coe_map_smul
    (T : VecLatHom (selfAdjoint Z) (selfAdjoint W)) (r : ℝ)
    (x : selfAdjoint Z) :
    ((T (r • x) : selfAdjoint W) : W) = r • (T x : W) := by
  calc
    ((T (r • x) : selfAdjoint W) : W) =
        ((r • T x : selfAdjoint W) : W) :=
      congrArg Subtype.val (T.toLinearMap.map_smul r x)
    _ = r • (T x : W) := ComplexVectorLattice.coe_smul r (T x)

/-- A vector lattice homomorphism between the self-adjoint parts extends uniquely
to a complex vector lattice homomorphism. -/
noncomputable def ofSelfAdjointVecLatHom
    (T : VecLatHom (selfAdjoint Z) (selfAdjoint W)) :
    ComplexVecLatHom Z W := by
  let L : Z →ₗ[ℂ] W :=
    { toFun := fun z ↦ (T (ℜ z) : W) + Complex.I • (T (ℑ z) : W)
      map_add' := by
        intro z w
        simp only [map_add, (selfAdjoint W).coe_add]
        module
      map_smul' := by
        intro c z
        rw [realPart_smul_eq, imaginaryPart_smul_eq]
        simp only [map_sub, map_add, (selfAdjoint W).coe_sub,
          (selfAdjoint W).coe_add]
        rw [coe_map_smul, coe_map_smul, coe_map_smul, coe_map_smul]
        match_scalars <;> apply Complex.ext <;> simp_all }
  refine { toLinearMap := L, map_modulus' := ?_ }
  intro z
  have hLcoe (x : selfAdjoint Z) : L (x : Z) = (T x : W) := by
    change (T (ℜ (x : Z)) : W) + Complex.I • (T (ℑ (x : Z)) : W) =
      (T x : W)
    simp
  rw [hLcoe]
  change ((T (ComplexVectorLattice.modulus z) : selfAdjoint W) : W) =
    ((ComplexVectorLattice.modulus (L z) : selfAdjoint W) : W)
  apply congrArg Subtype.val
  rw [ComplexVectorLattice.modulus_eq_complexModulus,
    ComplexVectorLattice.modulus_eq_complexModulus,
    T.map_complexModulus]
  congr 1
  · apply Subtype.ext
    simp [L]
  · apply Subtype.ext
    simp [L]

/-- The extension of a vector lattice homomorphism between the self-adjoint
parts acts separately on real and imaginary parts. -/
@[simp]
theorem ofSelfAdjointVecLatHom_apply
    (T : VecLatHom (selfAdjoint Z) (selfAdjoint W)) (z : Z) :
    ofSelfAdjointVecLatHom T z =
      (T (ℜ z) : W) + Complex.I • (T (ℑ z) : W) := by
  rfl

/-- Complex vector lattice homomorphisms correspond to vector lattice
homomorphisms between their self-adjoint parts. -/
noncomputable def selfAdjointEquiv :
    ComplexVecLatHom Z W ≃
      VecLatHom (selfAdjoint Z) (selfAdjoint W) := by
  exact
    { toFun := toSelfAdjointVecLatHom
      invFun := ofSelfAdjointVecLatHom
      left_inv := by
        intro T
        apply ext_selfAdjoint
        intro x
        rw [ofSelfAdjointVecLatHom_apply]
        simp
      right_inv := by
        intro T
        apply DFunLike.coe_injective
        funext x
        apply Subtype.ext
        rw [toSelfAdjointVecLatHom_apply, ofSelfAdjointVecLatHom_apply]
        simp only [selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe,
          map_zero]
        change (T x : W) + Complex.I • (0 : W) = (T x : W)
        simp }

/-- The forward direction of `selfAdjointEquiv` is restriction to the
self-adjoint parts. -/
@[simp]
theorem selfAdjointEquiv_apply (T : ComplexVecLatHom Z W) :
    selfAdjointEquiv T = T.toSelfAdjointVecLatHom := by
  rfl

/-- The inverse direction of `selfAdjointEquiv` is complex-linear extension
from the self-adjoint parts. -/
@[simp]
theorem selfAdjointEquiv_symm_apply
    (T : VecLatHom (selfAdjoint Z) (selfAdjoint W)) :
    selfAdjointEquiv.symm T = ofSelfAdjointVecLatHom T := by
  rfl


end ComplexVecLatHom

/-! ## Canonical equivalence with the complexification of the self-adjoint part -/

open scoped ComplexStarModule

namespace ComplexBanachLattice

variable (Z : Type*)
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

local instance : IsUniformlyCompleteVectorLattice (selfAdjoint Z) :=
  isUniformlyCompleteVectorLattice_of_banachLattice (selfAdjoint Z)

private theorem modulus_coe_add_I_smul_coe
    (x y : selfAdjoint Z) :
    ComplexVectorLattice.modulus ((x : Z) + Complex.I • (y : Z)) =
      VectorLattice.complexModulus x y := by
  rw [ComplexVectorLattice.modulus_eq_complexModulus]
  simp only [map_add, realPart_I_smul, imaginaryPart_I_smul,
    selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe,
    neg_zero, add_zero, zero_add]

/-- A complex Banach lattice is canonically equivalent to the complexification
of its self-adjoint part. -/
noncomputable def complexificationEquiv :
    ComplexBanachLatEquiv (Complexification (selfAdjoint Z)) Z := by
  let L : Complexification (selfAdjoint Z) →ₗ[ℂ] Z :=
    { toFun := fun z ↦ (z.re : Z) + Complex.I • (z.im : Z)
      map_add' := by
        intro z w
        simp only [Complexification.re_add, Complexification.im_add,
          (selfAdjoint Z).coe_add]
        module
      map_smul' := by
        intro c z
        rw [Complexification.re_smul, Complexification.im_smul,
          (selfAdjoint Z).coe_sub, (selfAdjoint Z).coe_add]
        simp only [ComplexVectorLattice.coe_smul]
        match_scalars <;> apply Complex.ext <;> simp_all }
  let e : Complexification (selfAdjoint Z) ≃ₗ[ℂ] Z :=
    { toFun := L
      invFun := fun z ↦ ⟨ℜ z, ℑ z⟩
      left_inv := by
        intro z
        change ⟨ℜ ((z.re : Z) + Complex.I • (z.im : Z)),
          ℑ ((z.re : Z) + Complex.I • (z.im : Z))⟩ = z
        ext <;> simp
      right_inv := realPart_add_I_smul_imaginaryPart
      map_add' := L.map_add
      map_smul' := L.map_smul }
  refine
    { toLinearIsometryEquiv :=
        { toLinearEquiv := e
          norm_map' := ?_ }
      map_modulus' := ?_ }
  · intro z
    calc
      ‖L z‖ = ‖ComplexVectorLattice.modulus (L z)‖ :=
        (norm_modulus (L z)).symm
      _ = ‖Complexification.modulus z‖ := by
        change ‖ComplexVectorLattice.modulus
          ((z.re : Z) + Complex.I • (z.im : Z))‖ = _
        rw [modulus_coe_add_I_smul_coe]
        rfl
      _ = ‖z‖ := (Complexification.norm_eq z).symm
  · intro z
    change L ((ComplexVectorLattice.modulus z : selfAdjoint
      (Complexification (selfAdjoint Z))) :
        Complexification (selfAdjoint Z)) =
      ((ComplexVectorLattice.modulus (L z) : selfAdjoint Z) : Z)
    rw [Complexification.coe_modulus]
    simp only [L]
    change ((Complexification.modulus z : selfAdjoint Z) : Z) +
      Complex.I • (0 : Z) =
      ((ComplexVectorLattice.modulus
        ((z.re : Z) + Complex.I • (z.im : Z)) :
        selfAdjoint Z) : Z)
    rw [smul_zero, add_zero]
    apply congrArg Subtype.val
    rw [modulus_coe_add_I_smul_coe]
    rfl

/-- The canonical equivalence reconstructs an element from its two coordinates. -/
@[simp]
theorem complexificationEquiv_apply
    (z : Complexification (selfAdjoint Z)) :
    complexificationEquiv Z z =
      (z.re : Z) + Complex.I • (z.im : Z) := by
  rfl

/-- The inverse canonical equivalence takes real and imaginary parts. -/
@[simp]
theorem complexificationEquiv_symm_apply (z : Z) :
    (complexificationEquiv Z).symm z = ⟨ℜ z, ℑ z⟩ := by
  rfl

end ComplexBanachLattice

namespace ComplexBanachLatEquiv

variable {Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

variable {W : Type*}
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexBanachLattice W]

/-- A Banach lattice isometric equivalence between the self-adjoint parts
extends uniquely to a complex Banach lattice isometric equivalence. -/
noncomputable def ofSelfAdjointBanachLatEquiv
    (e : BanachLatEquiv (selfAdjoint Z) (selfAdjoint W)) :
    ComplexBanachLatEquiv Z W :=
  (ComplexBanachLattice.complexificationEquiv Z).symm.trans
    ((Complexification.equivOfBanachLatEquiv e).trans
      (ComplexBanachLattice.complexificationEquiv W))

/-- The extension of a Banach lattice isometric equivalence between the
self-adjoint parts acts separately on real and imaginary parts. -/
@[simp]
theorem ofSelfAdjointBanachLatEquiv_apply
    (e : BanachLatEquiv (selfAdjoint Z) (selfAdjoint W)) (z : Z) :
    ofSelfAdjointBanachLatEquiv e z =
      (e (ℜ z) : W) + Complex.I • (e (ℑ z) : W) := by
  change ComplexBanachLattice.complexificationEquiv W
    (Complexification.equivOfBanachLatEquiv e
      ((ComplexBanachLattice.complexificationEquiv Z).symm z)) = _
  rw [ComplexBanachLattice.complexificationEquiv_symm_apply,
    Complexification.equivOfBanachLatEquiv_apply,
    ComplexBanachLattice.complexificationEquiv_apply]

/-- Complex Banach lattice isometric equivalences correspond to Banach lattice
isometric equivalences between their self-adjoint parts. -/
noncomputable def selfAdjointEquiv :
    ComplexBanachLatEquiv Z W ≃
      BanachLatEquiv (selfAdjoint Z) (selfAdjoint W) := by
  exact
    { toFun := toSelfAdjointBanachLatEquiv
      invFun := ofSelfAdjointBanachLatEquiv
      left_inv := by
        intro e
        apply ext_selfAdjoint
        intro x
        rw [ofSelfAdjointBanachLatEquiv_apply]
        simp
      right_inv := by
        intro e
        apply DFunLike.coe_injective
        funext x
        ext
        rw [toSelfAdjointBanachLatEquiv_apply,
          toSelfAdjointLinearIsometryEquiv_apply,
          ofSelfAdjointBanachLatEquiv_apply,
          selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe]
        have hzero : ((e (0 : selfAdjoint Z) : selfAdjoint W) : W) = 0 :=
          congrArg Subtype.val e.toLinearIsometryEquiv.map_zero
        rw [hzero, smul_zero, add_zero] }

/-- The forward direction of `selfAdjointEquiv` is restriction to the
self-adjoint parts. -/
@[simp]
theorem selfAdjointEquiv_apply (e : ComplexBanachLatEquiv Z W) :
    selfAdjointEquiv e = e.toSelfAdjointBanachLatEquiv := by
  rfl

/-- The inverse direction of `selfAdjointEquiv` is complex-linear extension
from the self-adjoint parts. -/
@[simp]
theorem selfAdjointEquiv_symm_apply
    (e : BanachLatEquiv (selfAdjoint Z) (selfAdjoint W)) :
    selfAdjointEquiv.symm e = ofSelfAdjointBanachLatEquiv e := by
  rfl

end ComplexBanachLatEquiv
