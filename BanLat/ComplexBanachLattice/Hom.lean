/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Basic
import BanLat.Operators.Hom

/-!
# Morphisms between complex vector and Banach lattices

This file defines **complex vector lattice homomorphisms** as complex-linear maps preserving the
lattice-valued modulus. Such maps are automatically continuous between complex Banach lattices.

It also defines **complex Banach lattice isometric equivalences** as complex-linear isometric
equivalences preserving the lattice-valued modulus.
-/

open scoped ComplexStarModule

/-! ## Complex vector lattice homomorphisms -/

/-- A **complex vector lattice homomorphism** is a complex-linear map preserving the
lattice-valued modulus. -/
structure ComplexVecLatHom (Z W : Type*)
    [AddCommGroup Z] [Module ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexVectorLattice Z]
    [AddCommGroup W] [Module ℂ W]
    [StarAddMonoid W] [StarModule ℂ W]
    [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
    [ComplexVectorLattice W]
    extends Z →ₗ[ℂ] W where
  map_modulus' (z : Z) :
    toLinearMap ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexVectorLattice.modulus (toLinearMap z) : selfAdjoint W) : W)

namespace ComplexVecLatHom

section Algebraic

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexVectorLattice Z]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexVectorLattice W]

/-- The canonical `FunLike` instance for complex vector lattice homomorphisms. -/
instance instFunLike : FunLike (ComplexVecLatHom Z W) Z W := by
  exact
    { coe := fun T ↦ T.toLinearMap
      coe_injective := by
        intro T S h
        cases T
        cases S
        congr
        exact LinearMap.ext (congrFun h) }

/-- Complex vector lattice homomorphisms form a class of complex-linear maps. -/
instance instLinearMapClass :
    LinearMapClass (ComplexVecLatHom Z W) ℂ Z W := by
  exact
    { map_add := fun T x y ↦ T.toLinearMap.map_add x y
      map_smulₛₗ := fun T c x ↦ T.toLinearMap.map_smul c x }

/-- Complex vector lattice homomorphisms preserve the lattice-valued modulus. -/
@[simp]
theorem map_modulus (T : ComplexVecLatHom Z W) (z : Z) :
    T ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexVectorLattice.modulus (T z) : selfAdjoint W) : W) := by
  exact T.map_modulus' z

/-- Two complex vector lattice homomorphisms are equal if they agree pointwise. -/
@[ext]
theorem ext {T S : ComplexVecLatHom Z W} (h : ∀ z, T z = S z) :
    T = S := by
  exact DFunLike.coe_injective (funext h)

/-- The underlying linear map has the same coercion to a function as the complex vector lattice
homomorphism. -/
@[simp]
theorem coe_toLinearMap (T : ComplexVecLatHom Z W) :
    ⇑T.toLinearMap = ⇑T := by
  rfl

/-- Evaluation of the underlying linear map agrees with the original homomorphism. -/
@[simp]
theorem toLinearMap_apply (T : ComplexVecLatHom Z W) (z : Z) :
    T.toLinearMap z = T z := by
  rfl

/-- A complex vector lattice homomorphism is determined by its underlying linear map. -/
theorem toLinearMap_injective :
    Function.Injective
      (ComplexVecLatHom.toLinearMap : ComplexVecLatHom Z W → Z →ₗ[ℂ] W) := by
  intro T S h
  apply ext
  intro z
  exact LinearMap.congr_fun h z

/-- Two complex vector lattice homomorphisms are equal if they agree on the self-adjoint part. -/
theorem ext_selfAdjoint {T S : ComplexVecLatHom Z W}
    (h : ∀ x : selfAdjoint Z, T (x : Z) = S (x : Z)) : T = S := by
  apply ext
  intro z
  rw [← realPart_add_I_smul_imaginaryPart z, map_add, map_add,
    map_smul, map_smul, h (ℜ z), h (ℑ z)]

/-- The identity complex vector lattice homomorphism. -/
def id (Z : Type*) [AddCommGroup Z] [Module ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexVectorLattice Z] : ComplexVecLatHom Z Z :=
  { toLinearMap := LinearMap.id
    map_modulus' := by intro z; rfl }

/-- Evaluation of the identity complex vector lattice homomorphism. -/
@[simp]
theorem id_apply (z : Z) : id Z z = z := by
  rfl

/-- The composition of two complex vector lattice homomorphisms. -/
def comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexVectorLattice V]
    (S : ComplexVecLatHom W V) (T : ComplexVecLatHom Z W) :
    ComplexVecLatHom Z V where
  toLinearMap := S.toLinearMap.comp T.toLinearMap
  map_modulus' z := by
    change S (T ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z)) =
      ((ComplexVectorLattice.modulus (S (T z)) : selfAdjoint V) : V)
    rw [T.map_modulus, S.map_modulus]

/-- Evaluation of a composition of complex vector lattice homomorphisms. -/
@[simp]
theorem comp_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexVectorLattice V]
    (S : ComplexVecLatHom W V) (T : ComplexVecLatHom Z W) (z : Z) :
    S.comp T z = S (T z) := by
  rfl

/-- Composing a complex vector lattice homomorphism with the identity on the right leaves it
unchanged. -/
@[simp]
theorem comp_id (T : ComplexVecLatHom Z W) : T.comp (id Z) = T := by
  apply ext
  intro z
  rfl

/-- Composing a complex vector lattice homomorphism with the identity on the left leaves it
unchanged. -/
@[simp]
theorem id_comp (T : ComplexVecLatHom Z W) : (id W).comp T = T := by
  apply ext
  intro z
  rfl

/-- Composition of complex vector lattice homomorphisms is associative. -/
theorem comp_assoc {V X : Type*}
    [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexVectorLattice V]
    [AddCommGroup X] [Module ℂ X]
    [StarAddMonoid X] [StarModule ℂ X]
    [Lattice (selfAdjoint X)] [IsOrderedAddMonoid (selfAdjoint X)]
    [ComplexVectorLattice X]
    (R : ComplexVecLatHom V X) (S : ComplexVecLatHom W V)
    (T : ComplexVecLatHom Z W) :
    (R.comp S).comp T = R.comp (S.comp T) := by
  apply ext
  intro z
  rfl

/-- A complex vector lattice homomorphism maps self-adjoint elements to self-adjoint elements. -/
theorem isSelfAdjoint_map (T : ComplexVecLatHom Z W) (x : selfAdjoint Z) :
    IsSelfAdjoint (T (x : Z)) := by
  have isSelfAdjoint_map_of_nonneg : ∀ (y : selfAdjoint Z), 0 ≤ y →
      IsSelfAdjoint (T (y : Z)) := by
    intro y hy
    have h := T.map_modulus (y : Z)
    rw [ComplexVectorLattice.modulus_coe, abs_of_nonneg hy] at h
    rw [h]
    exact (ComplexVectorLattice.modulus (T (y : Z))).2
  rw [show (x : Z) = ((x⁺ - x⁻ : selfAdjoint Z) : Z) by
    rw [posPart_sub_negPart]]
  rw [(selfAdjoint Z).coe_sub]
  change IsSelfAdjoint
    (T (((x⁺ : selfAdjoint Z) : Z) - ((x⁻ : selfAdjoint Z) : Z)))
  rw [map_sub]
  exact (isSelfAdjoint_map_of_nonneg x⁺ (posPart_nonneg x)).sub
    (isSelfAdjoint_map_of_nonneg x⁻ (negPart_nonneg x))

/-- A complex vector lattice homomorphism commutes with conjugation. -/
@[simp]
theorem map_star (T : ComplexVecLatHom Z W) (z : Z) :
    T (star z) = star (T z) := by
  rw [← realPart_add_I_smul_imaginaryPart z]
  rw [star_add, star_smul, map_add, map_smul]
  rw [map_add, map_smul, star_add, star_smul]
  rw [(ℜ z).property.star_eq, (ℑ z).property.star_eq]
  have hre : IsSelfAdjoint (T (ℜ z : Z)) := T.isSelfAdjoint_map (ℜ z)
  have him : IsSelfAdjoint (T (ℑ z : Z)) := T.isSelfAdjoint_map (ℑ z)
  rw [hre.star_eq, him.star_eq]

/-- Complex vector lattice homomorphisms form a class of star-preserving maps. -/
instance instStarHomClass : StarHomClass (ComplexVecLatHom Z W) Z W := by
  exact ⟨ComplexVecLatHom.map_star⟩

/-- The restriction of a complex vector lattice homomorphism to the self-adjoint part. -/
noncomputable def toSelfAdjointVecLatHom (T : ComplexVecLatHom Z W) :
    VecLatHom (selfAdjoint Z) (selfAdjoint W) := by
  let L : selfAdjoint Z →ₗ[ℝ] selfAdjoint W :=
    { toFun := fun x ↦ ⟨T (x : Z), T.isSelfAdjoint_map x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add T (x : Z) (y : Z)
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp only [ComplexVectorLattice.coe_smul]
        rw [← IsScalarTower.algebraMap_smul ℂ]
        exact map_smul T (r : ℂ) (x : Z) }
  exact VecLatHom.ofAbs L (by
    intro x
    apply Subtype.ext
    change T ((|x| : selfAdjoint Z) : Z) =
      ((|⟨T (x : Z), T.isSelfAdjoint_map x⟩| : selfAdjoint W) : W)
    rw [← ComplexVectorLattice.modulus_coe x,
      ← ComplexVectorLattice.modulus_coe ⟨T (x : Z), T.isSelfAdjoint_map x⟩]
    exact T.map_modulus (x : Z))

/-- Restriction to the self-adjoint part is evaluated by the original homomorphism. -/
@[simp]
theorem toSelfAdjointVecLatHom_apply (T : ComplexVecLatHom Z W) (x : selfAdjoint Z) :
    (T.toSelfAdjointVecLatHom x : W) = T (x : Z) := by
  rfl

/-- A complex vector lattice homomorphism commutes with real part. -/
@[simp]
theorem map_realPart (T : ComplexVecLatHom Z W) (z : Z) :
    T (ℜ z : Z) = (ℜ (T z) : W) := by
  exact _root_.map_realPart T z

/-- A complex vector lattice homomorphism commutes with imaginary part. -/
@[simp]
theorem map_imaginaryPart (T : ComplexVecLatHom Z W) (z : Z) :
    T (ℑ z : Z) = (ℑ (T z) : W) := by
  exact _root_.map_imaginaryPart T z

end Algebraic

section Normed

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexBanachLattice W]

/-- A complex vector lattice homomorphism between complex Banach lattices is continuous. -/
theorem continuous (T : ComplexVecLatHom Z W) : Continuous T := by
  have hT : Continuous T.toSelfAdjointVecLatHom :=
    Positive.continuous
      (Positive.monotone_iff.mp T.toSelfAdjointVecLatHom.monotone)
  have hre : Continuous (fun z : Z ↦ ℜ z) := by
    apply (continuous_fst.comp
      (ComplexBanachLattice.realImagEquiv (Z := Z)).continuous).congr
    intro z
    exact congrArg Prod.fst
      (ComplexBanachLattice.realImagEquiv_apply z)
  have him : Continuous (fun z : Z ↦ ℑ z) := by
    apply (continuous_snd.comp
      (ComplexBanachLattice.realImagEquiv (Z := Z)).continuous).congr
    intro z
    exact congrArg Prod.snd
      (ComplexBanachLattice.realImagEquiv_apply z)
  have hreal : Continuous (fun z : Z ↦ T (ℜ z : Z)) :=
    continuous_subtype_val.comp (hT.comp hre)
  have himaginary : Continuous (fun z : Z ↦ T (ℑ z : Z)) :=
    continuous_subtype_val.comp (hT.comp him)
  apply (hreal.add (himaginary.const_smul Complex.I)).congr
  intro z
  change T (ℜ z : Z) + Complex.I • T (ℑ z : Z) = T z
  calc
    T (ℜ z : Z) + Complex.I • T (ℑ z : Z) =
        T ((ℜ z : Z) + Complex.I • (ℑ z : Z)) := by
      rw [map_add, map_smul]
    _ = T z := congrArg T (realPart_add_I_smul_imaginaryPart z)

/-- A complex vector lattice homomorphism between complex Banach lattices as a continuous
linear map. -/
noncomputable def toContinuousLinearMap (T : ComplexVecLatHom Z W) :
    Z →L[ℂ] W :=
  { T.toLinearMap with cont := T.continuous }

/-- Evaluation as a continuous linear map agrees with the original homomorphism. -/
@[simp]
theorem toContinuousLinearMap_apply (T : ComplexVecLatHom Z W) (z : Z) :
    T.toContinuousLinearMap z = T z := by
  rfl

/-- The continuous linear map associated to a complex vector lattice homomorphism has the same
coercion to a function as the homomorphism. -/
@[simp]
theorem coe_toContinuousLinearMap (T : ComplexVecLatHom Z W) :
    ⇑T.toContinuousLinearMap = ⇑T := by
  rfl

end Normed

end ComplexVecLatHom

/-! ## Complex Banach lattice isometric equivalences -/

/-- A **complex Banach lattice isometric equivalence** is a complex-linear isometric
equivalence that preserves the lattice-valued modulus. -/
structure ComplexBanachLatEquiv (Z W : Type*)
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexBanachLattice Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [StarAddMonoid W] [StarModule ℂ W]
    [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
    [ComplexBanachLattice W]
    extends Z ≃ₗᵢ[ℂ] W where
  map_modulus' (z : Z) :
    toLinearIsometryEquiv ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexVectorLattice.modulus (toLinearIsometryEquiv z) : selfAdjoint W) : W)

namespace ComplexBanachLatEquiv

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexBanachLattice W]

/-- The canonical `EquivLike` instance for complex Banach lattice isometric equivalences. -/
instance instEquivLike : EquivLike (ComplexBanachLatEquiv Z W) Z W := by
  exact
    { coe := fun e ↦ e.toLinearIsometryEquiv
      inv := fun e ↦ e.toLinearIsometryEquiv.symm
      left_inv := fun e ↦ e.toLinearIsometryEquiv.left_inv
      right_inv := fun e ↦ e.toLinearIsometryEquiv.right_inv
      coe_injective' := by
        intro e f h _
        cases e
        cases f
        congr
        exact LinearIsometryEquiv.toLinearEquiv_injective
          (LinearEquiv.toEquiv_injective (Equiv.coe_inj.mp h)) }

/-- Complex Banach lattice isometric equivalences form a class of complex-linear isometric
equivalences. -/
instance instLinearIsometryEquivClass :
    LinearIsometryEquivClass (ComplexBanachLatEquiv Z W) ℂ Z W := by
  exact
    { map_add := fun e x y ↦ e.toLinearIsometryEquiv.map_add x y
      map_smulₛₗ := fun e c x ↦ e.toLinearIsometryEquiv.map_smul c x
      norm_map := fun e x ↦ e.toLinearIsometryEquiv.norm_map x }

/-- The underlying linear isometric equivalence has the same coercion to a function as the complex
Banach lattice isometric equivalence. -/
@[simp]
theorem coe_toLinearIsometryEquiv (e : ComplexBanachLatEquiv Z W) :
    ⇑e.toLinearIsometryEquiv = ⇑e := by
  rfl

/-- Evaluation of the underlying linear isometric equivalence agrees with the original
equivalence. -/
@[simp]
theorem toLinearIsometryEquiv_apply (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e.toLinearIsometryEquiv z = e z := by
  rfl

/-- The complex vector lattice homomorphism underlying an isometric equivalence. -/
def toComplexVecLatHom (e : ComplexBanachLatEquiv Z W) :
    ComplexVecLatHom Z W where
  toLinearMap := e.toLinearIsometryEquiv.toLinearEquiv.toLinearMap
  map_modulus' := e.map_modulus'

/-- The underlying complex vector lattice homomorphism has the expected value. -/
@[simp]
theorem toComplexVecLatHom_apply (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e.toComplexVecLatHom z = e z := by
  rfl

/-- The underlying complex vector lattice homomorphism has the same coercion to a function as the
isometric equivalence. -/
@[simp]
theorem coe_toComplexVecLatHom (e : ComplexBanachLatEquiv Z W) :
    ⇑e.toComplexVecLatHom = ⇑e := by
  rfl

/-- A complex Banach lattice isometric equivalence as a continuous linear equivalence. -/
noncomputable def toContinuousLinearEquiv (e : ComplexBanachLatEquiv Z W) :
    Z ≃L[ℂ] W :=
  e.toLinearIsometryEquiv.toContinuousLinearEquiv

/-- Evaluation as a continuous linear equivalence agrees with the original evaluation. -/
@[simp]
theorem toContinuousLinearEquiv_apply (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e.toContinuousLinearEquiv z = e z := by
  rfl

/-- The associated continuous linear equivalence has the same coercion to a function as the
complex Banach lattice isometric equivalence. -/
@[simp]
theorem coe_toContinuousLinearEquiv (e : ComplexBanachLatEquiv Z W) :
    ⇑e.toContinuousLinearEquiv = ⇑e := by
  rfl

/-- Complex Banach lattice isometric equivalences preserve the lattice-valued modulus. -/
@[simp]
theorem map_modulus (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexVectorLattice.modulus (e z) : selfAdjoint W) : W) := by
  exact e.map_modulus' z

/-- Two complex Banach lattice isometric equivalences are equal if they agree pointwise. -/
@[ext]
theorem ext {e f : ComplexBanachLatEquiv Z W} (h : ∀ z, e z = f z) :
    e = f := by
  exact DFunLike.coe_injective (funext h)

/-- A complex Banach lattice isometric equivalence is determined by its underlying linear
isometric equivalence. -/
theorem toLinearIsometryEquiv_injective :
    Function.Injective
      (ComplexBanachLatEquiv.toLinearIsometryEquiv :
        ComplexBanachLatEquiv Z W → Z ≃ₗᵢ[ℂ] W) := by
  intro e f h
  apply ext
  intro z
  exact DFunLike.congr_fun h z

/-- Two complex Banach lattice isometric equivalences are equal if they agree on the
self-adjoint part. -/
theorem ext_selfAdjoint {e f : ComplexBanachLatEquiv Z W}
    (h : ∀ x : selfAdjoint Z, e (x : Z) = f (x : Z)) : e = f := by
  apply ext
  intro z
  rw [← realPart_add_I_smul_imaginaryPart z, map_add, map_add,
    map_smul, map_smul, h (ℜ z), h (ℑ z)]

/-- The identity complex Banach lattice isometric equivalence. -/
def refl (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexBanachLattice Z] : ComplexBanachLatEquiv Z Z where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ Z
  map_modulus' _ := rfl

/-- Evaluation of the identity complex Banach lattice isometric equivalence. -/
@[simp]
theorem refl_apply (z : Z) : refl Z z = z := by
  rfl

/-- The inverse of a complex Banach lattice isometric equivalence. -/
def symm (e : ComplexBanachLatEquiv Z W) : ComplexBanachLatEquiv W Z := by
  exact
    { toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
      map_modulus' := by
        intro w
        apply e.toLinearIsometryEquiv.injective
        rw [e.toLinearIsometryEquiv.apply_symm_apply]
        symm
        have h := e.map_modulus' (e.toLinearIsometryEquiv.symm w)
        rw [e.toLinearIsometryEquiv.apply_symm_apply] at h
        exact h }

/-- Applying a complex Banach lattice isometric equivalence after its inverse is the identity. -/
@[simp]
theorem apply_symm_apply (e : ComplexBanachLatEquiv Z W) (w : W) :
    e (e.symm w) = w := by
  exact e.toLinearIsometryEquiv.apply_symm_apply w

/-- Applying the inverse of a complex Banach lattice isometric equivalence after the equivalence
is the identity. -/
@[simp]
theorem symm_apply_apply (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e.symm (e z) = z := by
  exact e.toLinearIsometryEquiv.symm_apply_apply z

/-- The composition of two complex Banach lattice isometric equivalences. -/
def trans {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    (e₁ : ComplexBanachLatEquiv Z W) (e₂ : ComplexBanachLatEquiv W V) :
    ComplexBanachLatEquiv Z V where
  toLinearIsometryEquiv :=
    e₁.toLinearIsometryEquiv.trans e₂.toLinearIsometryEquiv
  map_modulus' z := by
    change e₂ (e₁ ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z)) =
      ((ComplexVectorLattice.modulus (e₂ (e₁ z)) : selfAdjoint V) : V)
    rw [e₁.map_modulus, e₂.map_modulus]

/-- Evaluation of a composition of complex Banach lattice isometric equivalences. -/
@[simp]
theorem trans_apply {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    (e₁ : ComplexBanachLatEquiv Z W) (e₂ : ComplexBanachLatEquiv W V) (z : Z) :
    e₁.trans e₂ z = e₂ (e₁ z) := by
  rfl

/-- The inverse of a composition is the reverse composition of the inverses. -/
theorem symm_trans {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    (e₁ : ComplexBanachLatEquiv Z W) (e₂ : ComplexBanachLatEquiv W V) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := by
  apply ext
  intro z
  rfl

/-- Taking the inverse twice recovers the original complex Banach lattice isometric
equivalence. -/
@[simp]
theorem symm_symm (e : ComplexBanachLatEquiv Z W) : e.symm.symm = e := by
  apply ext
  intro z
  rfl

/-- The inverse of the identity complex Banach lattice isometric equivalence is the identity. -/
@[simp]
theorem refl_symm : (refl Z).symm = refl Z := by
  apply ext
  intro z
  rfl

/-- Composing a complex Banach lattice isometric equivalence with its inverse on the right gives
the identity. -/
@[simp]
theorem self_trans_symm (e : ComplexBanachLatEquiv Z W) :
    e.trans e.symm = refl Z := by
  apply ext
  intro z
  exact e.symm_apply_apply z

/-- Composing the inverse of a complex Banach lattice isometric equivalence with the equivalence
gives the identity. -/
@[simp]
theorem symm_trans_self (e : ComplexBanachLatEquiv Z W) :
    e.symm.trans e = refl W := by
  apply ext
  intro w
  exact e.apply_symm_apply w

/-- Composing a complex Banach lattice isometric equivalence with the identity on the right leaves
it unchanged. -/
@[simp]
theorem trans_refl (e : ComplexBanachLatEquiv Z W) : e.trans (refl W) = e := by
  apply ext
  intro z
  rfl

/-- Composing the identity with a complex Banach lattice isometric equivalence leaves it
unchanged. -/
@[simp]
theorem refl_trans (e : ComplexBanachLatEquiv Z W) : (refl Z).trans e = e := by
  apply ext
  intro z
  rfl

/-- Composition of complex Banach lattice isometric equivalences is associative. -/
theorem trans_assoc {V X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [StarAddMonoid X] [StarModule ℂ X]
    [Lattice (selfAdjoint X)] [IsOrderedAddMonoid (selfAdjoint X)]
    [ComplexBanachLattice X]
    (e₁ : ComplexBanachLatEquiv Z W) (e₂ : ComplexBanachLatEquiv W V)
    (e₃ : ComplexBanachLatEquiv V X) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := by
  apply ext
  intro z
  rfl

/-- A complex Banach lattice isometric equivalence maps self-adjoint elements to self-adjoint
elements. -/
theorem isSelfAdjoint_map (e : ComplexBanachLatEquiv Z W) (x : selfAdjoint Z) :
    IsSelfAdjoint (e (x : Z)) := by
  exact e.toComplexVecLatHom.isSelfAdjoint_map x

/-- A complex Banach lattice isometric equivalence commutes with conjugation. -/
@[simp]
theorem map_star (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e (star z) = star (e z) := by
  exact e.toComplexVecLatHom.map_star z

/-- Complex Banach lattice isometric equivalences form a class of star-preserving maps. -/
instance instStarHomClass : StarHomClass (ComplexBanachLatEquiv Z W) Z W := by
  exact ⟨ComplexBanachLatEquiv.map_star⟩

/-- The restriction of a complex Banach lattice isometric equivalence to self-adjoint parts as a
real-linear isometric equivalence. -/
noncomputable def toSelfAdjointLinearIsometryEquiv (e : ComplexBanachLatEquiv Z W) :
    selfAdjoint Z ≃ₗᵢ[ℝ] selfAdjoint W := by
  exact
    { toFun := fun x ↦ ⟨e (x : Z), e.isSelfAdjoint_map x⟩
      invFun := fun y ↦ ⟨e.symm (y : W), e.symm.isSelfAdjoint_map y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply (x : Z)
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply (y : W)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add e (x : Z) (y : Z)
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp only [ComplexVectorLattice.coe_smul]
        rw [← IsScalarTower.algebraMap_smul ℂ]
        exact map_smul e (r : ℂ) (x : Z)
      norm_map' := fun x ↦ norm_map e (x : Z) }

/-- Restriction to the self-adjoint part is evaluated by the original equivalence. -/
@[simp]
theorem toSelfAdjointLinearIsometryEquiv_apply (e : ComplexBanachLatEquiv Z W)
    (x : selfAdjoint Z) :
    (e.toSelfAdjointLinearIsometryEquiv x : W) = e (x : Z) := by
  rfl

/-- A complex Banach lattice isometric equivalence commutes with real part. -/
@[simp]
theorem map_realPart (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e (ℜ z : Z) = (ℜ (e z) : W) := by
  exact _root_.map_realPart e z

/-- A complex Banach lattice isometric equivalence commutes with imaginary part. -/
@[simp]
theorem map_imaginaryPart (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e (ℑ z : Z) = (ℑ (e z) : W) := by
  exact _root_.map_imaginaryPart e z

/-- The restriction of a complex Banach lattice isometric equivalence to the self-adjoint parts
is a Banach lattice isometric equivalence. -/
noncomputable def toSelfAdjointBanachLatEquiv (e : ComplexBanachLatEquiv Z W) :
    BanachLatEquiv (selfAdjoint Z) (selfAdjoint W) := by
  let T := e.toSelfAdjointLinearIsometryEquiv
  let V := e.toComplexVecLatHom.toSelfAdjointVecLatHom
  exact
    { toLinearIsometryEquiv := T
      map_sup' := V.map_sup'
      map_inf' := V.map_inf' }

/-- The Banach lattice equivalence on self-adjoint parts has the expected underlying real-linear
isometric equivalence. -/
@[simp]
theorem toSelfAdjointBanachLatEquiv_apply (e : ComplexBanachLatEquiv Z W)
    (x : selfAdjoint Z) :
    e.toSelfAdjointBanachLatEquiv x = e.toSelfAdjointLinearIsometryEquiv x := by
  rfl

end ComplexBanachLatEquiv
