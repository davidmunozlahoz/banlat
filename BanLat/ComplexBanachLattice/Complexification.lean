/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Complexification of a real Banach lattice

This file constructs the **complexification** of a real Banach lattice `E`, whose elements
are pairs with real and imaginary components `z.re` and `z.im`. Addition, complex scalar
multiplication and conjugation are defined in the usual way.

Disclaimer: Mathlib provides abstract real and imaginary parts for any complex star module, but it
does not provide the complexification constructed here. After equipping `Complexification E` with a
complex module structure and conjugation, we identify its self-adjoint part with `E` and show that
Mathlib's abstract real and imaginary parts agree with the concrete `re` and `im` coordinates.

Moreover, the lattice-valued modulus `modulus z ∈ E₊` is defined as the supremum of the set
`{cos(θ)·z.re + sin(θ)·z.im | θ : ℝ}`, and the norm is defined by means of
`‖z‖ = ‖modulus z‖`.

With all this structure, the complexification becomes a complete complex normed space
-/

/-- The complexification of a type `E`, represented as a pair of elements of `E`. -/
@[ext]
structure Complexification (E : Type*) where
  /-- The real part of an element of the complexification of `E`. -/
  re : E
  /-- The imaginary part of an element of the complexification of `E`. -/
  im : E

namespace Complexification

private def equivProd {E} : Complexification E ≃ E × E where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Addition on the complexification of an additive commutative group is defined componentwise. -/
instance {E : Type*} [AddCommGroup E] : AddCommGroup (Complexification E) :=
  equivProd.addCommGroup

/-- The real part of zero is zero. -/
@[simp]
theorem re_zero {E : Type*} [AddCommGroup E] : (0 : Complexification E).re = 0 := rfl

/-- The imaginary part of zero is zero. -/
@[simp]
theorem im_zero {E : Type*} [AddCommGroup E] : (0 : Complexification E).im = 0 := rfl

/-- The real part of a sum is the sum of the real parts. -/
@[simp]
theorem re_add {E : Type*} [AddCommGroup E] (z w : Complexification E) :
    (z + w).re = z.re + w.re := rfl

/-- The imaginary part of a sum is the sum of the imaginary parts. -/
@[simp]
theorem im_add {E : Type*} [AddCommGroup E] (z w : Complexification E) :
    (z + w).im = z.im + w.im := rfl

/-- The real part of a negation is the negation of the real part. -/
@[simp]
theorem re_neg {E : Type*} [AddCommGroup E] (z : Complexification E) :
    (-z).re = -z.re := rfl

/-- The imaginary part of a negation is the negation of the imaginary part. -/
@[simp]
theorem im_neg {E : Type*} [AddCommGroup E] (z : Complexification E) :
    (-z).im = -z.im := rfl

/-- The real part of a difference is the difference of the real parts. -/
@[simp]
theorem re_sub {E : Type*} [AddCommGroup E] (z w : Complexification E) :
    (z - w).re = z.re - w.re := rfl

/-- The imaginary part of a difference is the difference of the imaginary parts. -/
@[simp]
theorem im_sub {E : Type*} [AddCommGroup E] (z w : Complexification E) :
    (z - w).im = z.im - w.im := rfl

/-- Complex scalar multiplication on pairs. -/
instance {E : Type*} [AddCommGroup E] [Module ℝ E] : SMul ℂ (Complexification E) where
  smul c z :=
    ⟨c.re • z.re - c.im • z.im, c.im • z.re + c.re • z.im⟩

/-- The real part when multiplying by a complex scalar. -/
@[simp]
theorem re_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ℂ) (z : Complexification E) :
    (c • z).re = c.re • z.re - c.im • z.im := rfl

/-- The imaginary part when multiplying by a complex scalar. -/
@[simp]
theorem im_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ℂ) (z : Complexification E) :
    (c • z).im = c.im • z.re + c.re • z.im := rfl

/-- The complex vector-space structure on the complexification of a real vector space. -/
instance {E : Type*} [AddCommGroup E] [Module ℝ E] : Module ℂ (Complexification E) where
  one_smul z := by
    ext <;> simp
  mul_smul a b z := by
    ext <;> simp [sub_eq_add_neg] <;> module
  smul_zero a := by
    ext <;> simp
  smul_add a z w := by
    ext <;> simp <;> module
  add_smul a b z := by
    ext <;> simp <;> module
  zero_smul z := by
    ext <;> simp

/-- Conjugation on the complexification of an additive commutative group. -/
instance {E : Type*} [AddCommGroup E] : Star (Complexification E) where
  star z := ⟨z.re, -z.im⟩

/-- Conjugation fixes the real part. -/
@[simp]
theorem re_star {E : Type*} [AddCommGroup E] (z : Complexification E) :
    (star z).re = z.re := rfl

/-- Conjugation negates the imaginary part. -/
@[simp]
theorem im_star {E : Type*} [AddCommGroup E] (z : Complexification E) :
    (star z).im = -z.im := rfl

/-- Conjugation is an involutive additive operation on the complexification of an additive
commutative group. -/
instance {E : Type*} [AddCommGroup E] : StarAddMonoid (Complexification E) where
  star_involutive z := by
    ext <;> simp
  star_add z w := by
    ext
    · simp
    · simp
      abel

/-- Conjugation on the complexification of a real vector space satisfies
`star (c • z) = star c • star z`. -/
instance {E : Type*} [AddCommGroup E] [Module ℝ E] :
    StarModule ℂ (Complexification E) where
  star_smul c z := by
    ext
    · change c.re • z.re - c.im • z.im =
        c.re • z.re - (-c.im) • (-z.im)
      module
    · change -(c.im • z.re + c.re • z.im) =
        (-c.im) • z.re + c.re • (-z.im)
      module

section RealPart

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An element of the complexification of a real vector space is equal to
its conjugate exactly when its imaginary part is zero. -/
theorem isSelfAdjoint_iff_im_eq_zero (z : Complexification E) :
    IsSelfAdjoint z ↔ z.im = 0 := by
  rw [isSelfAdjoint_iff]
  constructor
  · intro h
    have him := congrArg Complexification.im h
    simp only [im_star] at him
    have hsum : z.im + z.im = 0 := by
      exact (congrArg (fun y ↦ y + z.im) him.symm).trans (neg_add_cancel z.im)
    have htwo : (2 : ℝ) • z.im = 0 := by
      simpa only [two_smul] using hsum
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · intro h
    ext <;> simp [h]

/-- The self-adjoint part of the complexification of a real vector space is
linearly equivalent to the original real vector space. -/
def selfAdjointEquiv :
    selfAdjoint (Complexification E) ≃ₗ[ℝ] E := by
  refine
    { toFun := fun z ↦ z.1.re
      invFun := fun x ↦ ⟨⟨x, 0⟩, (isSelfAdjoint_iff_im_eq_zero _).2 rfl⟩
      left_inv := by
        intro z
        apply Subtype.ext
        ext
        · rfl
        · exact ((isSelfAdjoint_iff_im_eq_zero z.1).1 z.2).symm
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro m x
        simpa using re_smul (m : ℂ) (x : Complexification E) }

/-- The real-linear equivalence from the self-adjoint part of the
complexification of a real vector space sends `z` to `z.re`. -/
@[simp]
theorem selfAdjointEquiv_apply (z : selfAdjoint (Complexification E)) :
    selfAdjointEquiv z = z.1.re := by
  rfl

/-- The inverse real-linear equivalence canonically embeds `x` as `(x, 0)` in
the complexification of a real vector space. -/
@[simp]
theorem coe_selfAdjointEquiv_symm_apply (x : E) :
    ((selfAdjointEquiv.symm x : selfAdjoint (Complexification E)) :
      Complexification E) = ⟨x, 0⟩ := by
  rfl

open scoped ComplexStarModule

/-- Under `selfAdjointEquiv`, the abstract real part agrees with the `re` coordinate. -/
theorem selfAdjointEquiv_realPart (z : Complexification E) :
    selfAdjointEquiv (ℜ z) = z.re := by
  rw [selfAdjointEquiv_apply]
  rw [realPart_apply_coe]
  rw [← IsScalarTower.algebraMap_smul ℂ]
  simp
  module

/-- Under `selfAdjointEquiv`, the abstract imaginary part agrees with the `im` coordinate. -/
theorem selfAdjointEquiv_imaginaryPart (z : Complexification E) :
    selfAdjointEquiv (ℑ z) = z.im := by
  rw [← neg_neg (ℑ z), ← realPart_I_smul, map_neg, selfAdjointEquiv_realPart]
  simp

end RealPart

section Norm

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [BanachLattice E]

/-- The modulus of an element of the complexification of a real Banach lattice. -/
noncomputable def modulus (z : Complexification E) : E :=
  BanachLattice.complexModulus z.re z.im

/-- The norm on the complexification of a real Banach lattice is induced by the complex modulus. -/
noncomputable instance : Norm (Complexification E) where
  norm z := ‖modulus z‖

/-- The norm on the complexification of a real Banach lattice satisfies
`‖z‖ = ‖modulus z‖`. -/
theorem norm_eq (z : Complexification E) :
    ‖z‖ = ‖modulus z‖ := rfl

private theorem normedSpaceCore : NormedSpace.Core ℂ (Complexification E) where
  norm_nonneg z := norm_nonneg (BanachLattice.complexModulus z.re z.im)
  norm_smul c z := by
    change ‖BanachLattice.complexModulus
        (c.re • z.re - c.im • z.im) (c.im • z.re + c.re • z.im)‖ =
      ‖c‖ * ‖BanachLattice.complexModulus z.re z.im‖
    rw [BanachLattice.complexModulus_linear_transform, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply, pow_two]
  norm_triangle z w := by
    change ‖BanachLattice.complexModulus (z.re + w.re) (z.im + w.im)‖ ≤
      ‖BanachLattice.complexModulus z.re z.im‖ +
        ‖BanachLattice.complexModulus w.re w.im‖
    calc
      _ ≤ ‖BanachLattice.complexModulus z.re z.im +
          BanachLattice.complexModulus w.re w.im‖ := by
        apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg (BanachLattice.complexModulus_nonneg _ _),
          abs_of_nonneg (add_nonneg (BanachLattice.complexModulus_nonneg _ _)
            (BanachLattice.complexModulus_nonneg _ _))]
        exact BanachLattice.complexModulus_add_le z.re z.im w.re w.im
      _ ≤ _ := norm_add_le _ _
  norm_eq_zero_iff z := by
    change ‖BanachLattice.complexModulus z.re z.im‖ = 0 ↔ z = 0
    rw [norm_eq_zero, BanachLattice.complexModulus_eq_zero_iff]
    constructor
    · rintro ⟨hre, him⟩
      ext <;> assumption
    · intro hz
      subst z
      exact ⟨re_zero, im_zero⟩

/-- The complexification of a real Banach lattice becomes a normed additive
commutative group. -/
noncomputable instance : NormedAddCommGroup (Complexification E) :=
  NormedAddCommGroup.ofCore normedSpaceCore

/-- The complexification of a real Banach lattice becomes a complex normed space. -/
noncomputable instance : NormedSpace ℂ (Complexification E) :=
  NormedSpace.ofCore normedSpaceCore

end Norm

section SelfAdjointBanachLattice

open scoped ComplexStarModule

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [BanachLattice E]

/-- The self-adjoint part of a complexification inherits the lattice structure of the
original real Banach lattice. -/
noncomputable instance instLatticeSelfAdjoint :
    Lattice (selfAdjoint (Complexification E)) := by
  exact selfAdjointEquiv.toEquiv.lattice

/-- Addition on the self-adjoint part of a complexification is compatible with its
transported order. -/
instance instIsOrderedAddMonoidSelfAdjoint :
    IsOrderedAddMonoid (selfAdjoint (Complexification E)) := by
  exact Function.Injective.isOrderedAddMonoid selfAdjointEquiv
    selfAdjointEquiv.map_add Iff.rfl

private theorem selfAdjointEquiv_sup
    (x y : selfAdjoint (Complexification E)) :
    selfAdjointEquiv (x ⊔ y) = selfAdjointEquiv x ⊔ selfAdjointEquiv y := by
  exact selfAdjointEquiv.apply_symm_apply _

private theorem selfAdjointEquiv_inf
    (x y : selfAdjoint (Complexification E)) :
    selfAdjointEquiv (x ⊓ y) = selfAdjointEquiv x ⊓ selfAdjointEquiv y := by
  exact selfAdjointEquiv.apply_symm_apply _

/-- The equivalence between the self-adjoint part of a complexification and the original
space preserves norms. -/
theorem norm_selfAdjointEquiv (x : selfAdjoint (Complexification E)) :
    ‖selfAdjointEquiv x‖ = ‖x‖ := by
  change ‖x.1.re‖ = ‖BanachLattice.complexModulus x.1.re x.1.im‖
  have him := (isSelfAdjoint_iff_im_eq_zero x.1).1 x.2
  rw [him, BanachLattice.complexModulus_zero_right, norm_abs_eq_norm]

/-- The self-adjoint part of the complexification of a real Banach lattice is a Banach
lattice. -/
noncomputable instance instBanachLatticeSelfAdjoint :
    BanachLattice (selfAdjoint (Complexification E)) := by
  refine
    { smul_le_smul_of_nonneg_left := by
        intro a ha x y hxy
        change selfAdjointEquiv (a • x) ≤ selfAdjointEquiv (a • y)
        change selfAdjointEquiv x ≤ selfAdjointEquiv y at hxy
        rw [map_smul, map_smul]
        exact smul_le_smul_of_nonneg_left hxy ha
      solid := by
        intro x y hxy
        rw [← norm_selfAdjointEquiv x, ← norm_selfAdjointEquiv y]
        apply norm_le_norm_of_abs_le_abs
        change selfAdjointEquiv |x| ≤ selfAdjointEquiv |y| at hxy
        simpa only [abs, selfAdjointEquiv_sup, map_neg] using hxy
      norm_smul := by
        intro r x
        rw [← norm_selfAdjointEquiv (r • x), ← norm_selfAdjointEquiv x, map_smul, norm_smul]
      toCompleteSpace := ?_ }
  exact
    (completeSpace_congr (e := selfAdjointEquiv.toEquiv)
      (AddMonoidHomClass.isometry_of_norm selfAdjointEquiv
        norm_selfAdjointEquiv).isUniformEmbedding).mpr inferInstance

/-- The self-adjoint part of a complexification is Banach-lattice isometrically
equivalent to the original real Banach lattice. -/
noncomputable def selfAdjointBanachLatEquiv :
    BanachLatEquiv (selfAdjoint (Complexification E)) E := by
  exact
    { toLinearIsometryEquiv :=
        { selfAdjointEquiv with norm_map' := norm_selfAdjointEquiv }
      map_sup' := selfAdjointEquiv_sup
      map_inf' := selfAdjointEquiv_inf }

/-- The Banach-lattice equivalence from the self-adjoint part agrees with
`selfAdjointEquiv`. -/
@[simp]
theorem selfAdjointBanachLatEquiv_apply
    (x : selfAdjoint (Complexification E)) :
    selfAdjointBanachLatEquiv x = selfAdjointEquiv x := by
  rfl

/-- The abstract complex modulus corresponds to the modulus used to norm the
complexification. -/
theorem selfAdjointBanachLatEquiv_modulus (z : Complexification E) :
    selfAdjointBanachLatEquiv (ComplexBanachLattice.modulus z) =
      Complexification.modulus z := by
  change selfAdjointBanachLatEquiv.toVecLatEquiv
      (BanachLattice.complexModulus (ℜ z) (ℑ z)) =
    BanachLattice.complexModulus z.re z.im
  rw [VecLatEquiv.map_complexModulus]
  change BanachLattice.complexModulus (selfAdjointBanachLatEquiv (ℜ z))
      (selfAdjointBanachLatEquiv (ℑ z)) =
    BanachLattice.complexModulus z.re z.im
  rw [selfAdjointBanachLatEquiv_apply, selfAdjointBanachLatEquiv_apply,
    selfAdjointEquiv_realPart, selfAdjointEquiv_imaginaryPart]

/-- The complexification of a real Banach lattice is a complex Banach lattice. -/
noncomputable instance instComplexBanachLattice :
    ComplexBanachLattice (Complexification E) := by
  refine { coe_smul := ?_, norm_modulus := ?_ }
  · intro r x
    rfl
  · intro z
    rw [← norm_selfAdjointEquiv]
    rw [← selfAdjointBanachLatEquiv_apply, selfAdjointBanachLatEquiv_modulus,
      ← norm_eq]

end SelfAdjointBanachLattice

end Complexification
