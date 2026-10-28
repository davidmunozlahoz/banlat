/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Operators.Hom
import BanLat.ComplexBanachLattice.Modulus.Basic

/-!
# Complexification of a real vector lattice

This file constructs the **complexification** of a real vector lattice `E`, whose elements are
pairs with real and imaginary components `z.re` and `z.im`. Addition, complex scalar multiplication
and conjugation are defined in the usual way.

When `E` is uniformly complete, the lattice-valued modulus `modulus z ∈ E₊` is defined as the
supremum of the set `{cos(θ)·z.re + sin(θ)·z.im | θ : ℝ}`. This makes its complexification a
complex vector lattice.

When `E` is a Banach lattice, the norm is defined by `‖z‖ = ‖modulus z‖`, and its complexification
becomes a complex Banach lattice.

*Disclaimer:* Mathlib provides abstract real and imaginary parts for any complex star module, but it
does not provide the complexification constructed here. After equipping `Complexification E` with a
complex module structure and conjugation, we identify its self-adjoint part with `E` and show that
Mathlib's abstract real and imaginary parts agree with the concrete `re` and `im` coordinates.
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

section Modulus

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [IsUniformlyCompleteVectorLattice E]

/-- The modulus of an element of the complexification of a uniformly complete real vector
lattice. -/
noncomputable def modulus (z : Complexification E) : E :=
  VectorLattice.complexModulus z.re z.im

end Modulus

section Norm

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [BanachLattice E]

local instance : IsUniformlyCompleteVectorLattice E :=
  isUniformlyCompleteVectorLattice_of_banachLattice E

/-- The norm on the complexification of a real Banach lattice is induced by the complex modulus. -/
noncomputable instance : Norm (Complexification E) where
  norm z := ‖modulus z‖

/-- The norm on the complexification of a real Banach lattice satisfies
`‖z‖ = ‖modulus z‖`. -/
theorem norm_eq (z : Complexification E) :
    ‖z‖ = ‖modulus z‖ := rfl

private theorem normedSpaceCore : NormedSpace.Core ℂ (Complexification E) where
  norm_nonneg z := norm_nonneg (VectorLattice.complexModulus z.re z.im)
  norm_smul c z := by
    change ‖VectorLattice.complexModulus
        (c.re • z.re - c.im • z.im) (c.im • z.re + c.re • z.im)‖ =
      ‖c‖ * ‖VectorLattice.complexModulus z.re z.im‖
    rw [VectorLattice.complexModulus_linear_transform, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply, pow_two]
  norm_triangle z w := by
    change ‖VectorLattice.complexModulus (z.re + w.re) (z.im + w.im)‖ ≤
      ‖VectorLattice.complexModulus z.re z.im‖ +
        ‖VectorLattice.complexModulus w.re w.im‖
    calc
      _ ≤ ‖VectorLattice.complexModulus z.re z.im +
          VectorLattice.complexModulus w.re w.im‖ := by
        apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg (VectorLattice.complexModulus_nonneg _ _),
          abs_of_nonneg (add_nonneg (VectorLattice.complexModulus_nonneg _ _)
            (VectorLattice.complexModulus_nonneg _ _))]
        exact VectorLattice.complexModulus_add_le z.re z.im w.re w.im
      _ ≤ _ := norm_add_le _ _
  norm_eq_zero_iff z := by
    change ‖VectorLattice.complexModulus z.re z.im‖ = 0 ↔ z = 0
    rw [norm_eq_zero, VectorLattice.complexModulus_eq_zero_iff]
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

section SelfAdjointVectorLattice

open scoped ComplexStarModule

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]

/-- The self-adjoint part of a complexification inherits the lattice structure of the
original real vector lattice. -/
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

end SelfAdjointVectorLattice

section ComplexVectorLatticeStructure

open scoped ComplexStarModule

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [IsUniformlyCompleteVectorLattice E]

/-- The complexification of a uniformly complete real vector lattice is a complex vector
lattice. -/
noncomputable instance instComplexVectorLattice :
    ComplexVectorLattice (Complexification E) := by
  refine
    { smul_le_smul_of_nonneg_left := ?_
      coe_smul := ?_
      exists_isLUB_rotationRange := ?_ }
  · intro a ha x y hxy
    change selfAdjointEquiv (a • x) ≤ selfAdjointEquiv (a • y)
    change selfAdjointEquiv x ≤ selfAdjointEquiv y at hxy
    rw [map_smul, map_smul]
    exact smul_le_smul_of_nonneg_left hxy ha
  · intro r x
    rfl
  · intro x y
    let u := selfAdjointEquiv.symm
      (VectorLattice.complexModulus (selfAdjointEquiv x) (selfAdjointEquiv y))
    refine ⟨u, ?_⟩
    constructor
    · rintro _ ⟨θ, rfl⟩
      change selfAdjointEquiv (Real.cos θ • x + Real.sin θ • y) ≤
        selfAdjointEquiv u
      rw [map_add, map_smul, map_smul, LinearEquiv.apply_symm_apply]
      exact (VectorLattice.complexModulus_isLUB
        (selfAdjointEquiv x) (selfAdjointEquiv y)).1 ⟨θ, rfl⟩
    · intro v hv
      change selfAdjointEquiv u ≤ selfAdjointEquiv v
      rw [LinearEquiv.apply_symm_apply]
      apply (VectorLattice.complexModulus_isLUB
        (selfAdjointEquiv x) (selfAdjointEquiv y)).2
      rintro _ ⟨θ, rfl⟩
      have h := hv ⟨θ, rfl⟩
      change selfAdjointEquiv (Real.cos θ • x + Real.sin θ • y) ≤
        selfAdjointEquiv v at h
      rw [map_add, map_smul, map_smul] at h
      exact h

private theorem selfAdjointEquiv_modulus (z : Complexification E) :
    selfAdjointEquiv |z|_ℂ = Complexification.modulus z := by
  symm
  apply (VectorLattice.complexModulus_isLUB z.re z.im).unique
  constructor
  · rintro _ ⟨θ, rfl⟩
    have h := (ComplexVectorLattice.modulus_isLUB z).1 ⟨θ, rfl⟩
    change selfAdjointEquiv (Real.cos θ • ℜ z + Real.sin θ • ℑ z) ≤
      selfAdjointEquiv (ComplexVectorLattice.modulus z) at h
    rw [map_add, map_smul, map_smul, selfAdjointEquiv_realPart,
      selfAdjointEquiv_imaginaryPart] at h
    exact h
  · intro u hu
    have h : ComplexVectorLattice.modulus z ≤ selfAdjointEquiv.symm u := by
      apply (ComplexVectorLattice.modulus_isLUB z).2
      rintro _ ⟨θ, rfl⟩
      change selfAdjointEquiv (Real.cos θ • ℜ z + Real.sin θ • ℑ z) ≤ u
      rw [map_add, map_smul, map_smul, selfAdjointEquiv_realPart,
        selfAdjointEquiv_imaginaryPart]
      exact hu ⟨θ, rfl⟩
    change selfAdjointEquiv (ComplexVectorLattice.modulus z) ≤ u
    change selfAdjointEquiv (ComplexVectorLattice.modulus z) ≤
      selfAdjointEquiv (selfAdjointEquiv.symm u) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h

/-- The abstract lattice-valued modulus, viewed in the ambient complexification, has the
concrete modulus as its real coordinate and zero imaginary coordinate. -/
@[simp]
theorem coe_modulus (z : Complexification E) :
    (|z|_ℂ : Complexification E) = ⟨Complexification.modulus z, 0⟩ := by
  ext
  · exact selfAdjointEquiv_modulus z
  · exact (isSelfAdjoint_iff_im_eq_zero _).mp
      (ComplexVectorLattice.modulus z).property

end ComplexVectorLatticeStructure

section SelfAdjointBanachLattice

open scoped ComplexStarModule

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [BanachLattice E]

local instance : IsUniformlyCompleteVectorLattice E :=
  isUniformlyCompleteVectorLattice_of_banachLattice E

/-- The equivalence between the self-adjoint part of a complexification and the original
space preserves norms. -/
theorem norm_selfAdjointEquiv (x : selfAdjoint (Complexification E)) :
    ‖selfAdjointEquiv x‖ = ‖x‖ := by
  change ‖x.1.re‖ = ‖VectorLattice.complexModulus x.1.re x.1.im‖
  have him := (isSelfAdjoint_iff_im_eq_zero x.1).1 x.2
  rw [him, VectorLattice.complexModulus_zero_right, norm_abs_eq_norm]

/-- The complexification of a real Banach lattice becomes a **complex Banach lattice.** -/
noncomputable instance instComplexBanachLattice :
    ComplexBanachLattice (Complexification E) := by
  refine
    { solid := ?_
      norm_smul := ?_
      toCompleteSpace := ?_
      norm_modulus := ?_ }
  · intro x y hxy
    rw [← norm_selfAdjointEquiv x, ← norm_selfAdjointEquiv y]
    apply norm_le_norm_of_abs_le_abs
    change selfAdjointEquiv |x| ≤ selfAdjointEquiv |y| at hxy
    simpa only [abs, selfAdjointEquiv_sup, map_neg] using hxy
  · intro r x
    rw [← norm_selfAdjointEquiv (r • x), ← norm_selfAdjointEquiv x,
      map_smul, norm_smul]
  · exact
      (completeSpace_congr (e := selfAdjointEquiv.toEquiv)
        (AddMonoidHomClass.isometry_of_norm selfAdjointEquiv
          norm_selfAdjointEquiv).isUniformEmbedding).mpr inferInstance
  · intro z
    rw [← norm_selfAdjointEquiv]
    have h := congrArg Complexification.re (coe_modulus z)
    change selfAdjointEquiv (ComplexVectorLattice.modulus z) =
      Complexification.modulus z at h
    rw [h]
    exact (norm_eq z).symm

/-- The self-adjoint part of a complexification is Banach lattice isometrically
equivalent to the original real Banach lattice. -/
noncomputable def selfAdjointBanachLatEquiv :
    BanachLatEquiv (selfAdjoint (Complexification E)) E := by
  exact
    { toLinearIsometryEquiv :=
        { selfAdjointEquiv with norm_map' := norm_selfAdjointEquiv }
      map_sup' := selfAdjointEquiv_sup
      map_inf' := selfAdjointEquiv_inf }

/-- The Banach lattice equivalence from the self-adjoint part agrees with
`selfAdjointEquiv`. -/
@[simp]
theorem selfAdjointBanachLatEquiv_apply
    (x : selfAdjoint (Complexification E)) :
    selfAdjointBanachLatEquiv x = selfAdjointEquiv x := by
  rfl

/-- The abstract complex modulus corresponds to the modulus used to norm the
complexification. -/
theorem selfAdjointBanachLatEquiv_modulus (z : Complexification E) :
    selfAdjointBanachLatEquiv |z|_ℂ = Complexification.modulus z := by
  rw [selfAdjointBanachLatEquiv_apply, selfAdjointEquiv_modulus]

end SelfAdjointBanachLattice

end Complexification
