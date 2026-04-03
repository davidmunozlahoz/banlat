import BanLat.Basic
import Mathlib.Algebra.Order.Module.Basic

/-!
# Morphisms of vector lattices

This file defines `VecLatHom`, the type of vector lattice homomorphisms — maps that are
simultaneously real-linear and lattice homomorphisms. It also defines `IsVecLatHom`, the
proposition-valued predicate characterising such maps, and `VecLatEquiv`, the type of
vector lattice isomorphisms. Key results include the characterisation of vector lattice
homomorphisms by their behaviour on absolute values (`of_abs`) and the fact that every
vector lattice homomorphism is monotone.
-/

/-- A vector lattice homomorphism from `X` to `Y`: a real-linear map that also preserves
`⊔` and `⊓`. -/
structure VecLatHom (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y] extends X →ₗ[ℝ] Y, LatticeHom X Y

variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

/-- Predicate form of `VecLatHom`: a map is a vector lattice homomorphism if it is linear
and preserves `⊔` and `⊓`. -/
structure IsVecLatHom (f : X → Y) extends IsLinearMap ℝ f where
  map_sup' : ∀ x y : X, f (x ⊔ y) = (f x) ⊔ (f y)
  map_inf' : ∀ x y : X, f (x ⊓ y) = (f x) ⊓ (f y)

namespace VecLatHom

/-- The canonical `FunLike` instance, making `VecLatHom X Y` a type of functions `X → Y`. -/
instance instFunLike : FunLike (VecLatHom X Y) X Y where
  coe f := f.toFun
  coe_injective' f g h := by
    dsimp at h
    cases f
    cases g
    congr
    exact LinearMap.ext_iff.mpr (congrFun h)

/-- Every `VecLatHom` satisfies the `IsVecLatHom` predicate. -/
theorem isVecLatHom (f : VecLatHom X Y) : IsVecLatHom f where
  map_add := f.toLinearMap.map_add
  map_smul := f.toLinearMap.map_smul
  map_sup' := f.toLatticeHom.map_sup'
  map_inf' := f.toLatticeHom.map_inf'

/-- Construct a `VecLatHom` from a proof that a function satisfies `IsVecLatHom`. -/
def of_isVecLatHom (f : X → Y) (h : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := h.map_add
  map_smul' := h.map_smul
  map_sup' := h.map_sup'
  map_inf' := h.map_inf'

/-- `VecLatHom X Y` is a `LatticeHomClass`. -/
instance instLatticeHomClass : LatticeHomClass (VecLatHom X Y) X Y where
  map_inf := by
    intro f a b
    exact f.toLatticeHom.map_inf' a b
  map_sup := by
    intro f a b
    exact f.toLatticeHom.map_sup' a b

/-- `VecLatHom X Y` is a `LinearMapClass`. -/
instance instLinearMapClass : LinearMapClass (VecLatHom X Y) ℝ X Y where
  map_add := by
    intro f a b
    exact f.toLinearMap.map_add a b
  map_smulₛₗ := by
    intro f c x
    simp
    exact f.toLinearMap.map_smul c x

/-- The underlying function of a `VecLatHom` equals its coercion to `X → Y`. -/
@[simp]
theorem toFun_eq_coe {f : VecLatHom X Y} : f.toFun = (f : X → Y) := rfl

/-- A vector lattice homomorphism preserves absolute values. -/
theorem map_abs (f : VecLatHom X Y) (x : X) : f |x| = |f x| := by
  rw [abs, abs, map_sup, map_neg]

/-- Every vector lattice homomorphism is monotone. -/
theorem monotone (f : VecLatHom X Y) : Monotone f := by
  intro x y hxy
  have : x ⊔ y = y := by simp [hxy]
  rw [← sup_eq_right, ← map_sup f x y, this]

/-- A vector lattice homomorphism maps nonneg elements to nonneg elements. -/
theorem map_nonneg (f : VecLatHom X Y) {x : X} (hx : 0 ≤ x) : 0 ≤ f x := by
  have h := f.monotone hx; rwa [map_zero] at h

/-- A vector lattice homomorphism preserves positive parts: `f x⁺ = (f x)⁺`. -/
theorem map_posPart (f : VecLatHom X Y) (x : X) : f x⁺ = (f x)⁺ := by
  rw [posPart_def, map_sup, map_zero, posPart_def]

/-- A vector lattice homomorphism preserves negative parts: `f x⁻ = (f x)⁻`. -/
theorem map_negPart (f : VecLatHom X Y) (x : X) : f x⁻ = (f x)⁻ := by
  rw [negPart_def, map_sup, map_neg, map_zero, negPart_def]

/-- A vector lattice homomorphism preserves disjointness: `x ⊓ y = 0 → f x ⊓ f y = 0`. -/
theorem map_disjoint (f : VecLatHom X Y) {x y : X} (h : x ⊓ y = 0) : f x ⊓ f y = 0 := by
  rw [← map_inf, h, map_zero]

/-- The identity vector lattice homomorphism. -/
def id : VecLatHom X X :=
  { LinearMap.id with
    map_sup' := fun _ _ => rfl
    map_inf' := fun _ _ => rfl }

/-- Construct a `VecLatHom` from a linear map that preserves absolute values. -/
def of_abs (f : X →ₗ[ℝ] Y) (abs : ∀ x : X, f |x| = |f x|) : VecLatHom X Y :=
  { f with
    map_sup' := fun a b => by
      change f (a ⊔ b) = f a ⊔ f b
      rw [sup_eq_half_smul_add_add_abs_sub' ℝ, map_smul, map_add, map_add,
          abs (b - a), map_sub, ← sup_eq_half_smul_add_add_abs_sub' ℝ]
    map_inf' := fun a b => by
      change f (a ⊓ b) = f a ⊓ f b
      rw [inf_eq_half_smul_add_sub_abs_sub' ℝ, map_smul, map_sub, map_add,
          abs (b - a), map_sub, ← inf_eq_half_smul_add_sub_abs_sub' ℝ] }

/-- Composition of two vector lattice homomorphisms. -/
def comp {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z] (g : VecLatHom Y Z) (f : VecLatHom X Y) :
  VecLatHom X Z :=
  {LinearMap.comp g.toLinearMap f.toLinearMap with
    map_sup' := by
      intro x y
      simp
      change g ( f (x ⊔ y) ) = (g (f x)) ⊔ (g (f y))
      simp only [map_sup]
    map_inf' := by
      intro x y
      simp
      change g ( f (x ⊓ y) ) = (g (f x)) ⊓ (g (f y))
      simp only [map_inf]
  }

/-- Evaluation of a composed `VecLatHom`. -/
theorem comp_apply {Z : Type*} [AddCommGroup Z] [Lattice Z]
  [IsOrderedAddMonoid Z] [VectorLattice Z] (g : VecLatHom Y Z)
  (f : VecLatHom X Y) (x : X) : g.comp f x = g (f x) := by
    rw [comp]
    change (LinearMap.comp g.toLinearMap f.toLinearMap) x = g (f x)
    simp
    rfl

/-- The inverse of a bijective vector lattice homomorphism is again a vector lattice
homomorphism. -/
noncomputable def symm (f : VecLatHom X Y) (h : Function.Bijective f) : VecLatHom Y X :=
  {(LinearEquiv.ofBijective f.toLinearMap h).symm with
    map_sup' := by
      intro a b
      change
        (LinearEquiv.ofBijective f.toLinearMap h).symm (a ⊔ b) =
        (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊔
        (LinearEquiv.ofBijective f.toLinearMap h).symm b
      rw [LinearEquiv.symm_apply_eq]
      change
        a ⊔ b = f ( (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊔
        (LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [map_sup]
      change
        a ⊔ b = LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm a) ⊔
                LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    map_inf' := by
      intro a b
      change
        (LinearEquiv.ofBijective f.toLinearMap h).symm (a ⊓ b) =
        (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊓
        (LinearEquiv.ofBijective f.toLinearMap h).symm b
      rw [LinearEquiv.symm_apply_eq]
      change
        a ⊓ b = f ( (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊓
        (LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [map_inf]
      change
        a ⊓ b = LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm a) ⊓
                LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  }

/-- The inverse bijection from `symm`: `(f.symm h) y = x ↔ y = f x`. -/
theorem symm_apply (f : VecLatHom X Y) (h : Function.Bijective f)
  (x : X) (y : Y) : (f.symm h) y = x ↔ y = f x := by
    let lineq := LinearEquiv.ofBijective f.toLinearMap h
    change lineq.symm y = x ↔ y = f x
    apply LinearEquiv.symm_apply_eq

end VecLatHom

namespace IsVecLatHom

/-- Bundle an `IsVecLatHom` proof into a `VecLatHom`. -/
def mk' (f : X → Y) (vlh : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := vlh.map_add
  map_smul' := vlh.map_smul
  map_sup' := vlh.map_sup'
  map_inf' := vlh.map_inf'

/-- Evaluation of `mk'` agrees with the underlying function. -/
@[simp]
theorem mk'_apply {f : X → Y} (vlh : IsVecLatHom f) (x : X) :
    mk' f vlh x = f x := rfl

/-- A linear map that preserves absolute values satisfies `IsVecLatHom`. -/
theorem of_abs {f : X → Y} (lin : IsLinearMap ℝ f) (abs : ∀ x : X, f |x|
  = |f x|) : IsVecLatHom f :=
  VecLatHom.isVecLatHom (VecLatHom.of_abs (IsLinearMap.mk' f lin) abs)

/-- A positive linear map that preserves disjointness is a vector lattice homomorphism. -/
theorem of_disjoint {f : X → Y} (lin : IsLinearMap ℝ f)
    (pos : ∀ x : X, 0 ≤ x → 0 ≤ f x)
    (disj : ∀ x y : X, x ⊓ y = 0 → f x ⊓ f y = 0) : IsVecLatHom f := by
  have fNeg : ∀ x : X, f (-x) = -f x := fun x => by
    have h := lin.map_smul (-1 : ℝ) x; rwa [neg_one_smul, neg_one_smul] at h
  have fSub : ∀ x y : X, f (x - y) = f x - f y := fun x y => by
    rw [sub_eq_add_neg, lin.map_add, fNeg, ← sub_eq_add_neg]
  have fPosPart : ∀ c : X, f c⁺ = (f c)⁺ := fun c =>
    uniqueness_posPart (f c) (by rw [← fSub, posPart_sub_negPart])
      (disj c⁺ c⁻ (posPart_inf_negPart_eq_zero c))
  have fSup : ∀ a b : X, f (a ⊔ b) = f a ⊔ f b := fun a b => by
    rw [sup_eq_add_posPart_sub, lin.map_add, fPosPart, fSub, ← sup_eq_add_posPart_sub]
  exact { lin with
    map_sup' := fSup
    map_inf' := fun a b => by
      have h := fSup (-a) (-b)
      rw [← neg_inf] at h
      rw [fNeg, fNeg a, fNeg b, ← neg_inf] at h
      exact neg_inj.mp h }

end IsVecLatHom

/-- A vector lattice isomorphism: a real-linear equivalence that also preserves `⊔` and `⊓`. -/
structure VecLatEquiv (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [VectorLattice X] [VectorLattice Y] extends X ≃ₗ[ℝ] Y, LatticeHom X Y

namespace VecLatEquiv

/-- The canonical `FunLike` instance, making `VecLatEquiv X Y` a type of functions `X → Y`. -/
instance instFunLike : FunLike (VecLatEquiv X Y) X Y where
  coe e := e.toFun
  coe_injective' := by
    intro f g h
    cases f; cases g
    congr 1
    exact LinearEquiv.ext (congrFun h)

/-- Coerce a `VecLatEquiv` to a `VecLatHom`. -/
def toVecLatHom (e : VecLatEquiv X Y) : VecLatHom X Y :=
  { e.toLinearMap with
    map_sup' := e.map_sup'
    map_inf' := e.map_inf' }

/-- The identity vector lattice isomorphism. -/
def refl : VecLatEquiv X X :=
  { LinearEquiv.refl ℝ X with
    map_sup' := fun _ _ => rfl
    map_inf' := fun _ _ => rfl }

/-- The inverse of a vector lattice isomorphism. -/
def symm (e : VecLatEquiv X Y) : VecLatEquiv Y X :=
  { e.toLinearEquiv.symm with
    map_sup' := fun a b => by
      have h := e.map_sup' (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      change e.toLinearEquiv.symm (a ⊔ b) = e.toLinearEquiv.symm a ⊔ e.toLinearEquiv.symm b
      exact e.toLinearEquiv.injective (by rw [LinearEquiv.apply_symm_apply]; exact h.symm)
    map_inf' := fun a b => by
      have h := e.map_inf' (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      change e.toLinearEquiv.symm (a ⊓ b) = e.toLinearEquiv.symm a ⊓ e.toLinearEquiv.symm b
      exact e.toLinearEquiv.injective (by rw [LinearEquiv.apply_symm_apply]; exact h.symm) }

/-- Composition of vector lattice isomorphisms. -/
def trans {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (e₁ : VecLatEquiv X Y) (e₂ : VecLatEquiv Y Z) : VecLatEquiv X Z :=
  { e₁.toLinearEquiv.trans e₂.toLinearEquiv with
    map_sup' := fun a b => by
      show e₂.toFun (e₁.toFun (a ⊔ b)) = e₂.toFun (e₁.toFun a) ⊔ e₂.toFun (e₁.toFun b)
      rw [e₁.map_sup', e₂.map_sup']
    map_inf' := fun a b => by
      show e₂.toFun (e₁.toFun (a ⊓ b)) = e₂.toFun (e₁.toFun a) ⊓ e₂.toFun (e₁.toFun b)
      rw [e₁.map_inf', e₂.map_inf'] }

end VecLatEquiv
