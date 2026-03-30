import VecLat.Basic

structure VecLatHom (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y] extends X →ₗ[ℝ] Y, LatticeHom X Y

variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

structure IsVecLatHom (f : X → Y) extends IsLinearMap ℝ f where
  map_sup' : ∀ x y : X, f (x ⊔ y) = (f x) ⊔ (f y)
  map_inf' : ∀ x y : X, f (x ⊓ y) = (f x) ⊓ (f y)

namespace VecLatHom

instance instFunLike : FunLike (VecLatHom X Y) X Y where
  coe f := f.toFun
  coe_injective' f g h := by
    dsimp at h
    cases f
    cases g
    congr
    exact LinearMap.ext_iff.mpr (congrFun h)

theorem isVecLatHom (f : VecLatHom X Y) : IsVecLatHom f where
  map_add := f.toLinearMap.map_add
  map_smul := f.toLinearMap.map_smul
  map_sup' := f.toLatticeHom.map_sup'
  map_inf' := f.toLatticeHom.map_inf'

def of_isVecLatHom (f : X → Y) (h : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := h.map_add
  map_smul' := h.map_smul
  map_sup' := h.map_sup'
  map_inf' := h.map_inf'

instance instLatticeHomClass : LatticeHomClass (VecLatHom X Y) X Y where
  map_inf := by
    intro f a b
    exact f.toLatticeHom.map_inf' a b
  map_sup := by
    intro f a b
    exact f.toLatticeHom.map_sup' a b

instance instLinearMapClass : LinearMapClass (VecLatHom X Y) ℝ X Y where
  map_add := by
    intro f a b
    exact f.toLinearMap.map_add a b
  map_smulₛₗ := by
    intro f c x
    simp
    exact f.toLinearMap.map_smul c x

@[simp]
theorem toFun_eq_coe {f : VecLatHom X Y} : f.toFun = (f : X → Y) := rfl

theorem map_abs (f : VecLatHom X Y) (x : X) : f |x| = |f x| := by
  rw [abs, abs]
  simp

theorem monotone (f : VecLatHom X Y) : Monotone f := by
  intro x y hxy
  have : x ⊔ y = y := by simp [hxy]
  rw [← sup_eq_right, ← map_sup f x y, this]

def of_abs (f : X →ₗ[ℝ] Y) (abs : ∀ x : X, f |x| = |f x|) : VecLatHom X Y :=
  {f with
      map_sup' := by
        intro x y
        simp
        rw [sup_eq_half_smul_add_add_abs_sub ℝ,sup_eq_half_smul_add_add_abs_sub ℝ]
        rw [f.map_smul ⅟2 (x + y + |y-x|)]
        congr
        rw [f.map_add, f.map_add]
        congr
        rw [abs (y-x)]
        congr
        exact f.map_sub y x
      map_inf' := by
        intro x y
        simp
        rw [inf_eq_half_smul_add_sub_abs_sub ℝ,inf_eq_half_smul_add_sub_abs_sub ℝ]
        rw [f.map_smul ⅟2 (x + y - |y-x|)]
        congr
        rw [f.map_sub, f.map_add]
        congr
        rw [abs (y-x)]
        congr
        exact f.map_sub y x
    }

def comp {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z] (g : VecLatHom Y Z) (f : VecLatHom X Y) :
  VecLatHom X Z :=
  {LinearMap.comp g.toLinearMap f.toLinearMap with
    map_sup' := by
      intro x y
      simp
      change g ( f (x ⊔ y) ) = (g (f x)) ⊔ (g (f y))
      simp
    map_inf' := by
      intro x y
      simp
      change g ( f (x ⊓ y) ) = (g (f x)) ⊓ (g (f y))
      simp
  }

theorem comp_apply {Z : Type*} [AddCommGroup Z] [Lattice Z]
  [IsOrderedAddMonoid Z] [VectorLattice Z] (g : VecLatHom Y Z)
  (f : VecLatHom X Y) (x : X) : g.comp f x = g (f x) := by
    rw [comp]
    change (LinearMap.comp g.toLinearMap f.toLinearMap) x = g (f x)
    simp
    rfl

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

theorem symm_apply (f : VecLatHom X Y) (h : Function.Bijective f)
  (x : X) (y : Y) : (f.symm h) y = x ↔ y = f x := by
    let lineq := LinearEquiv.ofBijective f.toLinearMap h
    change lineq.symm y = x ↔ y = f x
    apply LinearEquiv.symm_apply_eq

end VecLatHom

namespace IsVecLatHom

def mk' (f : X → Y) (vlh : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := vlh.1.1
  map_smul' := vlh.1.2
  map_sup' := vlh.2
  map_inf' := vlh.3

@[simp]
theorem mk'_apply {f : X → Y} (vlh : IsVecLatHom f) (x : X) :
    mk' f vlh x = f x := rfl

theorem of_abs {f : X → Y} (lin : IsLinearMap ℝ f) (abs : ∀ x : X, f |x|
  = |f x|) : IsVecLatHom f :=
  VecLatHom.isVecLatHom (VecLatHom.of_abs (IsLinearMap.mk' f lin) abs)

end IsVecLatHom

structure VecLatEquiv (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [VectorLattice X] [VectorLattice Y] extends X ≃ₗ[ℝ] Y, LatticeHom X Y

namespace VecLatEquiv

def symm (e : VecLatEquiv X Y) : VecLatEquiv Y X := sorry

end VecLatEquiv
