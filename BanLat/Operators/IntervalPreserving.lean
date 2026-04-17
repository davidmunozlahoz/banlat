import BanLat.Operators.Hom
import BanLat.Dual

/-!
# Interval preserving operators

A positive operator `T : X →ₗ[ℝ] Y` between vector lattices is **interval preserving**
if it maps order intervals surjectively onto order intervals: `T[0, x] = [0, Tx]` for
every positive `x`. The Kim–Ando theorem establishes that a positive operator is a lattice
homomorphism if and only if its order adjoint is interval preserving, provided the order
dual of the domain separates points.
-/

/-! ### Definition and basic properties -/

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A positive operator is *interval preserving* if for every `0 ≤ x` and
`0 ≤ y ≤ T x`, there exists `0 ≤ z ≤ x` with `T z = y`. -/
def IsIntervalPreserving (T : X →ₗ[ℝ] Y) : Prop :=
  Positive T ∧ ∀ x : X, 0 ≤ x → ∀ y : Y, 0 ≤ y → y ≤ T x →
    ∃ z : X, 0 ≤ z ∧ z ≤ x ∧ T z = y

namespace IsIntervalPreserving

/-- An interval preserving operator is positive. -/
theorem pos {T : X →ₗ[ℝ] Y} (hT : IsIntervalPreserving T) :
    Positive T :=
  hT.1

/-- The identity operator is interval preserving. -/
theorem id : IsIntervalPreserving (LinearMap.id : X →ₗ[ℝ] X) :=
  ⟨fun _ hx => hx, fun _ _ y hy hyx => ⟨y, hy, hyx, rfl⟩⟩

/-- The composition of interval preserving operators is interval preserving. -/
theorem comp {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z] {S : Y →ₗ[ℝ] Z} {T : X →ₗ[ℝ] Y}
    (hS : IsIntervalPreserving S) (hT : IsIntervalPreserving T) :
    IsIntervalPreserving (S.comp T) := by
  refine ⟨fun x hx => hS.1 _ (hT.1 x hx), fun x hx y hy hyST => ?_⟩
  obtain ⟨w, hw0, hwT, hSw⟩ := hS.2 (T x) (hT.1 x hx) y hy hyST
  obtain ⟨z, hz0, hzx, hTz⟩ := hT.2 x hx w hw0 hwT
  exact ⟨z, hz0, hzx, show S.comp T z = y from by rw [LinearMap.comp_apply, hTz, hSw]⟩

/-- Every surjective vector lattice homomorphism is interval preserving. -/
theorem of_surjective_vecLatHom {T : VecLatHom X Y}
    (hsurj : Function.Surjective T) :
    IsIntervalPreserving T.toLinearMap := by
  refine ⟨fun x hx => T.map_nonneg hx, fun x hx y hy hyx => ?_⟩
  obtain ⟨a, ha⟩ := hsurj y
  refine ⟨(a ⊔ 0) ⊓ x, le_inf le_sup_right hx, inf_le_right, ?_⟩
  change T ((a ⊔ 0) ⊓ x) = y
  rw [map_inf, map_sup, map_zero, ha, sup_eq_left.mpr hy]
  exact inf_eq_left.mpr hyx

end IsIntervalPreserving

/-- For bijective operators, interval preserving is equivalent to being a
lattice homomorphism. -/
theorem isIntervalPreserving_iff_isVecLatHom_of_bijective
    {T : X →ₗ[ℝ] Y} (hbij : Function.Bijective T) :
    IsIntervalPreserving T ↔ IsVecLatHom T := by
  constructor
  · intro hIP
    have hmono := Positive.monotone_iff.mpr hIP.1
    have hrefl : ∀ x : X, 0 ≤ T x → 0 ≤ x := by
      intro x hTx
      obtain ⟨z, hz0, _, hTz⟩ := hIP.2 x⁺ (posPart_nonneg x) (T x) hTx
        (hmono (le_posPart x))
      have heq := hbij.1 hTz; subst heq; exact hz0
    have hord : ∀ a b : X, T a ≤ T b → a ≤ b := fun a b hab =>
      sub_nonneg.mp (hrefl _ (by rw [map_sub]; exact sub_nonneg.mpr hab))
    have hT_sup : ∀ a b : X, T (a ⊔ b) = T a ⊔ T b := by
      intro a b; apply le_antisymm
      · obtain ⟨c, hc⟩ := hbij.2 (T a ⊔ T b)
        rw [← hc]
        exact hmono (sup_le (hord _ _ (le_sup_left.trans_eq hc.symm))
          (hord _ _ (le_sup_right.trans_eq hc.symm)))
      · exact sup_le (hmono le_sup_left) (hmono le_sup_right)
    have hT_inf : ∀ a b : X, T (a ⊓ b) = T a ⊓ T b := by
      intro a b; apply le_antisymm
      · exact le_inf (hmono inf_le_left) (hmono inf_le_right)
      · obtain ⟨c, hc⟩ := hbij.2 (T a ⊓ T b)
        rw [← hc]
        exact hmono (le_inf (hord _ _ (hc.le.trans inf_le_left))
          (hord _ _ (hc.le.trans inf_le_right)))
    exact { toIsLinearMap := T.isLinear
            map_sup' := hT_sup
            map_inf' := hT_inf }
  · intro hVLH
    have hmono : Monotone T := by
      intro a b hab
      have := @le_sup_left _ _ (T a) (T b)
      rwa [← hVLH.map_sup', sup_eq_right.mpr hab] at this
    constructor
    · exact Positive.monotone_iff.mp hmono
    · intro x hx y hy hyx
      obtain ⟨a, ha⟩ := hbij.2 y
      refine ⟨(a ⊔ 0) ⊓ x, le_inf le_sup_right hx, inf_le_right, ?_⟩
      rw [hVLH.map_inf' (a ⊔ 0) x, hVLH.map_sup' a 0, map_zero, ha,
        sup_eq_left.mpr hy]
      exact inf_eq_left.mpr hyx

/-! ### Order adjoint -/

/-- The **order adjoint** of an order bounded operator `T : OrderBoundedHom X Y`
maps an order bounded functional `φ` on `Y` to the order bounded functional
`φ ∘ T` on `X`. -/
noncomputable def orderAdjoint (T : OrderBoundedHom X Y) :
    OrderDualSpace Y →ₗ[ℝ] OrderDualSpace X where
  toFun φ := ⟨φ.toLinearMap.comp T.toLinearMap, by
    intro x hx
    obtain ⟨w, hw, hbT⟩ := T.isOrderBounded' x hx
    obtain ⟨y, hy, hbφ⟩ := φ.isOrderBounded' w hw
    exact ⟨y, hy, fun z hz => hbφ _ (hbT z hz)⟩⟩
  map_add' _ _ := OrderBoundedHom.ext fun _ => rfl
  map_smul' _ _ := OrderBoundedHom.ext fun _ => rfl

@[simp]
theorem orderAdjoint_apply (T : OrderBoundedHom X Y)
    (φ : OrderDualSpace Y) (x : X) :
    orderAdjoint T φ x = φ (T x) := rfl

/-- The order adjoint of a positive operator is positive. -/
theorem orderAdjoint_positive {T : OrderBoundedHom X Y}
    (hT : Positive T.toLinearMap) :
    Positive (orderAdjoint T) := by
  intro φ hφ
  rw [OrderDualSpace.nonneg_iff] at hφ ⊢
  intro x hx
  exact hφ _ (hT x hx)

/-- The order adjoint of an order bounded operator is order bounded. -/
theorem orderAdjoint_isOrderBounded (T : OrderBoundedHom X Y) :
    IsOrderBounded (orderAdjoint T) := sorry

/-! ### Kim–Ando theorem -/

namespace VecLatHom

/-- A vector lattice homomorphism viewed as an order bounded operator. -/
def toOrderBoundedHom (T : VecLatHom X Y) : OrderBoundedHom X Y where
  toLinearMap := T.toLinearMap
  isOrderBounded' := Positive.isOrderBounded (Positive.monotone_iff.mp T.monotone)

@[simp]
theorem toOrderBoundedHom_apply (T : VecLatHom X Y) (x : X) :
    T.toOrderBoundedHom x = T x := rfl

/-- **Kim–Ando** (forward): a vector lattice homomorphism has an interval
preserving order adjoint. -/
theorem isIntervalPreserving_orderAdjoint (T : VecLatHom X Y) :
    IsIntervalPreserving
      (orderAdjoint T.toOrderBoundedHom) := sorry

end VecLatHom

/-- **Kim–Ando** (backward): if the order dual separates points and the order
adjoint is interval preserving, the operator is a lattice homomorphism. -/
theorem isVecLatHom_of_isIntervalPreserving_orderAdjoint
    (hsep : OrderDualSpace.SeparatesPoints X)
    (T : OrderBoundedHom X Y)
    (hTadj : IsIntervalPreserving (orderAdjoint T)) :
    IsVecLatHom T := sorry

/-- **Kim–Ando**: a positive order bounded operator between vector lattices is a
lattice homomorphism if and only if its order adjoint is interval preserving,
when the order dual separates points. -/
theorem kim_ando (hsep : OrderDualSpace.SeparatesPoints X)
    (T : OrderBoundedHom X Y) (_hT : Positive T.toLinearMap) :
    IsVecLatHom T ↔ IsIntervalPreserving (orderAdjoint T) := by
  constructor
  · intro hVLH
    have := VecLatHom.isIntervalPreserving_orderAdjoint
      (VecLatHom.of_isVecLatHom T hVLH)
    rwa [show (VecLatHom.of_isVecLatHom (⇑T) hVLH).toOrderBoundedHom = T
      from OrderBoundedHom.ext fun _ => rfl] at this
  · exact isVecLatHom_of_isIntervalPreserving_orderAdjoint hsep T

/-! ### Banach lattice specialization -/

section BanachLattice

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- **Kim–Ando** for Banach lattices: a positive continuous operator is a lattice
homomorphism if and only if its norm adjoint is interval preserving. -/
theorem kim_ando_banachLattice {T : X →L[ℝ] Y}
    (hT : Positive T.toLinearMap) :
    IsVecLatHom T ↔
      IsIntervalPreserving
        (ContinuousLinearMap.precomp ℝ T : NormDualSpace Y →L[ℝ]
          NormDualSpace X).toLinearMap := sorry

end BanachLattice
