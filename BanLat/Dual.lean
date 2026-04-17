import BanLat.Operators.Regular
import BanLat.Operators.RieszKantorovich

/-!
# The order dual and norm dual of a vector or Banach lattice

The **order dual** `OrderDualSpace X` of a vector lattice `X` is the space of order
bounded real-valued linear functionals on `X`. Since `ℝ` is order complete, the
Riesz–Kantorovich machinery equips it with a canonical order complete vector
lattice structure. The **norm dual** `NormDualSpace X` of a normed vector lattice `X`
is the space `X →L[ℝ] ℝ` of continuous linear functionals. For a Banach lattice
the two duals coincide as sets — every continuous functional is order bounded
and every order bounded functional is automatically continuous — and the norm
dual inherits the structure of a Banach lattice.
-/

/-! ### `ℝ` as a (Banach) vector lattice -/

noncomputable instance : VectorLattice ℝ where

noncomputable instance : NormedVectorLattice ℝ where

noncomputable instance : BanachLattice ℝ where

/-! ### The order dual -/

/-- The **order dual** of a vector lattice: order bounded real-valued
linear functionals. -/
abbrev OrderDualSpace (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Type _ :=
  OrderBoundedHom X ℝ

namespace OrderDualSpace

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- Order on the order dual: `φ ≤ ψ` iff `φ x ≤ ψ x` for all positive `x`. -/
theorem le_iff {φ ψ : OrderDualSpace X} :
    φ ≤ ψ ↔ ∀ x : X, 0 ≤ x → φ x ≤ ψ x :=
  OrderBoundedHom.le_iff

/-- A dual element is positive iff it sends positive elements of `X` to
non-negative reals. -/
theorem nonneg_iff {φ : OrderDualSpace X} :
    0 ≤ φ ↔ ∀ x : X, 0 ≤ x → 0 ≤ φ x :=
  OrderBoundedHom.le_iff

/-- Riesz–Kantorovich: positive part of a dual functional at a positive
element is the supremum of `φ y` over `0 ≤ y ≤ x`. -/
theorem isLUB_posPart_apply {φ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB {r : ℝ | ∃ y, 0 ≤ y ∧ y ≤ x ∧ r = φ y} (φ⁺ x) :=
  OrderBoundedHom.isLUB_posPart_apply hx

/-- Negative part of a dual functional at a positive element. -/
theorem isLUB_negPart_apply {φ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB {r : ℝ | ∃ y, 0 ≤ y ∧ y ≤ x ∧ r = -(φ y)} (φ⁻ x) :=
  OrderBoundedHom.isLUB_negPart_apply hx

/-- Modulus of a dual functional at a positive element. -/
theorem isLUB_abs_apply {φ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB {r : ℝ | ∃ y, |y| ≤ x ∧ r = |φ y|} (|φ| x) :=
  OrderBoundedHom.isLUB_abs_apply hx

/-- Riesz–Kantorovich formula for the supremum of two dual functionals. -/
theorem isLUB_sup_apply {φ ψ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsLUB
      {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x ∧ r = φ y + ψ z}
      ((φ ⊔ ψ) x) :=
  OrderBoundedHom.isLUB_sup_apply hx

/-- Riesz–Kantorovich formula for the infimum of two dual functionals. -/
theorem isGLB_inf_apply {φ ψ : OrderDualSpace X} {x : X} (hx : 0 ≤ x) :
    IsGLB
      {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x ∧ r = φ y + ψ z}
      ((φ ⊓ ψ) x) :=
  OrderBoundedHom.isGLB_inf_apply hx

/-- The order dual is order complete: every non-empty order bounded family of
functionals admits a least upper bound. -/
example : IsOrderComplete (OrderDualSpace X) := inferInstance

/-- Every order dual element is regular: it can be written as a difference of
two positive functionals. -/
theorem isRegularOp (φ : OrderDualSpace X) :
    IsRegularOp φ.toLinearMap :=
  IsOrderBounded.isRegularOp φ.isOrderBounded'

variable (X) in
/-- The order dual separates points of `X`: every nonzero element is detected by
some order bounded functional. -/
def SeparatesPoints : Prop :=
  ∀ x : X, (∀ φ : OrderDualSpace X, φ x = 0) → x = 0

end OrderDualSpace

/-! ### The norm dual -/

/-- The **norm dual** of a normed vector lattice: continuous real-valued
linear functionals. -/
abbrev NormDualSpace (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Type _ :=
  X →L[ℝ] ℝ

namespace NormDualSpace

section NormedVectorLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [NormedVectorLattice X]

/-- Every continuous linear functional on a normed vector lattice is order
bounded. -/
theorem isOrderBounded (φ : NormDualSpace X) :
    IsOrderBounded φ.toLinearMap := by
  intro x hx
  refine ⟨‖φ‖ * ‖x‖, mul_nonneg (norm_nonneg _) (norm_nonneg _), fun z hz => ?_⟩
  have hzx : ‖z‖ ≤ ‖x‖ :=
    norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx]; exact hz)
  have h1 : |φ.toLinearMap z| = ‖φ z‖ := (Real.norm_eq_abs _).symm
  rw [h1]
  exact (φ.le_opNorm z).trans (by gcongr)

/-- The order bounded functional underlying a continuous linear functional. -/
def toOrderDualSpace (φ : NormDualSpace X) : OrderDualSpace X where
  toLinearMap := φ.toLinearMap
  isOrderBounded' := isOrderBounded φ

@[simp]
theorem toOrderDualSpace_apply (φ : NormDualSpace X) (x : X) :
    toOrderDualSpace φ x = φ x := rfl

/-- Bundling `toOrderDualSpace` as a real-linear map. -/
def toOrderDualSpaceLinear : NormDualSpace X →ₗ[ℝ] OrderDualSpace X where
  toFun := toOrderDualSpace
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

end NormedVectorLattice

section BanachLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- For a Banach lattice, every order bounded functional is continuous. -/
noncomputable def ofOrderDualSpace (f : OrderDualSpace X) : NormDualSpace X :=
  ⟨f.toLinearMap, IsOrderBounded.continuous f.isOrderBounded'⟩

@[simp]
theorem ofOrderDualSpace_apply (f : OrderDualSpace X) (x : X) :
    ofOrderDualSpace f x = f x := rfl

/-- For a Banach lattice, the order dual and the norm dual are linearly
equivalent: continuous functionals are exactly the order bounded ones. -/
noncomputable def equivOrderDualSpace : NormDualSpace X ≃ₗ[ℝ] OrderDualSpace X where
  toFun := toOrderDualSpace
  invFun := ofOrderDualSpace
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private theorem toOrderDualSpace_injective :
    Function.Injective (toOrderDualSpace (X := X)) := by
  intro f g h
  ext x
  have := congrArg (fun (ψ : OrderDualSpace X) => ψ x) h
  simpa using this

instance instLE : LE (NormDualSpace X) where
  le f g := toOrderDualSpace f ≤ toOrderDualSpace g

instance instLT : LT (NormDualSpace X) where
  lt f g := toOrderDualSpace f < toOrderDualSpace g

noncomputable instance instMax : Max (NormDualSpace X) where
  max f g := ofOrderDualSpace (toOrderDualSpace f ⊔ toOrderDualSpace g)

noncomputable instance instMin : Min (NormDualSpace X) where
  min f g := ofOrderDualSpace (toOrderDualSpace f ⊓ toOrderDualSpace g)

private theorem toOrderDualSpace_le {f g : NormDualSpace X} :
    toOrderDualSpace f ≤ toOrderDualSpace g ↔ f ≤ g := Iff.rfl

private theorem toOrderDualSpace_lt {f g : NormDualSpace X} :
    toOrderDualSpace f < toOrderDualSpace g ↔ f < g := Iff.rfl

private theorem toOrderDualSpace_sup (f g : NormDualSpace X) :
    toOrderDualSpace (f ⊔ g) = toOrderDualSpace f ⊔ toOrderDualSpace g := by
  ext x; rfl

private theorem toOrderDualSpace_inf (f g : NormDualSpace X) :
    toOrderDualSpace (f ⊓ g) = toOrderDualSpace f ⊓ toOrderDualSpace g := by
  ext x; rfl

/-- The induced lattice structure on the norm dual: `φ ≤ ψ` iff `φ x ≤ ψ x`
for all positive `x`, with sup/inf transported from the order dual. -/
noncomputable instance instLattice : Lattice (NormDualSpace X) :=
  toOrderDualSpace_injective.lattice _ toOrderDualSpace_le
    toOrderDualSpace_lt toOrderDualSpace_sup toOrderDualSpace_inf

private theorem toOrderDualSpace_add (f g : NormDualSpace X) :
    toOrderDualSpace (f + g) = toOrderDualSpace f + toOrderDualSpace g := by
  ext; rfl

private theorem toOrderDualSpace_smul (r : ℝ) (f : NormDualSpace X) :
    toOrderDualSpace (r • f) = r • toOrderDualSpace f := by
  ext; rfl

/-- The norm dual of a Banach lattice is an ordered additive group. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (NormDualSpace X) where
  add_le_add_left f g hfg c := by
    change toOrderDualSpace f ≤ toOrderDualSpace g at hfg
    change toOrderDualSpace (f + c) ≤ toOrderDualSpace (g + c)
    rw [toOrderDualSpace_add, toOrderDualSpace_add]
    exact IsOrderedAddMonoid.add_le_add_left _ _ hfg c.toOrderDualSpace

instance instPosSMulMono : PosSMulMono ℝ (NormDualSpace X) where
  smul_le_smul_of_nonneg_left {r} hr {f g} hfg := by
    change toOrderDualSpace f ≤ toOrderDualSpace g at hfg
    change toOrderDualSpace (r • f) ≤ toOrderDualSpace (r • g)
    rw [toOrderDualSpace_smul, toOrderDualSpace_smul]
    exact smul_le_smul_of_nonneg_left hfg hr

/-- The norm dual of a Banach lattice is a vector lattice. -/
noncomputable instance instVectorLattice : VectorLattice (NormDualSpace X) where

private theorem coe_abs_apply (φ : NormDualSpace X) (x : X) :
    (|φ| : NormDualSpace X) x = |toOrderDualSpace φ| x := rfl

private theorem abs_apply_le_abs_apply_abs (φ : NormDualSpace X) (x : X) :
    |φ x| ≤ (|φ| : NormDualSpace X) (|x|) := by
  rw [coe_abs_apply]
  exact (OrderBoundedHom.isLUB_abs_apply (f := toOrderDualSpace φ)
    (abs_nonneg x)).1 ⟨x, le_refl _, rfl⟩

private theorem abs_apply_nonneg (φ : NormDualSpace X) {x : X} (hx : 0 ≤ x) :
    0 ≤ (|φ| : NormDualSpace X) x := by
  rw [coe_abs_apply]
  exact (OrderBoundedHom.isLUB_abs_apply (f := toOrderDualSpace φ) hx).1
    ⟨0, by simp [hx], by simp⟩

/-- For a positive `x`, `|φ| x` is bounded by `‖φ‖ * ‖x‖`. -/
private theorem abs_apply_le_norm_mul (φ : NormDualSpace X) {x : X} (hx : 0 ≤ x) :
    (|φ| : NormDualSpace X) x ≤ ‖φ‖ * ‖x‖ := by
  rw [coe_abs_apply]
  refine (OrderBoundedHom.isLUB_abs_apply (f := toOrderDualSpace φ) hx).2 ?_
  rintro _ ⟨y, hyx, rfl⟩
  have hy : ‖y‖ ≤ ‖x‖ :=
    norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx]; exact hyx)
  calc |φ y| = ‖φ y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ‖ * ‖y‖ := φ.le_opNorm y
    _ ≤ ‖φ‖ * ‖x‖ := by gcongr

/-- The norm dual carries a solid lattice norm: `|φ| ≤ |ψ|` implies
`‖φ‖ ≤ ‖ψ‖`. -/
instance instHasSolidNorm : HasSolidNorm (NormDualSpace X) where
  solid {φ ψ} hφψ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h1 : |φ x| ≤ (|φ| : NormDualSpace X) (|x|) :=
      abs_apply_le_abs_apply_abs φ x
    have hOD : (|φ| : NormDualSpace X) (|x|) ≤ (|ψ| : NormDualSpace X) (|x|) := by
      change toOrderDualSpace |φ| ≤ toOrderDualSpace |ψ| at hφψ
      exact hφψ _ (abs_nonneg x)
    have h2 : (|ψ| : NormDualSpace X) (|x|) ≤ ‖ψ‖ * ‖x‖ := by
      have := abs_apply_le_norm_mul ψ (abs_nonneg x)
      rwa [norm_abs_eq_norm] at this
    calc ‖φ x‖ = |φ x| := Real.norm_eq_abs _
      _ ≤ (|ψ| : NormDualSpace X) (|x|) := h1.trans hOD
      _ ≤ ‖ψ‖ * ‖x‖ := h2

/-- The norm dual of a Banach lattice is itself a normed vector lattice. -/
noncomputable instance instNormedVectorLattice :
    NormedVectorLattice (NormDualSpace X) where
  norm_smul := norm_smul

/-- The norm dual of a Banach lattice is a Banach lattice. -/
noncomputable instance instBanachLattice : BanachLattice (NormDualSpace X) where

/-- The dual norm of the modulus equals the dual norm: `‖|φ|‖ = ‖φ‖`. -/
theorem norm_abs (φ : NormDualSpace X) : ‖|φ|‖ = ‖φ‖ :=
  le_antisymm
    (HasSolidNorm.solid (by rw [abs_abs]))
    (HasSolidNorm.solid (by rw [abs_abs]))

/-- For a positive functional, the dual norm is the supremum of `φ x` over the
intersection of the unit ball with the positive cone. -/
theorem norm_of_nonneg {φ : NormDualSpace X} (hφ : 0 ≤ φ) :
    ‖φ‖ = sSup ((φ : X → ℝ) '' ({x | ‖x‖ ≤ 1} ∩ {x | 0 ≤ x})) := by
  set S := (φ : X → ℝ) '' ({x | ‖x‖ ≤ 1} ∩ {x | 0 ≤ x})
  have hpos : ∀ {x : X}, 0 ≤ x → 0 ≤ φ x := by
    change toOrderDualSpace 0 ≤ toOrderDualSpace φ at hφ
    intro x hx
    have := hφ x hx; simpa using this
  have habs_eq : (|φ| : NormDualSpace X) = φ := abs_of_nonneg hφ
  have hub : ∀ s ∈ S, s ≤ ‖φ‖ := by
    rintro _ ⟨x, ⟨hx1, hx0⟩, rfl⟩
    have h1 : ‖φ x‖ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    have h2 : φ x = ‖φ x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos hx0)]
    rw [h2]
    exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hx1 (norm_nonneg _))
  have hbdd : BddAbove S := ⟨‖φ‖, hub⟩
  have hne : S.Nonempty := ⟨0, 0, ⟨by simp, le_refl _⟩, by simp⟩
  have hsup_nn : 0 ≤ sSup S :=
    Real.sSup_nonneg (by rintro _ ⟨y, ⟨_, hy0⟩, rfl⟩; exact hpos hy0)
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ hsup_nn fun x => ?_
    -- ‖φ x‖ ≤ φ |x| (positivity)
    have hbound : ‖φ x‖ ≤ φ (|x|) := by
      rw [Real.norm_eq_abs]
      have h := abs_apply_le_abs_apply_abs φ x
      rw [habs_eq] at h; exact h
    by_cases hx0 : x = 0
    · subst hx0
      simp only [map_zero, norm_zero, mul_zero]
      exact le_refl _
    -- normalise
    have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
    set y : X := ‖x‖⁻¹ • |x|
    have hy_nn : 0 ≤ y := smul_nonneg (inv_nonneg.mpr hxn.le) (abs_nonneg x)
    have hy_norm : ‖y‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hxn.le,
        norm_abs_eq_norm]
      exact (inv_mul_cancel₀ hxn.ne').le
    have hyS : φ y ∈ S := ⟨y, ⟨hy_norm, hy_nn⟩, rfl⟩
    have hyS_le : φ y ≤ sSup S := le_csSup hbdd hyS
    have hφy : φ y = ‖x‖⁻¹ * φ (|x|) := by
      change φ.toLinearMap (‖x‖⁻¹ • |x|) = _
      rw [map_smul]; rfl
    have hφabs : φ (|x|) ≤ ‖x‖ * sSup S := by
      have h1 := mul_le_mul_of_nonneg_left hyS_le hxn.le
      rw [hφy, ← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul] at h1
      exact h1
    exact hbound.trans (hφabs.trans (by rw [mul_comm]))
  · exact csSup_le hne hub

/-- For a Banach lattice, the order dual separates points. -/
theorem orderDual_separatesPoints :
    OrderDualSpace.SeparatesPoints X :=
  sorry

end BanachLattice

end NormDualSpace
