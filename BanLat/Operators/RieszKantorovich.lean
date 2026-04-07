import BanLat.Operators.OrderBounded
import BanLat.OrderComplete

/-!
# The Riesz-Kantorovich theorem

When the codomain `Y` is order complete, the space `OrderBoundedHom X Y` of
order bounded operators is an order complete vector lattice, with explicit
formulas for the lattice operations (the **Riesz-Kantorovich formulas**).
-/

namespace OrderBoundedHom

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X]
  [VectorLattice Y] [IsOrderComplete Y]

/-! ### Positive part construction for the Riesz-Kantorovich theorem -/

private def ppSet (f : OrderBoundedHom X Y) (x : X) : Set Y :=
  { w | ∃ y, 0 ≤ y ∧ y ≤ x ∧ w = f y }

omit [IsOrderComplete Y] in
private lemma ppSet_nonempty (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : (ppSet f x).Nonempty :=
  ⟨0, 0, le_rfl, hx, (map_zero f.toLinearMap).symm⟩

omit [IsOrderComplete Y] in
private lemma ppSet_bddAbove (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : BddAbove (ppSet f x) := by
  obtain ⟨u, _, hbound⟩ := f.isOrderBounded' x hx
  exact ⟨u, fun _ ⟨y, hy, hyx, hw⟩ => hw ▸
    (le_abs_self _).trans
      (hbound y (sup_le hyx (neg_nonpos_of_nonneg hy |>.trans hx)))⟩

private noncomputable def ppFun (f : OrderBoundedHom X Y)
    (x : X) : Y := by
  classical
  exact if hx : 0 ≤ x then
    (IsOrderComplete.isLUB_of_bddAbove (ppSet_bddAbove f hx)
      (ppSet_nonempty f hx)).choose
  else 0

private lemma ppFun_isLUB (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : IsLUB (ppSet f x) (ppFun f x) := by
  simp only [ppFun, dif_pos hx]
  exact (IsOrderComplete.isLUB_of_bddAbove (ppSet_bddAbove f hx)
    (ppSet_nonempty f hx)).choose_spec

private lemma ppFun_nonneg (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : 0 ≤ ppFun f x :=
  (ppFun_isLUB f hx).1
    ⟨0, le_rfl, hx, (map_zero f.toLinearMap).symm⟩

private lemma le_ppFun (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : f x ≤ ppFun f x :=
  (ppFun_isLUB f hx).1 ⟨x, hx, le_refl x, rfl⟩

private lemma ppFun_le (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) {u : Y}
    (hu : u ∈ upperBounds (ppSet f x)) : ppFun f x ≤ u :=
  (ppFun_isLUB f hx).2 hu

private lemma ppFun_add (f : OrderBoundedHom X Y) {x y : X}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ppFun f (x + y) = ppFun f x + ppFun f y := by
  apply le_antisymm
  · -- ≤: Riesz decomposition
    apply ppFun_le f (add_nonneg hx hy)
    intro w ⟨z, hz, hzxy, hw⟩
    obtain ⟨z₁, z₂, hz₁, hz₁x, hz₂, hz₂y, hsum⟩ :=
      riesz_decomposition z x y hz hx hy hzxy
    rw [hw, hsum]
    change f.toLinearMap (z₁ + z₂) ≤ ppFun f x + ppFun f y
    rw [map_add]
    exact add_le_add
      ((ppFun_isLUB f hx).1 ⟨z₁, hz₁, hz₁x, rfl⟩)
      ((ppFun_isLUB f hy).1 ⟨z₂, hz₂, hz₂y, rfl⟩)
  · -- ≥: double LUB argument
    have step1 : ∀ w₁ ∈ ppSet f x, ∀ w₂ ∈ ppSet f y,
        w₁ + w₂ ≤ ppFun f (x + y) := by
      intro w₁ ⟨z₁, hz₁, hz₁x, hw₁⟩ w₂ ⟨z₂, hz₂, hz₂y, hw₂⟩
      rw [hw₁, hw₂]
      change f.toLinearMap z₁ + f.toLinearMap z₂ ≤ ppFun f (x + y)
      rw [← map_add]
      exact (ppFun_isLUB f (add_nonneg hx hy)).1
        ⟨z₁ + z₂, add_nonneg hz₁ hz₂, add_le_add hz₁x hz₂y, rfl⟩
    have step2 : ∀ w₂ ∈ ppSet f y,
        ppFun f x + w₂ ≤ ppFun f (x + y) := by
      intro w₂ hw₂
      have hub : ppFun f (x + y) - w₂ ∈ upperBounds (ppSet f x) :=
        fun w₁ hw₁ =>
          le_sub_iff_add_le.mpr (step1 w₁ hw₁ w₂ hw₂)
      exact le_sub_iff_add_le.mp (ppFun_le f hx hub)
    have hub : ppFun f (x + y) - ppFun f x ∈
        upperBounds (ppSet f y) :=
      fun w₂ hw₂ => le_sub_iff_add_le.mpr
        (by rw [add_comm]; exact step2 w₂ hw₂)
    rw [add_comm]
    exact le_sub_iff_add_le.mp (ppFun_le f hy hub)

/-! ### The positive part operator -/

private noncomputable def ppOp (f : OrderBoundedHom X Y) :
    X →ₗ[ℝ] Y := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  exact Positive.extension (fun x hx => ppFun_nonneg f hx)
    (fun _ _ hx hy => ppFun_add f hx hy)

private lemma ppOp_apply_nonneg (f : OrderBoundedHom X Y)
    {x : X} (hx : 0 ≤ x) : ppOp f x = ppFun f x := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  exact Positive.extension_nonneg (fun x hx => ppFun_nonneg f hx)
    (fun _ _ hx hy => ppFun_add f hx hy) hx

private lemma ppOp_positive (f : OrderBoundedHom X Y) :
    Positive (ppOp f) := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  exact Positive.extension_positive
    (fun x hx => ppFun_nonneg f hx)
    (fun _ _ hx hy => ppFun_add f hx hy)

private lemma le_ppOp (f : OrderBoundedHom X Y) {x : X}
    (hx : 0 ≤ x) : f x ≤ ppOp f x :=
  ppOp_apply_nonneg f hx ▸ le_ppFun f hx

private lemma ppOp_le (f g : OrderBoundedHom X Y)
    (hg0 : ∀ x : X, 0 ≤ x → 0 ≤ g x)
    (hgf : ∀ x : X, 0 ≤ x → f x ≤ g x)
    {x : X} (hx : 0 ≤ x) : ppOp f x ≤ g x := by
  rw [ppOp_apply_nonneg f hx]
  apply ppFun_le f hx
  intro _ ⟨y, hy, hyx, hw⟩
  rw [hw]
  exact (hgf y hy).trans
    ((Positive.monotone_iff.mpr
      (show Positive g.toLinearMap from hg0)) hyx)

/-! ### Sup, inf and lattice laws -/

private noncomputable def obPosPart
    (f : OrderBoundedHom X Y) : OrderBoundedHom X Y :=
  ⟨ppOp f, Positive.isOrderBounded (ppOp_positive f)⟩

private lemma obPosPart_nonneg (f : OrderBoundedHom X Y) :
    (0 : OrderBoundedHom X Y) ≤ obPosPart f :=
  le_iff.mpr fun x hx => by
    convert ppOp_positive f x hx using 1

private lemma le_obPosPart (f : OrderBoundedHom X Y) :
    f ≤ obPosPart f :=
  le_iff.mpr fun _ hx => le_ppOp f hx

private lemma obPosPart_le {f g : OrderBoundedHom X Y}
    (hg0 : (0 : OrderBoundedHom X Y) ≤ g) (hgf : f ≤ g) :
    obPosPart f ≤ g :=
  le_iff.mpr fun x hx => by
    apply ppOp_le f g _ _ hx
    · intro y hy; convert le_iff.mp hg0 y hy using 1
    · intro y hy; exact le_iff.mp hgf y hy

private noncomputable def obSup
    (f g : OrderBoundedHom X Y) : OrderBoundedHom X Y :=
  g + obPosPart (f - g)

private noncomputable def obInf
    (f g : OrderBoundedHom X Y) : OrderBoundedHom X Y :=
  f + g - obSup f g

private lemma le_obSup_left (f g : OrderBoundedHom X Y) :
    f ≤ obSup f g := by
  change f ≤ g + obPosPart (f - g)
  have h1 := add_le_add_left (le_obPosPart (f - g)) g
  rw [sub_add_cancel, add_comm] at h1
  exact h1

private lemma le_obSup_right (f g : OrderBoundedHom X Y) :
    g ≤ obSup f g := by
  change g ≤ g + obPosPart (f - g)
  exact le_add_of_nonneg_right (obPosPart_nonneg (f - g))

private lemma obSup_le {f g h : OrderBoundedHom X Y}
    (hfh : f ≤ h) (hgh : g ≤ h) :
    obSup f g ≤ h := by
  change g + obPosPart (f - g) ≤ h
  have h1 : obPosPart (f - g) ≤ h - g :=
    obPosPart_le (sub_nonneg.mpr hgh)
      (sub_le_sub_right hfh g)
  have h2 := add_le_add_left h1 g
  rw [sub_add_cancel, add_comm] at h2
  exact h2

private lemma obInf_le_left (f g : OrderBoundedHom X Y) :
    obInf f g ≤ f := by
  have : obInf f g = f - obPosPart (f - g) := by
    change f + g - (g + obPosPart (f - g)) =
      f - obPosPart (f - g); abel
  rw [this]
  exact sub_le_self f (obPosPart_nonneg (f - g))

private lemma obInf_le_right (f g : OrderBoundedHom X Y) :
    obInf f g ≤ g := by
  have h1 : obInf f g = f - obPosPart (f - g) := by
    change f + g - (g + obPosPart (f - g)) =
      f - obPosPart (f - g); abel
  rw [h1]
  calc f - obPosPart (f - g)
      ≤ f - (f - g) :=
        sub_le_sub_left (le_obPosPart (f - g)) f
    _ = g := by abel

private lemma le_obInf {f g h : OrderBoundedHom X Y}
    (hhf : h ≤ f) (hhg : h ≤ g) :
    h ≤ obInf f g := by
  have key : obPosPart (f - g) ≤ f - h :=
    obPosPart_le (sub_nonneg.mpr hhf)
      (sub_le_sub_left hhg f)
  have h2 : obInf f g = f - obPosPart (f - g) := by
    change f + g - (g + obPosPart (f - g)) =
      f - obPosPart (f - g); abel
  rw [h2]
  calc h = f - (f - h) := by abel
    _ ≤ f - obPosPart (f - g) :=
        sub_le_sub_left key f

/-- When the codomain is order complete, the space of order bounded
operators is a lattice. -/
noncomputable instance instLattice :
    Lattice (OrderBoundedHom X Y) :=
  { (inferInstance :
      PartialOrder (OrderBoundedHom X Y)) with
    sup := obSup
    inf := obInf
    le_sup_left := le_obSup_left
    le_sup_right := le_obSup_right
    sup_le := fun _ _ _ hfh hgh => obSup_le hfh hgh
    inf_le_left := obInf_le_left
    inf_le_right := obInf_le_right
    le_inf := fun _ _ _ hhf hhg => le_obInf hhf hhg }

/-- When the codomain is order complete, the space of order bounded
operators is a vector lattice. -/
noncomputable instance instVectorLattice :
    VectorLattice (OrderBoundedHom X Y) :=
  { (inferInstance : Module ℝ (OrderBoundedHom X Y)),
    (inferInstance :
      PosSMulMono ℝ (OrderBoundedHom X Y)) with }

/-! ### Riesz-Kantorovich formulas -/

omit [IsOrderComplete Y] in
private lemma sub_apply (f g : OrderBoundedHom X Y) (y : X) :
    (f - g : OrderBoundedHom X Y) y = f y - g y :=
  show (f.toLinearMap - g.toLinearMap) y = _ from
  LinearMap.sub_apply _ _ _

omit [IsOrderComplete Y] in
private lemma add_apply' (f g : OrderBoundedHom X Y) (y : X) :
    (f + g : OrderBoundedHom X Y) y = f y + g y :=
  show (f.toLinearMap + g.toLinearMap) y = _ from
  LinearMap.add_apply _ _ _

omit [IsOrderComplete Y] in
private lemma map_sub_val (f : OrderBoundedHom X Y) (a b : X) :
    f (a - b) = f a - f b :=
  show f.toLinearMap (a - b) = _ from map_sub f.toLinearMap a b

private lemma sup_zero_eq_obPosPart
    (f : OrderBoundedHom X Y) :
    f ⊔ 0 = obPosPart f := by
  have : f ⊔ (0 : OrderBoundedHom X Y) =
      (0 : OrderBoundedHom X Y) + obPosPart (f - 0) := rfl
  rw [sub_zero, zero_add] at this; exact this

private lemma posPart_apply_eq_ppFun
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    f⁺ x = ppFun f x := by
  rw [posPart_def, sup_zero_eq_obPosPart]
  convert ppOp_apply_nonneg f hx using 1

/-- The positive part at a positive element is the supremum over
the order interval `[0, x]`. -/
theorem isLUB_posPart_apply
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y, 0 ≤ y ∧ y ≤ x ∧ w = f y}
      (f⁺ x) := by
  rw [posPart_apply_eq_ppFun hx]; exact ppFun_isLUB f hx

/-- The negative part at a positive element. -/
theorem isLUB_negPart_apply
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y, 0 ≤ y ∧ y ≤ x ∧ w = -(f y)}
      (f⁻ x) := by
  have h : f⁻ = (-f)⁺ := by rw [negPart_def, posPart_def]
  rw [h, posPart_apply_eq_ppFun hx]
  exact ppFun_isLUB (-f) hx

/-- The supremum of order bounded operators at a positive element
is given by the Riesz-Kantorovich formula. -/
theorem isLUB_sup_apply
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB
      {w | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊔ g) x) := by
  have hval : (f ⊔ g) x = g x + (f - g)⁺ x := by
    have h := sup_eq_add_posPart_sub f g; rw [h, add_apply']
  have hbridge : ∀ y : X, f y + g (x - y) = g x + (f - g) y := by
    intro y; rw [sub_apply, map_sub_val]; abel
  rw [hval, posPart_apply_eq_ppFun hx]
  have hPP := ppFun_isLUB (f - g) hx
  constructor
  · intro w ⟨y, z, hy, hz, hyz, hw⟩
    have hyx : y ≤ x := hyz ▸ le_add_of_nonneg_right hz
    rw [hw, show z = x - y from eq_sub_of_add_eq' hyz, hbridge]
    gcongr; exact hPP.1 ⟨y, hy, hyx, rfl⟩
  · intro u hu
    rw [show g x + ppFun (f - g) x =
        ppFun (f - g) x + g x from add_comm _ _,
      ← le_sub_iff_add_le]
    apply hPP.2
    intro v ⟨y, hy, hyx, hv⟩
    rw [le_sub_iff_add_le, hv, add_comm, ← hbridge]
    exact hu ⟨y, x - y, hy, sub_nonneg.mpr hyx, by abel, rfl⟩

omit [IsOrderComplete Y] in
private lemma map_add_val (f : OrderBoundedHom X Y) (a b : X) :
    f (a + b) = f a + f b :=
  show f.toLinearMap _ = _ from map_add f.toLinearMap a b

omit [IsOrderComplete Y] in
private lemma neg_apply' (f : OrderBoundedHom X Y) (y : X) :
    (-f : OrderBoundedHom X Y) y = -(f y) :=
  show (-f.toLinearMap) y = _ from LinearMap.neg_apply _ _

/-- The infimum of order bounded operators at a positive element. -/
theorem isGLB_inf_apply
    {f g : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsGLB
      {w | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x
        ∧ w = f y + g z}
      ((f ⊓ g) x) := by
  set S := {w : Y | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x
      ∧ w = f y + g z}
  set c := f x + g x
  have hsym : ∀ w ∈ S, c - w ∈ S := by
    intro w ⟨y, z, hy, hz, hyz, hw⟩
    refine ⟨z, y, hz, hy, by rw [add_comm]; exact hyz, ?_⟩
    rw [hw]; simp only [c]
    rw [← hyz, map_add_val f y z, map_add_val g y z]; abel
  have hinf : (f ⊓ g) x = c - (f ⊔ g) x := by
    have h : (f ⊓ g : OrderBoundedHom X Y) = f + g - (f ⊔ g) :=
      eq_sub_of_add_eq' ((add_comm _ _).trans (inf_add_sup f g))
    rw [h, sub_apply, add_apply']
  rw [hinf]
  have hLUB : IsLUB S ((f ⊔ g) x) := isLUB_sup_apply hx
  exact ⟨fun _ hw => sub_le_comm.mp (hLUB.1 (hsym _ hw)),
    fun _ hb => le_sub_comm.mpr
      (hLUB.2 fun _ hw => le_sub_comm.mp (hb (hsym _ hw)))⟩

/-- The modulus at a positive element. -/
theorem isLUB_abs_apply
    {f : OrderBoundedHom X Y} {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y, |y| ≤ x ∧ w = |f y|}
      (|f| x) := by
  have habs_val : |f| x = f⁺ x + f⁻ x := by
    have h : (|f| : OrderBoundedHom X Y) = f⁺ + f⁻ :=
      (posPart_add_negPart f).symm
    rw [h]; exact add_apply' f⁺ f⁻ x
  constructor
  · -- Upper bound: |f y| ≤ |f| x for |y| ≤ x
    intro w ⟨y, hyx, hw⟩
    rw [hw, habs_val]
    have hPP := isLUB_posPart_apply (f := f) hx
    have hNP := isLUB_negPart_apply (f := f) hx
    have hpos_le : y⁺ ≤ x :=
      (sup_le (le_abs_self y) (abs_nonneg y)).trans hyx
    have hneg_le : y⁻ ≤ x :=
      (sup_le (neg_le_abs y) (abs_nonneg y)).trans hyx
    have hfy : f y = f y⁺ - f y⁻ := by
      rw [← map_sub_val]; congr 1; exact (posPart_sub_negPart y).symm
    have hfyle : f y ≤ f⁺ x + f⁻ x := by
      rw [hfy, sub_eq_add_neg]
      exact add_le_add
        (hPP.1 ⟨y⁺, posPart_nonneg y, hpos_le, rfl⟩)
        (hNP.1 ⟨y⁻, negPart_nonneg y, hneg_le, rfl⟩)
    have hnfyle : -(f y) ≤ f⁺ x + f⁻ x := by
      rw [hfy, neg_sub, sub_eq_add_neg]
      exact add_le_add
        (hPP.1 ⟨y⁻, negPart_nonneg y, hneg_le, rfl⟩)
        (hNP.1 ⟨y⁺, posPart_nonneg y, hpos_le, rfl⟩)
    exact sup_le hfyle hnfyle
  · -- LUB: any upper bound u of B satisfies |f| x ≤ u
    intro u hu
    change (f ⊔ (-f : OrderBoundedHom X Y)) x ≤ u
    have hLUB : IsLUB _ ((f ⊔ (-f : OrderBoundedHom X Y)) x) :=
      isLUB_sup_apply hx
    exact hLUB.2 fun w ⟨a, b, ha, hb, hab, hw⟩ => by
      have habsle : |a - b| ≤ x :=
        sup_le
          ((sub_le_self a hb).trans (hab ▸ le_add_of_nonneg_right hb))
          ((neg_sub a b ▸ (sub_le_self b ha).trans
            (hab ▸ le_add_of_nonneg_left ha)))
      have hweq : w = f (a - b) := by
        rw [hw, neg_apply', map_sub_val]; abel
      rw [hweq]
      exact (le_abs_self _).trans (hu ⟨a - b, habsle, rfl⟩)

/-! ### Dual Riesz-Kantorovich formulas

The **dual** Riesz-Kantorovich formulas are companions to those above: instead
of computing the lattice operations of varying operators at a fixed positive
element of `X`, they fix a positive operator `f : X → Y` and describe `f`
applied to a lattice expression in `X` (`x⁺`, `x ⊔ y`, `|x|`, ...) as a
supremum or infimum taken over the order interval `[0, f]` of operators
dominated by `f`.
-/

/-! #### Witness operator construction (Aliprantis–Burkinshaw, Theorem 1.22)

For a positive operator `f` and a positive element `x₀`, we build an operator
`wit f x₀` with `0 ≤ wit f x₀ ≤ f`, equal to `f` at `x₀`, and vanishing on
elements disjoint from `x₀`. Concretely we set
`wit f x₀ y = sup_n f (y ⊓ n • x₀)` on the positive cone and extend linearly. -/

omit [IsOrderComplete Y] in
private lemma f_mono_of_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) : Monotone f.toLinearMap :=
  Positive.monotone_iff.mpr fun y hy => by
    have := le_iff.mp hf y hy; simpa using this

omit [IsOrderComplete Y] in
private lemma f_apply_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {y : X} (hy : 0 ≤ y) : 0 ≤ f y := by
  have := le_iff.mp hf y hy; simpa using this

/-- The value of the witness operator on the positive cone:
`witFun f x₀ y = sup_n f (y ⊓ n • x₀)`. Defaults to `0` outside the regime where
the supremum exists. -/
private noncomputable def witFun (f : OrderBoundedHom X Y) (x₀ y : X) : Y := by
  classical
  exact if h : ∃ s : Y, IsLUB
      (Set.range fun n : ℕ => f (y ⊓ n • x₀)) s then h.choose else 0

private lemma witFun_isLUB {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (_hx₀ : 0 ≤ x₀) (_hy : 0 ≤ y) :
    IsLUB (Set.range fun n : ℕ => f (y ⊓ n • x₀)) (witFun f x₀ y) := by
  have hex : ∃ s : Y, IsLUB (Set.range fun n : ℕ => f (y ⊓ n • x₀)) s := by
    refine IsOrderComplete.isLUB_of_bddAbove ⟨f y, ?_⟩ ⟨_, 0, rfl⟩
    rintro _ ⟨n, rfl⟩
    exact f_mono_of_nonneg hf inf_le_left
  simp only [witFun]; rw [dif_pos hex]; exact hex.choose_spec

private lemma witFun_le_f {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : witFun f x₀ y ≤ f y := by
  apply (witFun_isLUB hf hx₀ hy).2
  rintro _ ⟨n, rfl⟩
  exact f_mono_of_nonneg hf inf_le_left

private lemma witFun_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : 0 ≤ witFun f x₀ y := by
  refine (witFun_isLUB hf hx₀ hy).1 ⟨0, ?_⟩
  change f (y ⊓ (0 : ℕ) • x₀) = 0
  rw [zero_nsmul, inf_of_le_right hy]
  exact map_zero f.toLinearMap

private lemma witFun_eq_at {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witFun f x₀ x₀ = f x₀ := by
  refine le_antisymm (witFun_le_f hf hx₀ hx₀) ?_
  refine (witFun_isLUB hf hx₀ hx₀).1 ⟨1, ?_⟩
  change f (x₀ ⊓ (1 : ℕ) • x₀) = f x₀
  rw [one_nsmul, inf_idem]

private lemma witFun_zero_of_disjoint {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) (hd : y ⊓ x₀ = 0) :
    witFun f x₀ y = 0 := by
  have hyn : ∀ n : ℕ, y ⊓ n • x₀ = 0 := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, inf_of_le_right hy]
    | succ n ih =>
      have hle : y ⊓ (n + 1) • x₀ ≤ y ⊓ (n • x₀) + y ⊓ x₀ := by
        rw [succ_nsmul]
        exact inf_le_inf_add_inf_of_nonneg y (n • x₀) x₀ hy
          (nsmul_nonneg hx₀ n) hx₀
      rw [ih, hd, add_zero] at hle
      exact le_antisymm hle (le_inf hy (nsmul_nonneg hx₀ (n + 1)))
  refine le_antisymm ?_ (witFun_nonneg hf hx₀ hy)
  apply (witFun_isLUB hf hx₀ hy).2
  rintro _ ⟨n, rfl⟩
  change f (y ⊓ n • x₀) ≤ 0
  rw [hyn n]
  exact (map_zero f.toLinearMap).le

private lemma witFun_add {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y₁ y₂ : X}
    (hx₀ : 0 ≤ x₀) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    witFun f x₀ (y₁ + y₂) = witFun f x₀ y₁ + witFun f x₀ y₂ := by
  refine le_antisymm ?_ ?_
  · apply (witFun_isLUB hf hx₀ (add_nonneg hy₁ hy₂)).2
    rintro _ ⟨n, rfl⟩
    have hznn : 0 ≤ (y₁ + y₂) ⊓ n • x₀ :=
      le_inf (add_nonneg hy₁ hy₂) (nsmul_nonneg hx₀ n)
    have hzy : (y₁ + y₂) ⊓ n • x₀ ≤ y₁ + y₂ := inf_le_left
    obtain ⟨z₁, z₂, hz₁nn, hz₁y₁, hz₂nn, hz₂y₂, hzeq⟩ :=
      riesz_decomposition (x := (y₁ + y₂) ⊓ n • x₀) y₁ y₂ hznn hy₁ hy₂ hzy
    have hz_le : (y₁ + y₂) ⊓ n • x₀ ≤ n • x₀ := inf_le_right
    have hz₁_nx : z₁ ≤ n • x₀ :=
      ((le_add_of_nonneg_right hz₂nn).trans hzeq.symm.le).trans hz_le
    have hz₂_nx : z₂ ≤ n • x₀ :=
      ((le_add_of_nonneg_left hz₁nn).trans hzeq.symm.le).trans hz_le
    have hz₁_inf : z₁ ≤ y₁ ⊓ n • x₀ := le_inf hz₁y₁ hz₁_nx
    have hz₂_inf : z₂ ≤ y₂ ⊓ n • x₀ := le_inf hz₂y₂ hz₂_nx
    calc f ((y₁ + y₂) ⊓ n • x₀)
        = f (z₁ + z₂) := by rw [hzeq]
      _ = f z₁ + f z₂ := map_add f.toLinearMap z₁ z₂
      _ ≤ f (y₁ ⊓ n • x₀) + f (y₂ ⊓ n • x₀) :=
          add_le_add (f_mono_of_nonneg hf hz₁_inf) (f_mono_of_nonneg hf hz₂_inf)
      _ ≤ witFun f x₀ y₁ + witFun f x₀ y₂ :=
          add_le_add ((witFun_isLUB hf hx₀ hy₁).1 ⟨n, rfl⟩)
            ((witFun_isLUB hf hx₀ hy₂).1 ⟨n, rfl⟩)
  · have step1 : ∀ n m : ℕ,
        f (y₁ ⊓ n • x₀) + f (y₂ ⊓ m • x₀) ≤ witFun f x₀ (y₁ + y₂) := by
      intro n m
      have hsum : (y₁ ⊓ n • x₀) + (y₂ ⊓ m • x₀) ≤ (y₁ + y₂) ⊓ ((n + m) • x₀) := by
        refine le_inf (add_le_add inf_le_left inf_le_left) ?_
        rw [add_nsmul]; exact add_le_add inf_le_right inf_le_right
      calc f (y₁ ⊓ n • x₀) + f (y₂ ⊓ m • x₀)
          = f ((y₁ ⊓ n • x₀) + (y₂ ⊓ m • x₀)) :=
            (map_add f.toLinearMap _ _).symm
        _ ≤ f ((y₁ + y₂) ⊓ (n + m) • x₀) := f_mono_of_nonneg hf hsum
        _ ≤ witFun f x₀ (y₁ + y₂) :=
            (witFun_isLUB hf hx₀ (add_nonneg hy₁ hy₂)).1 ⟨n + m, rfl⟩
    have step2 : ∀ m : ℕ,
        witFun f x₀ y₁ + f (y₂ ⊓ m • x₀) ≤ witFun f x₀ (y₁ + y₂) := by
      intro m
      have hub : witFun f x₀ (y₁ + y₂) - f (y₂ ⊓ m • x₀) ∈
          upperBounds (Set.range fun n : ℕ => f (y₁ ⊓ n • x₀)) := by
        rintro _ ⟨n, rfl⟩
        exact le_sub_iff_add_le.mpr (step1 n m)
      exact le_sub_iff_add_le.mp ((witFun_isLUB hf hx₀ hy₁).2 hub)
    have hub : witFun f x₀ (y₁ + y₂) - witFun f x₀ y₁ ∈
        upperBounds (Set.range fun n : ℕ => f (y₂ ⊓ n • x₀)) := by
      rintro _ ⟨m, rfl⟩
      rw [le_sub_iff_add_le, add_comm]; exact step2 m
    have h := (witFun_isLUB hf hx₀ hy₂).2 hub
    have h2 := le_sub_iff_add_le.mp h
    rwa [add_comm] at h2

/-- The witness linear map for `f` and `x₀ ≥ 0`. -/
private noncomputable def witLin {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    X →ₗ[ℝ] Y := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  exact Positive.extension
    (fun y hy => witFun_nonneg hf hx₀ hy)
    (fun y₁ y₂ hy₁ hy₂ => witFun_add hf hx₀ hy₁ hy₂)

private lemma witLin_apply_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X}
    (hx₀ : 0 ≤ x₀) (hy : 0 ≤ y) : witLin hf hx₀ y = witFun f x₀ y := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  exact Positive.extension_nonneg _ _ hy

private lemma witLin_positive {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    Positive (witLin hf hx₀) := by
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  exact Positive.extension_positive _ _

/-- The witness operator as an `OrderBoundedHom`. -/
private noncomputable def witOp {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    OrderBoundedHom X Y :=
  ⟨witLin hf hx₀, Positive.isOrderBounded (witLin_positive hf hx₀)⟩

private lemma witOp_nonneg {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    (0 : OrderBoundedHom X Y) ≤ witOp hf hx₀ :=
  le_iff.mpr fun y hy => by
    have h := witLin_positive hf hx₀ y hy
    change (0 : Y) ≤ witLin hf hx₀ y at h
    simpa using h

private lemma witOp_le_f {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witOp hf hx₀ ≤ f :=
  le_iff.mpr fun y hy => by
    change witLin hf hx₀ y ≤ f y
    rw [witLin_apply_nonneg hf hx₀ hy]
    exact witFun_le_f hf hx₀ hy

private lemma witOp_apply_self {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ : X} (hx₀ : 0 ≤ x₀) :
    witOp hf hx₀ x₀ = f x₀ := by
  change witLin hf hx₀ x₀ = f x₀
  rw [witLin_apply_nonneg hf hx₀ hx₀, witFun_eq_at hf hx₀]

private lemma witOp_apply_disjoint {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) {x₀ y : X} (hx₀ : 0 ≤ x₀)
    (hy : 0 ≤ y) (hd : y ⊓ x₀ = 0) : witOp hf hx₀ y = 0 := by
  change witLin hf hx₀ y = 0
  rw [witLin_apply_nonneg hf hx₀ hy, witFun_zero_of_disjoint hf hx₀ hy hd]

/-- The witness operator at `x = x⁺ - x⁻` recovers `f x⁺`. -/
private lemma witOp_apply_eq_posPart {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    witOp hf (posPart_nonneg x) x = f x⁺ := by
  have hlin : (witOp hf (posPart_nonneg x)).toLinearMap x =
      (witOp hf (posPart_nonneg x)).toLinearMap x⁺ -
      (witOp hf (posPart_nonneg x)).toLinearMap x⁻ := by
    rw [← map_sub, posPart_sub_negPart]
  change (witOp hf (posPart_nonneg x)).toLinearMap x = f x⁺
  rw [hlin]
  have h1 : (witOp hf (posPart_nonneg x)).toLinearMap x⁺ = f x⁺ :=
    witOp_apply_self hf (posPart_nonneg x)
  have h2 : (witOp hf (posPart_nonneg x)).toLinearMap x⁻ = 0 := by
    apply witOp_apply_disjoint hf (posPart_nonneg x) (negPart_nonneg x)
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero x
  rw [h1, h2, sub_zero]

/-! #### Dual Riesz–Kantorovich theorems -/

/-- **Dual Riesz-Kantorovich for the positive part.** For a positive order
bounded operator `f : X → Y` and an arbitrary `x : X`, the value `f x⁺` is the
supremum of `g x` taken over all order bounded operators `g` with `0 ≤ g ≤ f`.
-/
theorem isLUB_apply_posPart {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x}
      (f x⁺) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have hg_neg : 0 ≤ g x⁻ := f_apply_nonneg hg0 (negPart_nonneg x)
    have key : g x = g x⁺ - g x⁻ := by
      change g.toLinearMap x = g.toLinearMap x⁺ - g.toLinearMap x⁻
      rw [← map_sub, posPart_sub_negPart]
    rw [key]
    exact (sub_le_self _ hg_neg).trans (le_iff.mp hgf x⁺ (posPart_nonneg x))
  · intro u hu
    have hwit_in :
        witOp hf (posPart_nonneg x) x ∈
          {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x} :=
      ⟨witOp hf (posPart_nonneg x), witOp_nonneg hf (posPart_nonneg x),
        witOp_le_f hf (posPart_nonneg x), rfl⟩
    have hub := hu hwit_in
    rwa [witOp_apply_eq_posPart hf x] at hub

/-- **Dual Riesz-Kantorovich for the negative part.** For a positive order
bounded operator `f` and `x : X`, `f x⁻ = sup {-(g x) | 0 ≤ g ≤ f}`. -/
theorem isLUB_apply_negPart {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = -(g x)}
      (f x⁻) := by
  have hpp := isLUB_apply_posPart hf (-x)
  rw [posPart_neg] at hpp
  have hgneg : ∀ g : OrderBoundedHom X Y, g (-x) = -(g x) := fun g => by
    change g.toLinearMap (-x) = -(g.toLinearMap x); rw [map_neg]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have hmem : g (-x) ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g (-x)} :=
      ⟨g, hg0, hgf, rfl⟩
    have h1 := hpp.1 hmem
    rw [hgneg] at h1; exact h1
  · intro u hu
    apply hpp.2
    rintro _ ⟨g, hg0, hgf, rfl⟩
    have hin : -(g x) ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = -(g x)} :=
      ⟨g, hg0, hgf, rfl⟩
    have h1 := hu hin
    rw [hgneg]; exact h1

/-- **Dual Riesz-Kantorovich for the supremum.** For a positive order bounded
operator `f` and `x y : X`,
`f (x ⊔ y) = sup {g x + (f - g) y | 0 ≤ g ≤ f}`. -/
theorem isLUB_apply_sup {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x y : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y,
        0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y}
      (f (x ⊔ y)) := by
  -- Use x ⊔ y = y + (x - y)⁺
  have hxy : (x ⊔ y) = y + (x - y)⁺ := by
    rw [posPart_def, add_sup, add_sub_cancel, add_zero, sup_comm]
  have hfxy : f (x ⊔ y) = f y + f ((x - y)⁺) := by
    rw [hxy]; exact map_add_val f y _
  rw [hfxy]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have hgxy : g x + (f - g) y = f y + g (x - y) := by
      rw [sub_apply, map_sub_val g]; abel
    rw [hgxy]
    have hgneg : 0 ≤ g (x - y)⁻ := f_apply_nonneg hg0 (negPart_nonneg _)
    have hgsplit : g (x - y) = g (x - y)⁺ - g (x - y)⁻ := by
      change g.toLinearMap (x - y) = g.toLinearMap (x - y)⁺ - g.toLinearMap (x - y)⁻
      rw [← map_sub, posPart_sub_negPart]
    have h1 : g (x - y) ≤ g (x - y)⁺ := by rw [hgsplit]; exact sub_le_self _ hgneg
    have h2 : g (x - y)⁺ ≤ f (x - y)⁺ := le_iff.mp hgf _ (posPart_nonneg _)
    exact add_le_add (le_refl (f y)) (h1.trans h2)
  · intro u hu
    set g := witOp hf (posPart_nonneg (x - y)) with hgdef
    have hg0 : (0 : OrderBoundedHom X Y) ≤ g := witOp_nonneg hf _
    have hgf : g ≤ f := witOp_le_f hf _
    have hgxy : g (x - y) = f (x - y)⁺ := witOp_apply_eq_posPart hf (x - y)
    have hin : g x + (f - g) y ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y} :=
      ⟨g, hg0, hgf, rfl⟩
    have hub := hu hin
    have hcalc : g x + (f - g) y = f y + f (x - y)⁺ := by
      have h0 : g x + (f - g) y = f y + g (x - y) := by
        rw [sub_apply, map_sub_val g]; abel
      rw [h0, hgxy]
    rw [hcalc] at hub; exact hub

/-- **Dual Riesz-Kantorovich for the infimum.** For a positive order bounded
operator `f` and `x y : X`,
`f (x ⊓ y) = inf {g x + (f - g) y | 0 ≤ g ≤ f}`. -/
theorem isGLB_apply_inf {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x y : X) :
    IsGLB {w | ∃ g : OrderBoundedHom X Y,
        0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y}
      (f (x ⊓ y)) := by
  -- Use x ⊓ y = x + y - x ⊔ y. The set is symmetric: replacing g by f - g sends
  -- g x + (f-g) y to (f-g) x + g y, and the sum (g x + (f-g) y) + ((f-g) x + g y)
  -- = f x + f y. So the inf set is the reflection of the sup set about (f x + f y)/2.
  set S : Set Y := {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x + (f - g) y}
  set c : Y := f x + f y with hcdef
  have hsym : ∀ w ∈ S, c - w ∈ S := by
    rintro _ ⟨g, hg0, hgf, rfl⟩
    refine ⟨f - g, sub_nonneg.mpr hgf, sub_le_self f hg0, ?_⟩
    change c - (g x + (f - g) y) = (f - g) x + (f - (f - g)) y
    rw [sub_sub_cancel, sub_apply, sub_apply]
    change f x + f y - (g x + (f y - g y)) = (f x - g x) + g y
    abel
  have hsup : IsLUB S (f (x ⊔ y)) := isLUB_apply_sup hf x y
  have hadd : f (x ⊓ y) + f (x ⊔ y) = c := by
    change f.toLinearMap (x ⊓ y) + f.toLinearMap (x ⊔ y) = f.toLinearMap x + f.toLinearMap y
    rw [← map_add f.toLinearMap, inf_add_sup, map_add]
  have hinf : f (x ⊓ y) = c - f (x ⊔ y) := eq_sub_of_add_eq hadd
  rw [hinf]
  refine ⟨?_, ?_⟩
  · intro w hw
    exact sub_le_comm.mp (hsup.1 (hsym w hw))
  · intro b hb
    have hub : ∀ w ∈ S, w ≤ c - b := fun w hw =>
      le_sub_comm.mp (hb (hsym w hw))
    exact le_sub_comm.mpr (hsup.2 hub)


/-- **Dual Riesz-Kantorovich for the modulus.** For a positive order bounded
operator `f` and `x : X`,
`f |x| = sup {g x - (f - g) x | 0 ≤ g ≤ f}`. -/
theorem isLUB_apply_abs {f : OrderBoundedHom X Y}
    (hf : (0 : OrderBoundedHom X Y) ≤ f) (x : X) :
    IsLUB {w | ∃ g : OrderBoundedHom X Y,
        0 ≤ g ∧ g ≤ f ∧ w = g x - (f - g) x}
      (f |x|) := by
  -- |x| = x⁺ + x⁻ and g x - (f - g) x = 2 g x - f x. Reduce to posPart formula.
  have habs : |x| = x⁺ + x⁻ := (posPart_add_negPart x).symm
  -- Note: x = x⁺ - x⁻, so f x = f x⁺ - f x⁻, and 2 f x⁺ - f x = f x⁺ + f x⁻ = f |x|.
  have hfabs : f |x| = 2 • f x⁺ - f x := by
    rw [habs, map_add_val]
    have : f x = f x⁺ - f x⁻ := by rw [← map_sub_val, posPart_sub_negPart]
    rw [this]; abel
  rw [hfabs]
  have hpp := isLUB_apply_posPart hf x
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg0, hgf, rfl⟩
    have heq : g x - (f - g) x = 2 • g x - f x := by
      rw [sub_apply, two_smul]; abel
    rw [heq]
    have hgx : g x ≤ f x⁺ := hpp.1 ⟨g, hg0, hgf, rfl⟩
    have h2 : 2 • g x ≤ 2 • f x⁺ := by
      rw [two_smul, two_smul]; exact add_le_add hgx hgx
    exact sub_le_sub_right h2 _
  · intro u hu
    set g := witOp hf (posPart_nonneg x) with hgdef
    have hg0 : (0 : OrderBoundedHom X Y) ≤ g := witOp_nonneg hf _
    have hgf : g ≤ f := witOp_le_f hf _
    have hgx : g x = f x⁺ := witOp_apply_eq_posPart hf x
    have hin : g x - (f - g) x ∈
        {w | ∃ g : OrderBoundedHom X Y, 0 ≤ g ∧ g ≤ f ∧ w = g x - (f - g) x} :=
      ⟨g, hg0, hgf, rfl⟩
    have hub := hu hin
    have heq : g x - (f - g) x = 2 • f x⁺ - f x := by
      rw [sub_apply, hgx, two_smul]; abel
    rw [heq] at hub; exact hub

/-- The supremum of a non-empty upward-directed bounded above set of order
bounded operators exists and is computed pointwise on the positive cone:
its value at any positive `x` is the supremum of `{g x | g ∈ S}`. -/
theorem isLUB_of_directedOn
    {S : Set (OrderBoundedHom X Y)} (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (hbdd : BddAbove S) :
    ∃ f : OrderBoundedHom X Y, IsLUB S f ∧
      ∀ {x : X}, 0 ≤ x →
        IsLUB ((fun g : OrderBoundedHom X Y => g x) '' S) (f x) := by
  classical
  haveI : IsVLArchimedean Y := IsVLArchimedean_of_isSigmaOrderComplete
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨h, hh⟩ := hbdd
  have aux : ∀ {x : X}, 0 ≤ x →
      ∃ s : Y, IsLUB ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) s := by
    intro x hx
    refine IsOrderComplete.isLUB_of_bddAbove
      ⟨h x - g₀ x, ?_⟩ ⟨0, g₀, hg₀, sub_self _⟩
    rintro _ ⟨g, hg, rfl⟩
    exact sub_le_sub_right (hh hg x hx) _
  let σ : X → Y := fun x => if hx : 0 ≤ x then (aux hx).choose else 0
  have σ_isLUB : ∀ {x : X} (hx : 0 ≤ x),
      IsLUB ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) (σ x) := by
    intro x hx
    change IsLUB _ (if hx : 0 ≤ x then (aux hx).choose else 0)
    rw [dif_pos hx]
    exact (aux hx).choose_spec
  have σ_nn : ∀ x, 0 ≤ x → 0 ≤ σ x := fun x hx => by
    have h1 := (σ_isLUB hx).1 ⟨g₀, hg₀, sub_self _⟩
    simpa using h1
  have σ_add : ∀ x y, 0 ≤ x → 0 ≤ y → σ (x + y) = σ x + σ y := by
    intro x y hx hy
    refine le_antisymm ?_ ?_
    · apply (σ_isLUB (add_nonneg hx hy)).2
      rintro _ ⟨g, hg, rfl⟩
      change g (x + y) - g₀ (x + y) ≤ σ x + σ y
      have hgxy : g (x + y) - g₀ (x + y) = (g x - g₀ x) + (g y - g₀ y) := by
        rw [map_add_val g, map_add_val g₀]; abel
      rw [hgxy]
      exact add_le_add ((σ_isLUB hx).1 ⟨g, hg, rfl⟩)
        ((σ_isLUB hy).1 ⟨g, hg, rfl⟩)
    · have step1 : ∀ w₁ ∈ ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S),
          ∀ w₂ ∈ ((fun g : OrderBoundedHom X Y => g y - g₀ y) '' S),
          w₁ + w₂ ≤ σ (x + y) := by
        rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
        obtain ⟨g, hg, hg₁g, hg₂g⟩ := hdir g₁ hg₁ g₂ hg₂
        have h1 : g₁ x - g₀ x ≤ g x - g₀ x :=
          sub_le_sub_right (hg₁g x hx) _
        have h2 : g₂ y - g₀ y ≤ g y - g₀ y :=
          sub_le_sub_right (hg₂g y hy) _
        have h3 : (g x - g₀ x) + (g y - g₀ y) = g (x + y) - g₀ (x + y) := by
          rw [map_add_val g, map_add_val g₀]; abel
        calc g₁ x - g₀ x + (g₂ y - g₀ y)
            ≤ (g x - g₀ x) + (g y - g₀ y) := add_le_add h1 h2
          _ = g (x + y) - g₀ (x + y) := h3
          _ ≤ σ (x + y) :=
            (σ_isLUB (add_nonneg hx hy)).1 ⟨g, hg, rfl⟩
      have step2 : ∀ w₂ ∈ ((fun g : OrderBoundedHom X Y => g y - g₀ y) '' S),
          σ x + w₂ ≤ σ (x + y) := by
        intro w₂ hw₂
        have hub : σ (x + y) - w₂ ∈ upperBounds
            ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) :=
          fun w₁ hw₁ => le_sub_iff_add_le.mpr (step1 w₁ hw₁ w₂ hw₂)
        exact le_sub_iff_add_le.mp ((σ_isLUB hx).2 hub)
      have hub2 : σ (x + y) - σ x ∈ upperBounds
          ((fun g : OrderBoundedHom X Y => g y - g₀ y) '' S) := by
        intro w₂ hw₂
        rw [le_sub_iff_add_le, add_comm]
        exact step2 w₂ hw₂
      have h3 := (σ_isLUB hy).2 hub2
      have := le_sub_iff_add_le.mp h3
      rwa [add_comm] at this
  let T : X →ₗ[ℝ] Y := Positive.extension σ_nn σ_add
  have hT_pos : Positive T := Positive.extension_positive σ_nn σ_add
  have hT_apply : ∀ {x : X}, 0 ≤ x → T x = σ x :=
    fun {x} hx => Positive.extension_nonneg σ_nn σ_add hx
  let Tob : OrderBoundedHom X Y := ⟨T, hT_pos.isOrderBounded⟩
  refine ⟨Tob + g₀, ?_, ?_⟩
  · refine ⟨fun g hg x hx => ?_, fun k hk x hx => ?_⟩
    · rw [add_apply']
      change g x ≤ T x + g₀ x
      rw [hT_apply hx]
      have : g x - g₀ x ≤ σ x := (σ_isLUB hx).1 ⟨g, hg, rfl⟩
      exact sub_le_iff_le_add.mp this
    · rw [add_apply']
      change T x + g₀ x ≤ k x
      rw [hT_apply hx]
      have hub : k x - g₀ x ∈ upperBounds
          ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) := by
        rintro _ ⟨g, hg, rfl⟩
        exact sub_le_sub_right (hk hg x hx) _
      have h1 := (σ_isLUB hx).2 hub
      exact le_sub_iff_add_le.mp h1
  · intro x hx
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      rw [add_apply']
      change g x ≤ T x + g₀ x
      rw [hT_apply hx]
      have : g x - g₀ x ≤ σ x := (σ_isLUB hx).1 ⟨g, hg, rfl⟩
      exact sub_le_iff_le_add.mp this
    · intro u hu
      rw [add_apply']
      change T x + g₀ x ≤ u
      rw [hT_apply hx]
      have hub : u - g₀ x ∈ upperBounds
          ((fun g : OrderBoundedHom X Y => g x - g₀ x) '' S) := by
        rintro _ ⟨g, hg, rfl⟩
        exact sub_le_sub_right (hu ⟨g, hg, rfl⟩) _
      have h1 := (σ_isLUB hx).2 hub
      exact le_sub_iff_add_le.mp h1

/-- When the codomain is order complete, the space of order bounded
operators is order complete. -/
instance instIsOrderComplete :
    IsOrderComplete (OrderBoundedHom X Y) := by
  refine ⟨fun {S} hbdd hne => ?_⟩
  classical
  let S' : Set (OrderBoundedHom X Y) :=
    {f | ∃ F : Finset (OrderBoundedHom X Y), ∃ hF : F.Nonempty,
      ↑F ⊆ S ∧ f = F.sup' hF id}
  have hS'_ne : S'.Nonempty := by
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, {g}, Finset.singleton_nonempty g, ?_, ?_⟩
    · simpa using hg
    · simp
  have hS'_bdd : BddAbove S' := by
    obtain ⟨h, hh⟩ := hbdd
    refine ⟨h, ?_⟩
    rintro _ ⟨F, hF, hFS, rfl⟩
    exact Finset.sup'_le hF id (fun g hgF => hh (hFS hgF))
  have hS'_dir : DirectedOn (· ≤ ·) S' := by
    rintro _ ⟨F₁, hF₁, hF₁S, rfl⟩ _ ⟨F₂, hF₂, hF₂S, rfl⟩
    have hU : (F₁ ∪ F₂).Nonempty := hF₁.mono Finset.subset_union_left
    refine ⟨(F₁ ∪ F₂).sup' hU id, ⟨F₁ ∪ F₂, hU, ?_, rfl⟩, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_union.mp hg with h | h
      · exact hF₁S h
      · exact hF₂S h
    · exact Finset.sup'_le hF₁ id (fun g hg =>
        Finset.le_sup' id (Finset.mem_union_left _ hg))
    · exact Finset.sup'_le hF₂ id (fun g hg =>
        Finset.le_sup' id (Finset.mem_union_right _ hg))
  obtain ⟨f, hLUB, _⟩ := isLUB_of_directedOn hS'_ne hS'_dir hS'_bdd
  refine ⟨f, ?_, ?_⟩
  · intro g hg
    exact hLUB.1 ⟨{g}, Finset.singleton_nonempty g,
      by simpa using hg, by simp⟩
  · intro k hk
    apply hLUB.2
    rintro _ ⟨F, hF, hFS, rfl⟩
    exact Finset.sup'_le hF id (fun g hgF => hk (hFS hgF))

end OrderBoundedHom
