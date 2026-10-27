/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.AMSpace.Kakutani
import BanLat.ComplexBanachLattice.Basic

/-!
# Complex modulus in uniformly complete real vector lattices

This file introduces the **complex modulus** associated to each pair `(x, y)` of
elements of a **uniformly complete (real) vector lattice** `E`, defined as
`|(x, y)| := sup{cos(θ)x+sin(θ)y | θ ∈ ℝ} ∈ E₊`.

This is done first for `x, y ∈ ℝ`, where `|(x, y)| = sqrt(x^2+y^2)`, then pointwise
for `f, g ∈ C(K, ℝ)`. Kakutani's representation theorem is used to prove that such a
supremum exists for any two elements of a uniformly complete real vector lattice.

Usual properties of this modulus are also derived.
-/

/-- The Euclidean norm is attained by rotation through the complex argument. -/
private theorem sqrt_sq_add_sq_eq_rotation_arg (a b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2) =
      Real.cos (Complex.arg ⟨a, b⟩) * a + Real.sin (Complex.arg ⟨a, b⟩) * b := by
  rw [← Complex.norm_eq_sqrt_sq_add_sq (⟨a, b⟩ : ℂ)]
  change ‖(⟨a, b⟩ : ℂ)‖ =
    Real.cos (Complex.arg ⟨a, b⟩) * (⟨a, b⟩ : ℂ).re +
      Real.sin (Complex.arg ⟨a, b⟩) * (⟨a, b⟩ : ℂ).im
  rw [← Complex.norm_mul_cos_arg (⟨a, b⟩ : ℂ),
    ← Complex.norm_mul_sin_arg (⟨a, b⟩ : ℂ)]
  calc
    ‖(⟨a, b⟩ : ℂ)‖ = ‖(⟨a, b⟩ : ℂ)‖ * 1 := (mul_one _).symm
    _ = ‖(⟨a, b⟩ : ℂ)‖ *
        (Real.cos (Complex.arg ⟨a, b⟩) ^ 2 + Real.sin (Complex.arg ⟨a, b⟩) ^ 2) := by
      rw [Real.cos_sq_add_sin_sq]
    _ = _ := by ring

/-- The Euclidean norm is the least upper bound of all real rotations. -/
private theorem real_rotationRange_isLUB (a b : ℝ) :
    IsLUB (Set.range fun θ : ℝ ↦ Real.cos θ * a + Real.sin θ * b)
      (Real.sqrt (a ^ 2 + b ^ 2)) := by
  constructor
  · rintro _ ⟨θ, rfl⟩
    apply Real.le_sqrt_of_sq_le
    calc
      (Real.cos θ * a + Real.sin θ * b) ^ 2 ≤
          (Real.cos θ * a + Real.sin θ * b) ^ 2 +
            (Real.sin θ * a - Real.cos θ * b) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (a ^ 2 + b ^ 2) := by ring
      _ = a ^ 2 + b ^ 2 := by rw [Real.cos_sq_add_sin_sq, one_mul]
  · intro u hu
    have h := hu ⟨Complex.arg ⟨a, b⟩, rfl⟩
    rw [sqrt_sq_add_sq_eq_rotation_arg]
    exact h

/-- The pointwise Euclidean modulus of two real-valued continuous functions. -/
noncomputable def continuousMapModulus {K : Type*} [TopologicalSpace K]
    (f g : C(K, ℝ)) : C(K, ℝ) where
  toFun t := Real.sqrt (f t ^ 2 + g t ^ 2)
  continuous_toFun := Real.continuous_sqrt.comp ((f.continuous.pow 2).add (g.continuous.pow 2))

/-- The pointwise modulus is the least upper bound of all rotations. -/
theorem continuousMapModulus_isLUB {K : Type*} [TopologicalSpace K]
    (f g : C(K, ℝ)) :
    IsLUB (Set.range fun θ : ℝ ↦ Real.cos θ • f + Real.sin θ • g)
      (continuousMapModulus f g) := by
  constructor
  · rintro _ ⟨θ, rfl⟩ t
    exact (real_rotationRange_isLUB (f t) (g t)).1 ⟨θ, rfl⟩
  · intro u hu t
    apply (real_rotationRange_isLUB (f t) (g t)).2
    rintro _ ⟨θ, rfl⟩
    exact (hu ⟨θ, rfl⟩) t

namespace VectorLattice

section Algebraic

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]

/-- Every upper bound for all rotations is nonnegative. -/
private theorem nonneg_of_upperBound_rotationRange {x y u : E}
    (hu : u ∈ upperBounds (rotationRange x y)) : 0 ≤ u := by
  exact (abs_nonneg x).trans
    (le_sup_left.trans (sup_abs_le_of_mem_upperBounds_rotationRange hu))

/-- Every pair in a uniformly complete vector lattice has a complex modulus. -/
private theorem exists_isLUB_rotationRange [IsUniformlyCompleteVectorLattice E]
    (x y : E) : ∃ z, IsLUB (rotationRange x y) z := by
  let e := |x| + |y|
  have he : 0 ≤ e := add_nonneg (abs_nonneg x) (abs_nonneg y)
  by_cases hzero : e = 0
  · have hxabs : |x| = 0 := le_antisymm
      (le_trans (le_add_of_nonneg_right (abs_nonneg y)) (hzero.le)) (abs_nonneg x)
    have hyabs : |y| = 0 := le_antisymm
      (le_trans (le_add_of_nonneg_left (abs_nonneg x)) (hzero.le)) (abs_nonneg y)
    have hx0 : x = 0 := (abs_eq_zero_iff_zero x).mp hxabs
    have hy0 : y = 0 := (abs_eq_zero_iff_zero y).mp hyabs
    subst x
    subst y
    refine ⟨0, ?_⟩
    constructor
    · rintro _ ⟨θ, rfl⟩
      simp
    · intro u hu
      simpa using hu ⟨0, rfl⟩
  · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hzero)
    letI : NormedAddCommGroup ↥(OrderIdeal.principal e) :=
      OrderIdeal.principalNormedAddCommGroup e
    letI : Lattice ↥(OrderIdeal.principal e) := OrderIdeal.instLatticePrincipal e
    letI : IsOrderedAddMonoid ↥(OrderIdeal.principal e) :=
      OrderIdeal.instIsOrderedAddMonoidPrincipal e
    letI : AMSpaceWithUnit ↥(OrderIdeal.principal e) :=
      OrderIdeal.principalAMSpaceWithUnit he
        (IsUniformlyCompleteVectorLattice.complete_principal e hepos)
    let T := OrderIdeal.principalKakutaniEquiv hepos
    have hx : x ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he]
      exact le_add_of_nonneg_right (abs_nonneg y)
    have hy : y ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he]
      exact le_add_of_nonneg_left (abs_nonneg x)
    let f := T ⟨x, hx⟩
    let g := T ⟨y, hy⟩
    let z := T.symm (continuousMapModulus f g)
    refine ⟨z, ?_⟩
    constructor
    · rintro _ ⟨θ, rfl⟩
      let r : ↥(OrderIdeal.principal e) :=
        Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
          Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))
      have hrmap : T r = Real.cos θ • f + Real.sin θ • g := by
        change T.toLinearIsometryEquiv
            (Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
              Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))) =
          Real.cos θ • T.toLinearIsometryEquiv ⟨x, hx⟩ +
            Real.sin θ • T.toLinearIsometryEquiv ⟨y, hy⟩
        rw [map_add, map_smul, map_smul]
      have hfun := (continuousMapModulus_isLUB f g).1 ⟨θ, rfl⟩
      change Real.cos θ • f + Real.sin θ • g ≤ continuousMapModulus f g at hfun
      rw [← hrmap] at hfun
      have hback := T.symm.toOrderIso.monotone hfun
      change T.symm (T r) ≤ T.symm (continuousMapModulus f g) at hback
      have hleft : T.symm (T r) = r := by
        change T.toLinearIsometryEquiv.symm (T.toLinearIsometryEquiv r) = r
        exact T.toLinearIsometryEquiv.symm_apply_apply r
      rw [hleft] at hback
      exact hback
    · intro u hu
      have hu0 : 0 ≤ u := nonneg_of_upperBound_rotationRange hu
      have huv0 : 0 ≤ u ⊓ e := le_inf hu0 he
      have huv_mem : u ⊓ e ∈ OrderIdeal.principal e := by
        rw [OrderIdeal.mem_principal]
        refine ⟨1, zero_le_one, ?_⟩
        rw [one_smul, abs_of_nonneg huv0, abs_of_nonneg he]
        exact inf_le_right
      let v : ↥(OrderIdeal.principal e) := ⟨u ⊓ e, huv_mem⟩
      have hTv : T v ∈ upperBounds
          (Set.range fun θ : ℝ ↦ Real.cos θ • f + Real.sin θ • g) := by
        rintro _ ⟨θ, rfl⟩
        let r : ↥(OrderIdeal.principal e) :=
          Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
            Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))
        have hr : r ≤ v := by
          change Real.cos θ • x + Real.sin θ • y ≤ u ⊓ e
          exact le_inf (hu ⟨θ, rfl⟩) (rotation_le_abs_add_abs x y θ)
        have hmap := T.toOrderIso.monotone hr
        change T r ≤ T v at hmap
        have hrmap : T r = Real.cos θ • f + Real.sin θ • g := by
          change T.toLinearIsometryEquiv
              (Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
                Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))) =
            Real.cos θ • T.toLinearIsometryEquiv ⟨x, hx⟩ +
              Real.sin θ • T.toLinearIsometryEquiv ⟨y, hy⟩
          rw [map_add, map_smul, map_smul]
        rw [hrmap] at hmap
        exact hmap
      have hmod : continuousMapModulus f g ≤ T v :=
        (continuousMapModulus_isLUB f g).2 hTv
      have hzv : z ≤ v := by
        have hback := T.symm.toOrderIso.monotone hmod
        change T.symm (continuousMapModulus f g) ≤ v
        change T.symm (continuousMapModulus f g) ≤ T.symm (T v) at hback
        have hright : T.symm (T v) = v := by
          change T.toLinearIsometryEquiv.symm (T.toLinearIsometryEquiv v) = v
          exact T.toLinearIsometryEquiv.symm_apply_apply v
        rw [hright] at hback
        exact hback
      calc
        (z : E) ≤ (v : E) := hzv
        _ = u ⊓ e := rfl
        _ ≤ u := inf_le_left

variable [IsUniformlyCompleteVectorLattice E]

/-- The complex modulus associated with a pair in a uniformly complete vector lattice. -/
noncomputable def complexModulus (x y : E) : E :=
  Classical.choose (exists_isLUB_rotationRange x y)

/-- The complex modulus is the least upper bound of all rotations of the pair. -/
theorem complexModulus_isLUB (x y : E) :
    IsLUB (rotationRange x y) (complexModulus x y) := by
  exact Classical.choose_spec (exists_isLUB_rotationRange x y)

/-- The complex modulus is nonnegative. -/
theorem complexModulus_nonneg (x y : E) :
    0 ≤ complexModulus x y := by
  exact nonneg_of_upperBound_rotationRange (complexModulus_isLUB x y).1

/-- The complex modulus of `(x, 0)` is the absolute value of `x`. -/
theorem complexModulus_zero_right (x : E) :
    complexModulus x 0 = |x| := by
  apply le_antisymm
  · apply (complexModulus_isLUB x 0).2
    rintro _ ⟨θ, rfl⟩
    simpa using rotation_le_abs_add_abs x 0 θ
  · have hx : x ≤ complexModulus x 0 := by
      simpa only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] using
        (complexModulus_isLUB x 0).1 ⟨0, rfl⟩
    have hnx : -x ≤ complexModulus x 0 := by
      simpa only [Real.cos_pi, Real.sin_pi, neg_smul, one_smul, zero_smul, add_zero] using
        (complexModulus_isLUB x 0).1 ⟨Real.pi, rfl⟩
    exact abs_le'.mpr ⟨hx, hnx⟩

/-- The complex modulus of `(0, y)` is the absolute value of `y`. -/
theorem complexModulus_zero_left (y : E) :
    complexModulus 0 y = |y| := by
  apply le_antisymm
  · apply (complexModulus_isLUB 0 y).2
    rintro _ ⟨θ, rfl⟩
    simpa using rotation_le_abs_add_abs 0 y θ
  · have hy : y ≤ complexModulus 0 y := by
      simpa only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add] using
        (complexModulus_isLUB 0 y).1 ⟨Real.pi / 2, rfl⟩
    have hny : -y ≤ complexModulus 0 y := by
      simpa only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two,
        zero_smul, neg_smul, one_smul, zero_add] using
        (complexModulus_isLUB 0 y).1 ⟨-(Real.pi / 2), rfl⟩
    exact abs_le'.mpr ⟨hy, hny⟩

/-- Changing the sign of the first component does not change the complex modulus. -/
theorem complexModulus_neg_left (x y : E) :
    complexModulus (-x) y = complexModulus x y := by
  apply (complexModulus_isLUB (-x) y).unique
  rw [rotationRange_neg_left]
  exact complexModulus_isLUB x y

/-- Changing the sign of the second component does not change the complex modulus. -/
theorem complexModulus_neg_right (x y : E) :
    complexModulus x (-y) = complexModulus x y := by
  apply (complexModulus_isLUB x (-y)).unique
  rw [rotationRange_neg_right]
  exact complexModulus_isLUB x y

/-- Interchanging the two components does not change the complex modulus. -/
theorem complexModulus_comm (x y : E) :
    complexModulus x y = complexModulus y x := by
  apply (complexModulus_isLUB x y).unique
  rw [rotationRange_comm]
  exact complexModulus_isLUB y x

/-- The absolute value of the first component is bounded by the complex modulus. -/
theorem abs_le_complexModulus_left (x y : E) :
    |x| ≤ complexModulus x y := by
  exact le_sup_left.trans
    (sup_abs_le_of_mem_upperBounds_rotationRange (complexModulus_isLUB x y).1)

/-- The absolute value of the second component is bounded by the complex modulus. -/
theorem abs_le_complexModulus_right (x y : E) :
    |y| ≤ complexModulus x y := by
  exact le_sup_right.trans
    (sup_abs_le_of_mem_upperBounds_rotationRange (complexModulus_isLUB x y).1)

/-- The complex modulus is bounded by the sum of the component absolute values. -/
theorem complexModulus_le_abs_add_abs (x y : E) :
    complexModulus x y ≤ |x| + |y| := by
  apply (complexModulus_isLUB x y).2
  rintro _ ⟨θ, rfl⟩
  exact rotation_le_abs_add_abs x y θ

/-- The complex modulus is zero exactly when both components are zero. -/
theorem complexModulus_eq_zero_iff (x y : E) :
    complexModulus x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hxabs : |x| = 0 := le_antisymm ((abs_le_complexModulus_left x y).trans_eq h)
      (abs_nonneg x)
    have hyabs : |y| = 0 := le_antisymm ((abs_le_complexModulus_right x y).trans_eq h)
      (abs_nonneg y)
    exact ⟨(abs_eq_zero_iff_zero x).mp hxabs, (abs_eq_zero_iff_zero y).mp hyabs⟩
  · rintro ⟨rfl, rfl⟩
    simpa using complexModulus_zero_right (0 : E)

/-- The complex modulus satisfies the triangle inequality. -/
theorem complexModulus_add_le (x₁ y₁ x₂ y₂ : E) :
    complexModulus (x₁ + x₂) (y₁ + y₂) ≤
      complexModulus x₁ y₁ + complexModulus x₂ y₂ := by
  apply (complexModulus_isLUB (x₁ + x₂) (y₁ + y₂)).2
  exact add_mem_upperBounds_rotationRange
    (complexModulus_isLUB x₁ y₁).1
    (complexModulus_isLUB x₂ y₂).1

/-- The complex modulus satisfies the reversed triangle inequality. -/
theorem abs_complexModulus_sub_complexModulus_le (x₁ y₁ x₂ y₂ : E) :
    |complexModulus x₁ y₁ - complexModulus x₂ y₂| ≤
      complexModulus (x₁ - x₂) (y₁ - y₂) := by
  exact abs_sub_le_of_isLUB_rotationRange
    (complexModulus_isLUB x₁ y₁)
    (complexModulus_isLUB x₂ y₂)
    (complexModulus_isLUB (x₁ - x₂) (y₁ - y₂))

/-- A complex-linear coordinate change scales the complex modulus by its Euclidean norm. -/
theorem complexModulus_linear_transform (a b : ℝ) (x y : E) :
    complexModulus (a • x - b • y) (b • x + a • y) =
      Real.sqrt (a ^ 2 + b ^ 2) • complexModulus x y := by
  apply (complexModulus_isLUB (a • x - b • y) (b • x + a • y)).unique
  have h := isLUB_smul_of_nonneg (Real.sqrt_nonneg (a ^ 2 + b ^ 2))
    (complexModulus_isLUB x y)
  rw [← rotationRange_linear_transform] at h
  exact h

end Algebraic

/-- On real-valued continuous functions, the complex modulus is computed pointwise. -/
@[simp]
theorem complexModulus_apply {K : Type*} [TopologicalSpace K]
    [IsUniformlyCompleteVectorLattice C(K, ℝ)]
    (f g : C(K, ℝ)) (t : K) :
    complexModulus f g t = Real.sqrt (f t ^ 2 + g t ^ 2) := by
  have h : complexModulus f g = continuousMapModulus f g :=
    (complexModulus_isLUB f g).unique (continuousMapModulus_isLUB f g)
  rw [h]
  rfl

section Normed

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E] [IsUniformlyCompleteVectorLattice E]

/-- The norm of the first component is bounded by the norm of the complex modulus. -/
theorem norm_le_norm_complexModulus_left (x y : E) :
    ‖x‖ ≤ ‖complexModulus x y‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (complexModulus_nonneg x y)]
  exact abs_le_complexModulus_left x y

/-- The norm of the second component is bounded by the norm of the complex modulus. -/
theorem norm_le_norm_complexModulus_right (x y : E) :
    ‖y‖ ≤ ‖complexModulus x y‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (complexModulus_nonneg x y)]
  exact abs_le_complexModulus_right x y

/-- The norm of the complex modulus is bounded by the sum of the component norms. -/
theorem norm_complexModulus_le_add_norm (x y : E) :
    ‖complexModulus x y‖ ≤ ‖x‖ + ‖y‖ := by
  calc
    ‖complexModulus x y‖ ≤ ‖|x| + |y|‖ := norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (complexModulus_nonneg x y),
        abs_of_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y))]
      exact complexModulus_le_abs_add_abs x y)
    _ ≤ ‖|x|‖ + ‖|y|‖ := norm_add_le _ _
    _ = ‖x‖ + ‖y‖ := by rw [norm_abs_eq_norm, norm_abs_eq_norm]

end Normed

/-- A real-linear order isomorphism between uniformly complete
vector lattices preserves the complex modulus. -/
private theorem map_complexModulus_of_linearOrderIso
    {E F : Type*}
    [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [VectorLattice E] [IsUniformlyCompleteVectorLattice E]
    [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    [VectorLattice F] [IsUniformlyCompleteVectorLattice F]
    (K : E ≃o F) (hK : IsLinearMap ℝ K) (x y : E) :
    K (complexModulus x y) = complexModulus (K x) (K y) := by
  symm
  apply (complexModulus_isLUB (K x) (K y)).unique
  constructor
  · rintro _ ⟨θ, rfl⟩
    change Real.cos θ • K x + Real.sin θ • K y ≤ K (complexModulus x y)
    rw [← hK.map_smul, ← hK.map_smul, ← hK.map_add]
    exact K.monotone ((complexModulus_isLUB x y).1 ⟨θ, rfl⟩)
  · intro u hu
    rw [← K.apply_symm_apply u, map_le_map_iff K]
    apply (complexModulus_isLUB x y).2
    rintro _ ⟨θ, rfl⟩
    rw [K.le_symm_apply, hK.map_add, hK.map_smul, hK.map_smul]
    exact hu ⟨θ, rfl⟩

end VectorLattice

open scoped ComplexStarModule

namespace ComplexVectorLattice

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [BanachLattice (selfAdjoint Z)]

/-- A complex star-module whose self-adjoint part is a Banach lattice inherits a complex
vector lattice structure when real scalar multiplication agrees with the ambient scalar action. -/
@[reducible]
noncomputable def ofSelfAdjointBanachLattice
    (coe_smul :
      letI : SMul ℝ (selfAdjoint Z) := VectorLattice.toModule.toSMul
      ∀ (r : ℝ) (x : selfAdjoint Z),
        ((r • x : selfAdjoint Z) : Z) = r • (x : Z)) :
    ComplexVectorLattice Z := by
  letI : IsUniformlyCompleteVectorLattice (selfAdjoint Z) :=
    isUniformlyCompleteVectorLattice_of_banachLattice _
  exact
    { coe_smul := coe_smul
      exists_isLUB_rotationRange := fun x y ↦
        ⟨VectorLattice.complexModulus x y,
          VectorLattice.complexModulus_isLUB x y⟩ }

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexVectorLattice Z]

/-- In a uniformly complete self-adjoint part, the modulus agrees with the canonical complex
modulus of the real and imaginary parts. -/
theorem modulus_eq_complexModulus [IsUniformlyCompleteVectorLattice (selfAdjoint Z)] (z : Z) :
    modulus z = VectorLattice.complexModulus (ℜ z) (ℑ z) := by
  exact (modulus_isLUB z).unique
    (VectorLattice.complexModulus_isLUB (ℜ z) (ℑ z))

end ComplexVectorLattice

namespace ComplexBanachLattice

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [BanachLattice (selfAdjoint Z)]

/-- A complex normed star-module whose self-adjoint part is a Banach lattice becomes a complex
Banach lattice when its norm is induced by the canonical complex modulus. -/
@[reducible]
noncomputable def ofSelfAdjointBanachLattice
    (coe_smul :
      letI : SMul ℝ (selfAdjoint Z) := VectorLattice.toModule.toSMul
      ∀ (r : ℝ) (x : selfAdjoint Z),
        ((r • x : selfAdjoint Z) : Z) = r • (x : Z))
    (norm_complexModulus :
      letI : IsUniformlyCompleteVectorLattice (selfAdjoint Z) :=
        isUniformlyCompleteVectorLattice_of_banachLattice _
      ∀ z : Z, ‖VectorLattice.complexModulus (ℜ z) (ℑ z)‖ = ‖z‖) :
    ComplexBanachLattice Z := by
  letI : IsUniformlyCompleteVectorLattice (selfAdjoint Z) :=
    isUniformlyCompleteVectorLattice_of_banachLattice _
  letI : ComplexVectorLattice Z :=
    ComplexVectorLattice.ofSelfAdjointBanachLattice coe_smul
  refine { norm_modulus := ?_ }
  intro z
  rw [ComplexVectorLattice.modulus_eq_complexModulus]
  exact norm_complexModulus z

end ComplexBanachLattice

namespace VecLatEquiv

variable {E F : Type*}
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [IsUniformlyCompleteVectorLattice E]
  [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [VectorLattice F] [IsUniformlyCompleteVectorLattice F]

/-- A vector lattice equivalence between uniformly complete vector
lattices preserves the complex modulus. -/
@[simp]
theorem map_complexModulus (e : VecLatEquiv E F) (x y : E) :
    e (VectorLattice.complexModulus x y) =
      VectorLattice.complexModulus (e x) (e y) := by
  exact VectorLattice.map_complexModulus_of_linearOrderIso e.toOrderIso
    e.toLinearEquiv.toLinearMap.isLinear x y

end VecLatEquiv
