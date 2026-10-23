/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Complex vector and Banach lattices

A **complex vector lattice** is a complex star module whose self-adjoint part is a real vector
lattice and in which every pair of self-adjoint elements has a complex modulus, defined as the
least upper bound of its real rotations.

This file establishes the basic algebraic and order-theoretic properties of the lattice-valued
modulus. It then defines **complex Banach lattices** by requiring the self-adjoint part to be a real
Banach lattice and the norm to be induced by the modulus.
-/

open scoped ComplexStarModule

namespace VectorLattice

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]

/-- The set of rotations of a pair of elements in a vector lattice. -/
def rotationRange (x y : E) : Set E :=
  Set.range fun θ : ℝ ↦ Real.cos θ • x + Real.sin θ • y

/-- Every rotation is bounded above by the sum of the component absolute values. -/
theorem rotation_le_abs_add_abs (x y : E) (θ : ℝ) :
    Real.cos θ • x + Real.sin θ • y ≤ |x| + |y| := by
  calc
    Real.cos θ • x + Real.sin θ • y ≤
        |Real.cos θ • x + Real.sin θ • y| := le_abs_self _
    _ ≤ |Real.cos θ • x| + |Real.sin θ • y| := abs_add_le _ _
    _ = |Real.cos θ| • |x| + |Real.sin θ| • |y| := by
      rw [abs_smul', abs_smul']
    _ ≤ (1 : ℝ) • |x| + (1 : ℝ) • |y| := add_le_add
      (smul_le_smul_of_nonneg_right (Real.abs_cos_le_one θ) (abs_nonneg x))
      (smul_le_smul_of_nonneg_right (Real.abs_sin_le_one θ) (abs_nonneg y))
    _ = |x| + |y| := by rw [one_smul, one_smul]

/-- An upper bound for all rotations bounds both component absolute values. -/
theorem sup_abs_le_of_mem_upperBounds_rotationRange {x y u : E}
    (hu : u ∈ upperBounds (rotationRange x y)) : |x| ⊔ |y| ≤ u := by
  apply sup_le
  · apply abs_le'.mpr
    constructor
    · simpa only [rotationRange, Real.cos_zero, Real.sin_zero, one_smul, zero_smul,
        add_zero] using hu ⟨0, rfl⟩
    · simpa only [rotationRange, Real.cos_pi, Real.sin_pi, neg_smul, one_smul,
        zero_smul, add_zero] using hu ⟨Real.pi, rfl⟩
  · apply abs_le'.mpr
    constructor
    · simpa only [rotationRange, Real.cos_pi_div_two, Real.sin_pi_div_two,
        zero_smul, one_smul, zero_add] using hu ⟨Real.pi / 2, rfl⟩
    · simpa only [rotationRange, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg,
        Real.sin_pi_div_two, zero_smul, neg_smul, one_smul, zero_add] using
        hu ⟨-(Real.pi / 2), rfl⟩

/-- Negating the first component does not change the rotation range. -/
theorem rotationRange_neg_left (x y : E) :
    rotationRange (-x) y = rotationRange x y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi - θ, ?_⟩
    change Real.cos (Real.pi - θ) • x + Real.sin (Real.pi - θ) • y =
      Real.cos θ • (-x) + Real.sin θ • y
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    module
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi - θ, ?_⟩
    change Real.cos (Real.pi - θ) • (-x) + Real.sin (Real.pi - θ) • y =
      Real.cos θ • x + Real.sin θ • y
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    module

/-- Negating the second component does not change the rotation range. -/
theorem rotationRange_neg_right (x y : E) :
    rotationRange x (-y) = rotationRange x y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨-θ, ?_⟩
    change Real.cos (-θ) • x + Real.sin (-θ) • y =
      Real.cos θ • x + Real.sin θ • (-y)
    rw [Real.cos_neg, Real.sin_neg]
    module
  · rintro _ ⟨θ, rfl⟩
    refine ⟨-θ, ?_⟩
    change Real.cos (-θ) • x + Real.sin (-θ) • (-y) =
      Real.cos θ • x + Real.sin θ • y
    rw [Real.cos_neg, Real.sin_neg]
    module

/-- Swapping the components does not change the rotation range. -/
theorem rotationRange_comm (x y : E) :
    rotationRange x y = rotationRange y x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi / 2 - θ, ?_⟩
    change Real.cos (Real.pi / 2 - θ) • y + Real.sin (Real.pi / 2 - θ) • x =
      Real.cos θ • x + Real.sin θ • y
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    module
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi / 2 - θ, ?_⟩
    change Real.cos (Real.pi / 2 - θ) • x + Real.sin (Real.pi / 2 - θ) • y =
      Real.cos θ • y + Real.sin θ • x
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    module

/-- The sum of upper bounds for two rotation ranges is an upper bound for the
rotation range of the coordinatewise sum. -/
theorem add_mem_upperBounds_rotationRange
    {x₁ y₁ x₂ y₂ u₁ u₂ : E}
    (hu₁ : u₁ ∈ upperBounds (rotationRange x₁ y₁))
    (hu₂ : u₂ ∈ upperBounds (rotationRange x₂ y₂)) :
    u₁ + u₂ ∈ upperBounds (rotationRange (x₁ + x₂) (y₁ + y₂)) := by
  rintro _ ⟨θ, rfl⟩
  calc
    Real.cos θ • (x₁ + x₂) + Real.sin θ • (y₁ + y₂) =
        (Real.cos θ • x₁ + Real.sin θ • y₁) +
          (Real.cos θ • x₂ + Real.sin θ • y₂) := by module
    _ ≤ u₁ + u₂ := add_le_add (hu₁ ⟨θ, rfl⟩) (hu₂ ⟨θ, rfl⟩)

/-- Least upper bounds of rotation ranges satisfy the reversed triangle inequality. -/
theorem abs_sub_le_of_isLUB_rotationRange
    {x₁ y₁ x₂ y₂ u₁ u₂ u : E}
    (hu₁ : IsLUB (rotationRange x₁ y₁) u₁)
    (hu₂ : IsLUB (rotationRange x₂ y₂) u₂)
    (hu : IsLUB (rotationRange (x₁ - x₂) (y₁ - y₂)) u) :
    |u₁ - u₂| ≤ u := by
  apply abs_le'.mpr
  constructor
  · rw [sub_le_iff_le_add]
    apply hu₁.2
    simpa only [sub_add_cancel] using
      add_mem_upperBounds_rotationRange hu.1 hu₂.1
  · rw [neg_sub, sub_le_iff_le_add]
    apply hu₂.2
    have hu' : u ∈ upperBounds (rotationRange (x₂ - x₁) (y₂ - y₁)) := by
      rw [← neg_sub x₁ x₂, ← neg_sub y₁ y₂,
        rotationRange_neg_left, rotationRange_neg_right]
      exact hu.1
    simpa only [sub_add_cancel] using
      add_mem_upperBounds_rotationRange hu' hu₁.1

/-- A complex-linear coordinate change scales the rotation range by its Euclidean norm. -/
theorem rotationRange_linear_transform (a b : ℝ) (x y : E) :
    rotationRange (a • x - b • y) (b • x + a • y) =
      (fun z ↦ Real.sqrt (a ^ 2 + b ^ 2) • z) '' rotationRange x y := by
  let r := Real.sqrt (a ^ 2 + b ^ 2)
  let δ := Complex.arg (⟨a, b⟩ : ℂ)
  change rotationRange (a • x - b • y) (b • x + a • y) =
    (fun z ↦ r • z) '' rotationRange x y
  have ha : r * Real.cos δ = a := by
    dsimp [r, δ]
    rw [← Complex.norm_eq_sqrt_sq_add_sq (⟨a, b⟩ : ℂ)]
    exact Complex.norm_mul_cos_arg (⟨a, b⟩ : ℂ)
  have hb : r * Real.sin δ = b := by
    dsimp [r, δ]
    rw [← Complex.norm_eq_sqrt_sq_add_sq (⟨a, b⟩ : ℂ)]
    exact Complex.norm_mul_sin_arg (⟨a, b⟩ : ℂ)
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.cos (θ - δ) • x + Real.sin (θ - δ) • y, ⟨θ - δ, rfl⟩, ?_⟩
    change r • (Real.cos (θ - δ) • x + Real.sin (θ - δ) • y) =
      Real.cos θ • (a • x - b • y) + Real.sin θ • (b • x + a • y)
    rw [Real.cos_sub, Real.sin_sub, ← ha, ← hb]
    module
  · rintro _ ⟨_, ⟨θ, rfl⟩, rfl⟩
    refine ⟨θ + δ, ?_⟩
    change Real.cos (θ + δ) • (a • x - b • y) +
        Real.sin (θ + δ) • (b • x + a • y) =
      r • (Real.cos θ • x + Real.sin θ • y)
    rw [Real.cos_add, Real.sin_add, ← ha, ← hb]
    match_scalars
    · calc
        (Real.cos θ * Real.cos δ - Real.sin θ * Real.sin δ) *
              (r * Real.cos δ * 1) +
            (Real.sin θ * Real.cos δ + Real.cos θ * Real.sin δ) *
              (r * Real.sin δ * 1) =
          r * Real.cos θ * (Real.cos δ ^ 2 + Real.sin δ ^ 2) := by ring
        _ = r * (Real.cos θ * 1) := by rw [Real.cos_sq_add_sin_sq]; ring
    · calc
        (Real.cos θ * Real.cos δ - Real.sin θ * Real.sin δ) *
              -(r * Real.sin δ * 1) +
            (Real.sin θ * Real.cos δ + Real.cos θ * Real.sin δ) *
              (r * Real.cos δ * 1) =
          r * Real.sin θ * (Real.cos δ ^ 2 + Real.sin δ ^ 2) := by ring
        _ = r * (Real.sin θ * 1) := by rw [Real.cos_sq_add_sin_sq]; ring

end VectorLattice

/-- A **complex vector lattice** is a complex star module whose self-adjoint part is a real vector
lattice, in which every pair of self-adjoint elements admits a complex modulus. -/
class ComplexVectorLattice (Z : Type*) [AddCommGroup Z] [Module ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    extends VectorLattice (selfAdjoint Z) where
  /-- Real scalar multiplication in the self-adjoint part agrees with scalar multiplication in
  the ambient complex space. -/
  coe_smul (r : ℝ) (x : selfAdjoint Z) : ((r • x : selfAdjoint Z) : Z) = r • (x : Z)
  /-- Every pair of self-adjoint elements has a least upper bound of its real rotations. -/
  exists_isLUB_rotationRange (x y : selfAdjoint Z) :
    ∃ u : selfAdjoint Z, IsLUB (VectorLattice.rotationRange x y) u

attribute [simp] ComplexVectorLattice.coe_smul

namespace ComplexVectorLattice

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexVectorLattice Z]

/-- The lattice-valued modulus of an element of a complex vector lattice. -/
noncomputable def modulus (z : Z) : selfAdjoint Z :=
  Classical.choose
    (ComplexVectorLattice.exists_isLUB_rotationRange (Z := Z) (ℜ z) (ℑ z))

/-- The modulus is the least upper bound of the rotations of the real and imaginary parts. -/
theorem modulus_isLUB (z : Z) :
    IsLUB (VectorLattice.rotationRange (ℜ z) (ℑ z)) (modulus z) := by
  exact Classical.choose_spec
    (ComplexVectorLattice.exists_isLUB_rotationRange (Z := Z) (ℜ z) (ℑ z))

/-- The modulus is equal to any least upper bound of the rotations of the real and imaginary
parts. -/
theorem modulus_eq_of_isLUB {z : Z} {x : selfAdjoint Z}
    (hx : IsLUB (VectorLattice.rotationRange (ℜ z) (ℑ z)) x) :
    modulus z = x := by
  exact (modulus_isLUB z).unique hx

private theorem rotation_le_modulus (z : Z) (θ : ℝ) :
    Real.cos θ • ℜ z + Real.sin θ • ℑ z ≤ modulus z := by
  have h := (modulus_isLUB z).1 ⟨θ, rfl⟩
  convert h using 1
  ext
  simp

/-- The modulus is bounded above by an element exactly when every rotation is bounded above by
that element. -/
theorem modulus_le_iff {z : Z} {x : selfAdjoint Z} :
    modulus z ≤ x ↔
      ∀ θ : ℝ, Real.cos θ • ℜ z + Real.sin θ • ℑ z ≤ x := by
  constructor
  · intro h θ
    exact (rotation_le_modulus z θ).trans h
  · intro h
    apply (modulus_isLUB z).2
    rintro _ ⟨θ, rfl⟩
    have hr := h θ
    convert hr using 1
    ext
    simp

private theorem sup_abs_parts_le_modulus (z : Z) :
    |ℜ z| ⊔ |ℑ z| ≤ modulus z := by
  exact VectorLattice.sup_abs_le_of_mem_upperBounds_rotationRange
    (modulus_isLUB z).1

/-- The modulus of an element is always nonnegative. -/
theorem modulus_nonneg (z : Z) :
    0 ≤ modulus z := by
  exact (abs_nonneg (ℜ z)).trans (le_sup_left.trans (sup_abs_parts_le_modulus z))

/-- The modulus of zero is zero. -/
@[simp]
theorem modulus_zero :
    modulus (0 : Z) = 0 := by
  apply le_antisymm
  · rw [modulus_le_iff]
    intro θ
    simp
  · exact modulus_nonneg 0

/-- The modulus of an element is zero if and only if the element is zero. -/
@[simp]
theorem modulus_eq_zero_iff (z : Z) :
    modulus z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hreabs : |ℜ z| = 0 := le_antisymm
      ((le_sup_left.trans (sup_abs_parts_le_modulus z)).trans_eq h) (abs_nonneg _)
    have himabs : |ℑ z| = 0 := le_antisymm
      ((le_sup_right.trans (sup_abs_parts_le_modulus z)).trans_eq h) (abs_nonneg _)
    have hre : ℜ z = 0 := (abs_eq_zero_iff_zero _).mp hreabs
    have him : ℑ z = 0 := (abs_eq_zero_iff_zero _).mp himabs
    rw [← realPart_add_I_smul_imaginaryPart z, hre, him]
    simp
  · rintro rfl
    exact modulus_zero

/-- Conjugation preserves the lattice-valued modulus. -/
@[simp]
theorem modulus_star (z : Z) :
    modulus (star z) = modulus z := by
  apply modulus_eq_of_isLUB
  have hre : ℜ (star z) = ℜ z := by
    ext
    simp only [realPart_apply_coe, star_star]
    module
  have him : ℑ (star z) = -ℑ z := by
    ext
    simp [imaginaryPart_apply_coe]
    module
  rw [hre, him, VectorLattice.rotationRange_neg_right]
  exact modulus_isLUB z

/-- Complex scalar multiplication scales the lattice-valued modulus by the norm of the scalar. -/
theorem modulus_smul (c : ℂ) (z : Z) :
    modulus (c • z) = ‖c‖ • modulus z := by
  apply (modulus_isLUB (c • z)).unique
  rw [realPart_smul, imaginaryPart_smul]
  have h := isLUB_smul_of_nonneg (Real.sqrt_nonneg (c.re ^ 2 + c.im ^ 2))
    (modulus_isLUB z)
  rw [← VectorLattice.rotationRange_linear_transform] at h
  simp only [Complex.norm_def, Complex.normSq_apply]
  convert h using 1
  all_goals first | rfl | (congr 1 <;> (ext; simp [add_comm])) | (ext; simp [pow_two])

/-- Negation preserves the lattice-valued modulus. -/
@[simp]
theorem modulus_neg (z : Z) :
    modulus (-z) = modulus z := by
  simpa using modulus_smul (-1 : ℂ) z

/-- The absolute value of the real part is bounded by the modulus. -/
theorem abs_realPart_le_modulus (z : Z) :
    |ℜ z| ≤ modulus z := by
  exact le_sup_left.trans (sup_abs_parts_le_modulus z)

/-- The absolute value of the imaginary part is bounded by the modulus. -/
theorem abs_imaginaryPart_le_modulus (z : Z) :
    |ℑ z| ≤ modulus z := by
  exact le_sup_right.trans (sup_abs_parts_le_modulus z)

/-- The modulus is bounded by the sum of the absolute values of its real and imaginary parts. -/
theorem modulus_le_abs_realPart_add_abs_imaginaryPart (z : Z) :
    modulus z ≤ |ℜ z| + |ℑ z| := by
  apply (modulus_isLUB z).2
  rintro _ ⟨θ, rfl⟩
  exact VectorLattice.rotation_le_abs_add_abs (ℜ z) (ℑ z) θ

/-- The lattice-valued modulus satisfies the triangle inequality. -/
theorem modulus_add_le (z w : Z) :
    modulus (z + w) ≤ modulus z + modulus w := by
  rw [modulus_le_iff]
  intro θ
  rw [map_add, map_add]
  have h := (VectorLattice.add_mem_upperBounds_rotationRange
    (modulus_isLUB z).1 (modulus_isLUB w).1) ⟨θ, rfl⟩
  convert h using 1
  all_goals
    ext
    simp

/-- On self-adjoint elements, the complex modulus agrees with the lattice absolute value. -/
@[simp]
theorem modulus_coe (x : selfAdjoint Z) :
    modulus (x : Z) = |x| := by
  apply le_antisymm
  · simpa using modulus_le_abs_realPart_add_abs_imaginaryPart (x : Z)
  · simpa using abs_realPart_le_modulus (x : Z)

/-- The difference of two moduli is bounded in absolute value by the modulus of the difference. -/
theorem abs_modulus_sub_modulus_le (z w : Z) :
    |modulus z - modulus w| ≤ modulus (z - w) := by
  apply VectorLattice.abs_sub_le_of_isLUB_rotationRange
    (modulus_isLUB z) (modulus_isLUB w)
  simpa only [map_sub] using modulus_isLUB (z - w)

end ComplexVectorLattice

/-- A **complex Banach lattice** is a complex vector lattice whose self-adjoint part is a real
Banach lattice and whose norm is induced by the lattice-valued modulus. -/
class ComplexBanachLattice (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    extends ComplexVectorLattice Z, BanachLattice (selfAdjoint Z) where
  /-- The norm is determined by the lattice-valued modulus. -/
  norm_modulus (z : Z) : ‖ComplexVectorLattice.modulus z‖ = ‖z‖

namespace ComplexBanachLattice

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

/-- The lattice-valued modulus is Lipschitz with constant one. -/
theorem norm_modulus_sub_modulus_le (z w : Z) :
    ‖ComplexVectorLattice.modulus z - ComplexVectorLattice.modulus w‖ ≤ ‖z - w‖ := by
  calc
    ‖ComplexVectorLattice.modulus z - ComplexVectorLattice.modulus w‖ ≤
        ‖ComplexVectorLattice.modulus (z - w)‖ :=
      norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (ComplexVectorLattice.modulus_nonneg (z - w))]
        exact ComplexVectorLattice.abs_modulus_sub_modulus_le z w)
    _ = ‖z - w‖ := norm_modulus (z - w)

/-- Conjugation is isometric on a complex Banach lattice. -/
noncomputable instance instNormedStarGroup : NormedStarGroup Z := by
  constructor
  intro z
  rw [← norm_modulus (star z), ComplexVectorLattice.modulus_star, norm_modulus]

/-- The real and imaginary parts give a real continuous linear equivalence with two copies
of the self-adjoint part. -/
noncomputable def realImagEquiv :
    Z ≃L[ℝ] selfAdjoint Z × selfAdjoint Z := by
  let e : Z ≃ₗ[ℝ] selfAdjoint Z × selfAdjoint Z := by
    refine
      { toFun := fun z ↦ (ℜ z, ℑ z)
        invFun := fun p ↦ (p.1 : Z) + Complex.I • (p.2 : Z)
        left_inv := realPart_add_I_smul_imaginaryPart
        right_inv := by
          intro p
          ext <;> simp
        map_add' := by
          intro z w
          ext <;> simp
        map_smul' := by
          intro r z
          ext <;> simp }
  refine e.toContinuousLinearEquivOfBounds 1 2 ?_ ?_
  · intro z
    change ‖(ℜ z, ℑ z)‖ ≤ 1 * ‖z‖
    simpa [Prod.norm_def] using max_le (realPart.norm_le z) (imaginaryPart.norm_le z)
  · intro p
    rw [Prod.norm_def]
    calc
      ‖e.symm p‖ ≤ ‖(p.1 : Z)‖ + ‖Complex.I • (p.2 : Z)‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ + ‖p.2‖ :=
        add_le_add_right (by simpa using norm_smul_le Complex.I (p.2 : Z)) _
      _ ≤ max ‖p.1‖ ‖p.2‖ + max ‖p.1‖ ‖p.2‖ :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max ‖p.1‖ ‖p.2‖ := by ring

/-- The real-imaginary equivalence sends an element to its real and imaginary parts. -/
@[simp]
theorem realImagEquiv_apply (z : Z) :
    realImagEquiv z = (ℜ z, ℑ z) := by
  rfl

/-- The inverse real-imaginary equivalence sends `(x, y)` to `x + I • y`. -/
@[simp]
theorem realImagEquiv_symm_apply (p : selfAdjoint Z × selfAdjoint Z) :
    realImagEquiv.symm p = (p.1 : Z) + Complex.I • (p.2 : Z) := by
  rfl

/-- A complex Banach lattice is complete. -/
noncomputable instance instCompleteSpace : CompleteSpace Z := by
  let e : Z ≃L[ℝ] selfAdjoint Z × selfAdjoint Z := realImagEquiv
  exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).mpr inferInstance

end ComplexBanachLattice
