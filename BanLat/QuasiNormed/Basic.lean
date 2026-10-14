/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.Analysis.Normed.Module.Basic

/-!
# Quasi-seminorms, quasi-norms and quasi-normed vector spaces

This file introduces the notions of **quasi-seminorms** and **quasi-norms** over additive
commutative groups. Following Mathlib convention, it also defines a **quasi-normed** space
over a normed field `𝕜` as a `𝕜`-module equipped with a quasi-**semi**norm.

Lastly, it also proves that:
* every norm of a seminormed additive commutative group is a quasi-seminorm.
* every norm of a normed additive commutative group is a quasi-norm.
* every normed space is a quasi-normed space.
-/

/-- A *quasi-triangle constant*, that is, an uniform constant for which
the quasi-triangle inequality holds. -/
def IsQuasiTriangleConstant (E : Type*) [AddCommGroup E] [Norm E] (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ x y : E, ‖x + y‖ ≤ K * (‖x‖ + ‖y‖)

/-- A function `‖·‖ : E → ℝ` on an additive commutative group is a **quasi-seminorm** if it is
nonnegative, vanishes at zero, is invariant under negation, and satisfies a quasi-triangle
inequality. -/
class IsQuasiSeminorm (E : Type*) [AddCommGroup E] [Norm E] : Prop where
  norm_zero : ‖(0 : E)‖ = 0
  norm_nonneg : ∀ x : E, 0 ≤ ‖x‖
  norm_neg : ∀ x : E, ‖-x‖ = ‖x‖
  exists_quasi_triangle_constant : ∃ K : ℝ, IsQuasiTriangleConstant E K

attribute [simp] IsQuasiSeminorm.norm_zero IsQuasiSeminorm.norm_neg

/-- A quasi-seminorm is a **quasi-norm** if it vanishes only at zero. -/
class IsQuasiNorm (E : Type*) [AddCommGroup E] [Norm E] : Prop
    extends IsQuasiSeminorm E where
  eq_zero_of_norm_eq_zero : ∀ x : E, ‖x‖ = 0 → x = 0

namespace IsQuasiSeminorm

variable {E : Type*} [AddCommGroup E] [Norm E]

/-- Construct a **quasi-seminorm** from its defining properties and
a specified quasi-triangle constant. -/
theorem of_norm_add_le
    (hnonneg : ∀ x : E, 0 ≤ ‖x‖) (hzero : ‖(0 : E)‖ = 0)
    (hneg : ∀ x : E, ‖-x‖ = ‖x‖) {K : ℝ} (hK : 1 ≤ K)
    (hadd : ∀ x y : E, ‖x + y‖ ≤ K * (‖x‖ + ‖y‖)) :
    IsQuasiSeminorm E where
  norm_zero := hzero
  norm_nonneg := hnonneg
  norm_neg := hneg
  exists_quasi_triangle_constant := ⟨K, hK, hadd⟩

variable [IsQuasiSeminorm E]

/-- A nonpositive quasi-seminorm value is zero. -/
lemma norm_eq_zero_of_nonpos {x : E} (hx : ‖x‖ ≤ 0) : ‖x‖ = 0 :=
  le_antisymm hx (norm_nonneg x)

/-- A quasi-seminorm value is nonpositive exactly when it is zero. -/
@[simp]
lemma norm_le_zero_iff (x : E) : ‖x‖ ≤ 0 ↔ ‖x‖ = 0 := by
  constructor
  · exact norm_eq_zero_of_nonpos
  · exact fun hx ↦ hx.le

/-- Reversing a difference does not change its quasi-seminorm. -/
theorem norm_sub_rev (x y : E) : ‖x - y‖ = ‖y - x‖ := by
  rw [show x - y = -(y - x) by abel, norm_neg]

end IsQuasiSeminorm

namespace IsQuasiTriangleConstant

variable {E : Type*} [AddCommGroup E] [Norm E] {K L : ℝ}

/-- A quasi-triangle constant is at least one. -/
theorem one_le (hK : IsQuasiTriangleConstant E K) : 1 ≤ K :=
  hK.1

/-- A quasi-triangle constant is strictly positive. -/
theorem pos (hK : IsQuasiTriangleConstant E K) : 0 < K :=
  zero_lt_one.trans_le hK.one_le

/-- A quasi-triangle constant is nonnegative. -/
theorem nonneg (hK : IsQuasiTriangleConstant E K) : 0 ≤ K :=
  hK.pos.le

/-- The quasi-triangle inequality associated to a given constant. -/
theorem norm_add_le (hK : IsQuasiTriangleConstant E K) (x y : E) :
    ‖x + y‖ ≤ K * (‖x‖ + ‖y‖) :=
  hK.2 x y

/-- Ik `K` is a quasi-triangle constant, so is every `L ≥ K`. -/
theorem mono [IsQuasiSeminorm E] (hK : IsQuasiTriangleConstant E K) (hKL : K ≤ L) :
    IsQuasiTriangleConstant E L := by
  refine ⟨hK.one_le.trans hKL, fun x y ↦ ?_⟩
  exact (hK.norm_add_le x y).trans <|
    mul_le_mul_of_nonneg_right hKL <|
      add_nonneg (IsQuasiSeminorm.norm_nonneg x) (IsQuasiSeminorm.norm_nonneg y)

/-- The subtraction form of the quasi-triangle inequality. -/
theorem norm_sub_le [IsQuasiSeminorm E] (hK : IsQuasiTriangleConstant E K) (x y : E) :
    ‖x - y‖ ≤ K * (‖x‖ + ‖y‖) := by
  simpa only [sub_eq_add_neg, IsQuasiSeminorm.norm_neg] using hK.norm_add_le x (-y)

/-- A shifted form of the quasi-triangle inequality. -/
theorem norm_le_add (hK : IsQuasiTriangleConstant E K) (x y : E) :
    ‖x‖ ≤ K * (‖x - y‖ + ‖y‖) := by
  calc
    ‖x‖ = ‖(x - y) + y‖ := by
      congr 1
      abel
    _ ≤ K * (‖x - y‖ + ‖y‖) := hK.norm_add_le (x - y) y

end IsQuasiTriangleConstant

namespace IsQuasiNorm

variable {E : Type*} [AddCommGroup E] [Norm E]

/-- Construct a **quasi-norm** from a specified quasi-triangle constant. -/
theorem of_norm_add_le
    (hnonneg : ∀ x : E, 0 ≤ ‖x‖) (hzero : ∀ x : E, ‖x‖ = 0 ↔ x = 0)
    (hneg : ∀ x : E, ‖-x‖ = ‖x‖) {K : ℝ} (hK : 1 ≤ K)
    (hadd : ∀ x y : E, ‖x + y‖ ≤ K * (‖x‖ + ‖y‖)) : IsQuasiNorm E where
  toIsQuasiSeminorm := IsQuasiSeminorm.of_norm_add_le hnonneg ((hzero 0).2 rfl) hneg hK hadd
  eq_zero_of_norm_eq_zero := fun x ↦ (hzero x).1

variable [IsQuasiNorm E]

/-- A quasi-norm vanishes exactly at zero. -/
@[simp]
theorem norm_eq_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0 :=
  ⟨IsQuasiNorm.eq_zero_of_norm_eq_zero x, fun hx ↦ hx ▸ IsQuasiSeminorm.norm_zero⟩

/-- A quasi-norm value is nonpositive exactly when its argument is zero. -/
theorem norm_le_zero_iff (x : E) : ‖x‖ ≤ 0 ↔ x = 0 := by
  rw [IsQuasiSeminorm.norm_le_zero_iff, norm_eq_zero_iff]

/-- An element has nonzero quasi-norm exactly when it is nonzero. -/
theorem norm_ne_zero_iff (x : E) : ‖x‖ ≠ 0 ↔ x ≠ 0 :=
  not_congr (norm_eq_zero_iff x)

/-- A nonzero element has nonzero quasi-norm. -/
theorem norm_ne_zero {x : E} (hx : x ≠ 0) : ‖x‖ ≠ 0 :=
  (norm_ne_zero_iff x).2 hx

/-- An element has strictly positive quasi-norm exactly when it is nonzero. -/
@[simp]
theorem norm_pos_iff (x : E) : 0 < ‖x‖ ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    rw [hzero, IsQuasiSeminorm.norm_zero] at hx
    exact (lt_irrefl 0) hx
  · intro hx
    apply lt_of_le_of_ne (IsQuasiSeminorm.norm_nonneg x)
    intro hzero
    exact hx ((norm_eq_zero_iff x).mp hzero.symm)

/-- A nonzero element has positive quasi-norm. -/
theorem norm_pos {x : E} (hx : x ≠ 0) : 0 < ‖x‖ :=
  (norm_pos_iff x).2 hx

section Scalar

variable {R : Type*} [Semiring R] [IsCancelMulZero R] [Module R E]
  [Module.IsTorsionFree R E]

/-- A scalar multiple has zero quasi-norm exactly when one of its factors is zero. -/
theorem norm_smul_eq_zero_iff (a : R) (x : E) :
    ‖a • x‖ = 0 ↔ a = 0 ∨ x = 0 := by
  rw [norm_eq_zero_iff, smul_eq_zero]

/-- A scalar multiple has positive quasi-norm exactly when both factors are nonzero. -/
theorem norm_smul_pos_iff (a : R) (x : E) :
    0 < ‖a • x‖ ↔ a ≠ 0 ∧ x ≠ 0 := by
  rw [norm_pos_iff, smul_ne_zero_iff]

end Scalar

section RealScalar

variable [Module ℝ E] [NormSMulClass ℝ E]

/-- Normalizing a nonzero vector by its quasi-norm gives a vector of quasi-norm one. -/
theorem norm_inv_smul (x : E) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (IsQuasiSeminorm.norm_nonneg x)),
    inv_mul_cancel₀ ((norm_ne_zero_iff x).2 hx)]

end RealScalar

end IsQuasiNorm

/-- The norm of a seminormed additive commutative group is a quasi-seminorm with constant one. -/
instance (priority := 100) SeminormedAddCommGroup.toIsQuasiSeminorm
    (E : Type*) [SeminormedAddCommGroup E] : IsQuasiSeminorm E where
  norm_zero := norm_zero
  norm_nonneg := fun x ↦ norm_nonneg x
  norm_neg := fun x ↦ norm_neg x
  exists_quasi_triangle_constant := ⟨1, le_rfl, fun x y ↦ by simpa using norm_add_le x y⟩

/-- The norm of a normed additive commutative group is a quasi-norm with constant one. -/
instance (priority := 100) NormedAddCommGroup.toIsQuasiNorm
    (E : Type*) [NormedAddCommGroup E] : IsQuasiNorm E where
  eq_zero_of_norm_eq_zero := fun _ ↦ norm_eq_zero.mp

/-- A **quasi-normed** space over a normed field `𝕜` is a `𝕜`-module equipped with a
quasi-**semi**norm that is homogeneous under scalar multiplication. -/
class QuasiNormedSpace (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [Norm E]
    [IsQuasiSeminorm E] extends Module 𝕜 E, NormSMulClass 𝕜 E

/-- Every normed space is a quasi-normed space. -/
instance (priority := 100) NormedSpace.toQuasiNormedSpace
    (𝕜 E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    QuasiNormedSpace 𝕜 E where

namespace QuasiNormedSubmodule

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Norm E]
  [IsQuasiSeminorm E] [QuasiNormedSpace 𝕜 E]

/-- A submodule inherits the restriction of the quasi-seminorm of its ambient space. -/
scoped instance instNorm (S : Submodule 𝕜 E) : Norm S :=
  ⟨fun x ↦ ‖(x : E)‖⟩

/-- The quasi-seminorm inherited by a submodule is a quasi-seminorm. -/
scoped instance instIsQuasiSeminorm (S : Submodule 𝕜 E) : IsQuasiSeminorm S where
  norm_zero := IsQuasiSeminorm.norm_zero (E := E)
  norm_nonneg x := IsQuasiSeminorm.norm_nonneg (x : E)
  norm_neg x := IsQuasiSeminorm.norm_neg (x : E)
  exists_quasi_triangle_constant := by
    obtain ⟨K, hK⟩ := IsQuasiSeminorm.exists_quasi_triangle_constant (E := E)
    exact ⟨K, hK.one_le, fun x y ↦ hK.norm_add_le (x : E) (y : E)⟩

/-- A submodule of a quasi-normed space is a quasi-normed space. -/
scoped instance instQuasiNormedSpace (S : Submodule 𝕜 E) : QuasiNormedSpace 𝕜 S where
  norm_smul c x := norm_smul c (x : E)

/-- The quasi-seminorm of a submodule element is its quasi-seminorm in the ambient space. -/
@[simp]
theorem coe_quasiNorm {S : Submodule 𝕜 E} (x : S) : ‖x‖ = ‖(x : E)‖ :=
  rfl

end QuasiNormedSubmodule

namespace QuasiNormedSubmodule

open scoped QuasiNormedSubmodule

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Norm E]
  [IsQuasiNorm E] [QuasiNormedSpace 𝕜 E]

/-- The quasi-seminorm inherited by a submodule is a genuine quasi-norm
when the ambient quasi-seminorm is a quasi-norm. -/
scoped instance instIsQuasiNorm (S : Submodule 𝕜 E) : IsQuasiNorm S where
  eq_zero_of_norm_eq_zero x hx :=
    Subtype.ext (IsQuasiNorm.eq_zero_of_norm_eq_zero (x : E) hx)

end QuasiNormedSubmodule
