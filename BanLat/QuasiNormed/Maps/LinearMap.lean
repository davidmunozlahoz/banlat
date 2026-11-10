/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Preliminaries.ContinuousLinearMap
import BanLat.QuasiNormed.Maps.Basic

/-!
# Linear maps between quasi-seminormed spaces

For linear maps between quasi-seminormed spaces, this file establishes:

* An `ε–δ` characterization of continuity at zero.
* Criteria for uniform continuity, uniform embeddings, and complete or closed ranges,
  using upper and positive lower quasi-seminorm bounds.
* Equivalence of continuity and a positive global quasi-seminorm bound over a
  nontrivially normed field.

Maps satisfying an upper quasi-seminorm bound are bundled using Mathlib's
`ContinuousLinearMap`, with the induced quasi-seminorm topologies.
-/

open IsQuasiSeminorm

attribute [local instance] IsQuasiSeminorm.topology

namespace LinearMap

variable {R E F : Type*} [Semiring R]

section QuasiSeminorm

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]
  (T : E →ₗ[R] F)

/-! ### Continuity and uniformity -/

/-- A linear map is continuous for the induced topologies exactly when it
satisfies the `ε–δ` condition at zero. -/
theorem continuous_iff_quasiNorm :
    Continuous T ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖T x‖ < ε := by
  exact AddMonoidHom.continuous_iff_quasiNorm T

/-- An upper quasi-seminorm bound makes a linear map uniformly continuous
for the induced uniformities. -/
theorem uniformContinuous_of_quasiNorm_le_mul
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @UniformContinuous E F (uniformSpace E) (uniformSpace F) T := by
  exact AddMonoidHom.uniformContinuous_of_quasiNorm_le_mul T hC hupper

/-- A linear map bounded above by a nonnegative multiple of the source
quasi-seminorm is continuous for the induced topologies. -/
theorem continuous_of_quasiNorm_le_mul
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    Continuous T := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact (T.uniformContinuous_of_quasiNorm_le_mul hC hupper).continuous

/-- A uniformly continuous linear map with a positive lower quasi-seminorm
bound induces the source uniformity. -/
theorem isUniformInducing_of_uniformContinuous_of_le_quasiNorm
    (hT : @UniformContinuous E F (uniformSpace E) (uniformSpace F) T)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) T := by
  exact AddMonoidHom.isUniformInducing_of_uniformContinuous_of_le_quasiNorm T hT hc hlower

/-- Upper and positive lower quasi-seminorm bounds on a linear map make
the source uniformity the uniformity induced by the map. -/
theorem isUniformInducing_of_le_quasiNorm_of_quasiNorm_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) T := by
  exact AddMonoidHom.isUniformInducing_of_le_quasiNorm_of_quasiNorm_le T hc hC hlower hupper

/-! ### Bundling bounded linear maps -/

/-- Bundle a linear map with an upper quasi-seminorm bound as a continuous
linear map for the induced topologies. -/
noncomputable def mkQuasiContinuous
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    E →L[R] F := by
  exact { toLinearMap := T, cont := T.continuous_of_quasiNorm_le_mul hC hupper }

/-- Bundling a bounded linear map preserves its underlying linear map. -/
@[simp]
theorem mkQuasiContinuous_toLinearMap
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    (T.mkQuasiContinuous C hC hupper).toLinearMap = T := by
  rfl

/-- Bundling a bounded linear map preserves its values. -/
@[simp]
theorem mkQuasiContinuous_apply
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) (x : E) :
    T.mkQuasiContinuous C hC hupper x = T x := by
  rfl

/-! ### Complete ranges -/

/-- A linear map from a complete source satisfying upper and positive lower
quasi-seminorm bounds has complete range. -/
theorem isComplete_range_of_le_quasiNorm_of_quasiNorm_le
    [QuasiSeminormCompleteSpace E]
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsComplete F (uniformSpace F) (Set.range T) := by
  exact AddMonoidHom.isComplete_range_of_le_quasiNorm_of_quasiNorm_le T hc hC hlower hupper

end QuasiSeminorm

section QuasiNorm

variable [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]
  (T : E →ₗ[R] F)

/-! ### Uniform embeddings -/

/-- Upper and positive lower quasi-norm bounds on a linear map give a uniform
embedding when the source quasi-norm separates points. -/
theorem isUniformEmbedding_of_le_quasiNorm_of_quasiNorm_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsUniformEmbedding E F (uniformSpace E) (uniformSpace F) T := by
  exact AddMonoidHom.isUniformEmbedding_of_le_quasiNorm_of_quasiNorm_le T hc hC hlower hupper

end QuasiNorm

section ClosedRange

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]
  [Module R E] [Module R F]
  (T : E →ₗ[R] F)

/-- A linear map from a complete source satisfying upper and positive lower
bounds has closed range when the target quasi-norm separates points. -/
theorem isClosed_range_of_le_quasiNorm_of_quasiNorm_le
    [QuasiSeminormCompleteSpace E]
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    IsClosed (Set.range T) := by
  exact AddMonoidHom.isClosed_range_of_le_quasiNorm_of_quasiNorm_le T hc hC hlower hupper

end ClosedRange

section NormedField

variable {𝕜 𝓕 : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [QuasiNormedSpace 𝕜 E] [QuasiNormedSpace 𝕜 F]
  [FunLike 𝓕 E F] [LinearMapClass 𝓕 𝕜 E F] (T : 𝓕)

/-! ### Global bounds from continuity

These results apply to any bundled map type satisfying `LinearMapClass`, including
continuous linear maps and linear equivalences.
-/

include 𝕜

private lemma bound_of_quasiNorm_ball {ε : ℝ} (hε : 0 < ε)
    (hT : ∀ x, ‖x‖ < ε → ‖T x‖ < 1)
    {a : 𝕜} (ha : 1 < ‖a‖) (x : E) :
    ‖T x‖ ≤ (‖a‖ / ε) * ‖x‖ := by
  by_cases hx : ‖T x‖ = 0
  · simpa only [hx] using
      mul_nonneg (div_nonneg (_root_.norm_nonneg a) hε.le) (IsQuasiSeminorm.norm_nonneg x)
  · obtain ⟨n, hn₁, hn₂⟩ := exists_mem_Ico_zpow
      (lt_of_le_of_ne (IsQuasiSeminorm.norm_nonneg (T x)) (Ne.symm hx)) ha
    have hp : 0 < ‖a‖ ^ n := zpow_pos (zero_lt_one.trans ha) n
    have hscaled : 1 ≤ ‖T (a ^ (-n) • x)‖ := by
      simpa only [map_smul, norm_smul, norm_zpow, zpow_neg, norm_inv, ← div_eq_inv_mul] using
        (one_le_div hp).2 hn₁
    have hεx : ε ≤ ‖a ^ (-n) • x‖ :=
      le_of_not_gt (fun h ↦ (hT _ h).not_ge hscaled)
    rw [norm_smul, norm_zpow, zpow_neg, ← div_eq_inv_mul, le_div_iff₀ hp] at hεx
    rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans ha)), zpow_one] at hn₂
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    calc
      ‖T x‖ * ε ≤ (‖a‖ ^ n * ‖a‖) * ε := mul_le_mul_of_nonneg_right hn₂.le hε.le
      _ = ‖a‖ * (ε * ‖a‖ ^ n) := by ring
      _ ≤ ‖a‖ * ‖x‖ := mul_le_mul_of_nonneg_left hεx (_root_.norm_nonneg a)

/-- Over a nontrivially normed field, a continuous linear map admits a
positive global quasi-seminorm bound. -/
theorem exists_pos_quasiNorm_bound_of_continuous
    (hT : Continuous T) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  obtain ⟨ε, hε, hball⟩ :=
    ((LinearMap.ofClass T : E →ₗ[𝕜] F).continuous_iff_quasiNorm.mp hT) 1 zero_lt_one
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  exact ⟨‖a‖ / ε, div_pos (zero_lt_one.trans ha) hε,
    bound_of_quasiNorm_ball T hε hball ha⟩

/-- Over a nontrivially normed field, continuity of a linear map is equivalent
to the existence of a positive global quasi-seminorm bound. -/
theorem continuous_iff_exists_pos_quasiNorm_bound :
    Continuous T ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  exact ⟨exists_pos_quasiNorm_bound_of_continuous T,
    fun ⟨C, hC, hupper⟩ ↦
      (LinearMap.ofClass T : E →ₗ[𝕜] F).continuous_of_quasiNorm_le_mul hC.le hupper⟩

end NormedField

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [QuasiNormedSpace 𝕜 E] [QuasiNormedSpace 𝕜 F]

/-- A continuous linear map between quasi-seminormed spaces over a nontrivially
normed field admits a positive global quasi-seminorm bound. -/
theorem exists_pos_quasiNorm_bound (T : E →L[𝕜] F) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  exact LinearMap.exists_pos_quasiNorm_bound_of_continuous T T.continuous

end ContinuousLinearMap
