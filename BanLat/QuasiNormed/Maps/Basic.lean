/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.QuasiNormed.Complete
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Maps between quasi-seminormed spaces

For maps between quasi-seminormed spaces, this file establishes:

* `ε–δ` characterizations of continuity and uniform continuity.
* Criteria for inducing the source uniformity and for uniform embeddings,
  using upper and positive lower bounds on quasi-seminorms of differences.
* Completeness of the range for maps inducing the uniformity of a complete source,
  and closedness of the range when the target is quasi-normed.

For additive maps, these criteria are expressed using quasi-seminorm bounds at zero.
-/

namespace IsQuasiSeminorm

variable {E F : Type*} {f : E → F}

section QuasiSeminorm

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-! ### Characterizations using differences -/

/-- Continuity at a point for the induced topologies is equivalent to the
`ε–δ` condition on quasi-seminorms of differences. -/
theorem continuousAt_iff_norm_sub {a : E} :
    @ContinuousAt E F (topology E) (topology F) f a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - a‖ < δ → ‖f x - f a‖ < ε := by
  simpa only [ContinuousAt, mem_ball] using
    (nhds_hasBasis a).tendsto_iff (nhds_hasBasis (f a)) (f := f)

/-- Uniform continuity for the induced uniformities is equivalent to a uniform
`ε–δ` condition on quasi-seminorms of differences. -/
theorem uniformContinuous_iff_norm_sub :
    @UniformContinuous E F (uniformSpace E) (uniformSpace F) f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y,
        ‖x - y‖ < δ → ‖f x - f y‖ < ε := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  simpa only [Set.mem_ofPred_eq, norm_sub_rev] using
    (uniformity_hasBasis (E := E)).uniformContinuous_iff
      (uniformity_hasBasis (E := F)) (f := f)

/-- A map induces the source uniformity exactly when it is uniformly continuous
and small image differences force small source differences. -/
theorem isUniformInducing_iff_norm_sub :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f ↔
      @UniformContinuous E F (uniformSpace E) (uniformSpace F) f ∧
        ∀ ε > 0, ∃ δ > 0, ∀ x y,
          ‖f x - f y‖ < δ → ‖x - y‖ < ε := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  rw [_root_.isUniformInducing_iff']
  refine and_congr Iff.rfl ?_
  rw [((uniformity_hasBasis (E := F)).comap (Prod.map f f)).le_basis_iff
    (uniformity_hasBasis (E := E))]
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_ofPred_eq, Prod.forall, Prod.map_apply,
    norm_sub_rev]

/-! ### Quantitative bounds -/

/-- An upper bound on quasi-seminorms of differences implies uniform continuity
for the induced uniformities. -/
theorem uniformContinuous_of_norm_sub_le_mul
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
    @UniformContinuous E F (uniformSpace E) (uniformSpace F) f := by
  refine uniformContinuous_iff_norm_sub.mpr ?_
  refine fun ε hε ↦ ⟨ε / (C + 1), div_pos hε (by positivity), fun x y hxy ↦ ?_⟩
  calc
    ‖f x - f y‖ ≤ C * ‖x - y‖ := hf x y
    _ ≤ (C + 1) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' (by positivity)).mp hxy

/-- A uniformly continuous map with a positive lower bound on differences
induces the source uniformity. -/
theorem isUniformInducing_of_uniformContinuous_of_le_norm_sub
    (hf : @UniformContinuous E F (uniformSpace E) (uniformSpace F) f)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x y, c * ‖x - y‖ ≤ ‖f x - f y‖) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f := by
  refine isUniformInducing_iff_norm_sub.mpr
    ⟨hf, fun ε hε ↦ ⟨c * ε, mul_pos hc hε, fun x y hxy ↦ ?_⟩⟩
  exact (mul_lt_mul_iff_right₀ hc).mp ((hlower x y).trans_lt hxy)

/-- Upper and positive lower bounds on quasi-seminorms of differences make
the source uniformity the uniformity induced by the map. -/
theorem isUniformInducing_of_le_norm_sub_of_norm_sub_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x y, c * ‖x - y‖ ≤ ‖f x - f y‖)
    (hupper : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f := by
  exact isUniformInducing_of_uniformContinuous_of_le_norm_sub
    (uniformContinuous_of_norm_sub_le_mul hC hupper) hc hlower

end QuasiSeminorm

section QuasiNorm

variable [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-! ### Uniform embeddings -/

/-- Upper and positive lower bounds on differences give a uniform embedding
when the source quasi-norm separates points. -/
theorem isUniformEmbedding_of_le_norm_sub_of_norm_sub_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x y, c * ‖x - y‖ ≤ ‖f x - f y‖)
    (hupper : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
    @IsUniformEmbedding E F (uniformSpace E) (uniformSpace F) f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact (isUniformInducing_of_le_norm_sub_of_norm_sub_le hc hC hlower hupper).isUniformEmbedding

end QuasiNorm

section CompleteRange

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [QuasiSeminormCompleteSpace E]

/-! ### Complete ranges -/

/-- A map inducing the quasi-seminorm uniformity of a complete source has
complete range in the target quasi-seminorm uniformity. -/
theorem isComplete_range_of_isUniformInducing
    (hf : @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f) :
    @IsComplete F (uniformSpace F) (Set.range f) := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact hf.isComplete_range

/-- A map from a complete source satisfying upper and positive lower
quasi-seminorm bounds on differences has complete range. -/
theorem isComplete_range_of_le_norm_sub_of_norm_sub_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x y, c * ‖x - y‖ ≤ ‖f x - f y‖)
    (hupper : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
    @IsComplete F (uniformSpace F) (Set.range f) := by
  exact isComplete_range_of_isUniformInducing
    (isUniformInducing_of_le_norm_sub_of_norm_sub_le hc hC hlower hupper)

end CompleteRange

section ClosedRange

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]
  [QuasiSeminormCompleteSpace E]

/-! ### Closed ranges -/

/-- A map inducing the quasi-seminorm uniformity of a complete source has
closed range when the target quasi-norm separates points. -/
theorem isClosed_range_of_isUniformInducing
    (hf : @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f) :
    @IsClosed F (topology F) (Set.range f) := by
  let : UniformSpace F := uniformSpace F
  exact (isComplete_range_of_isUniformInducing hf).isClosed

/-- A map from a complete source satisfying upper and positive lower bounds
on differences has closed range when the target quasi-norm separates points. -/
theorem isClosed_range_of_le_norm_sub_of_norm_sub_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x y, c * ‖x - y‖ ≤ ‖f x - f y‖)
    (hupper : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
    @IsClosed F (topology F) (Set.range f) := by
  exact isClosed_range_of_isUniformInducing
    (isUniformInducing_of_le_norm_sub_of_norm_sub_le hc hC hlower hupper)

end ClosedRange

end IsQuasiSeminorm

namespace AddMonoidHom

open IsQuasiSeminorm

variable {E F 𝓕 : Type*}

/-! ### Additive maps -/

section QuasiSeminorm

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] (T : 𝓕)

/-- An additive map is continuous for the induced topologies exactly when it
satisfies the `ε–δ` condition at zero. -/
theorem continuous_iff_quasiNorm :
    @Continuous E F (topology E) (topology F) T ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖T x‖ < ε := by
  let : TopologicalSpace E := topology E
  let : TopologicalSpace F := topology F
  have : IsTopologicalAddGroup E := (addGroupFilterBasis E).isTopologicalAddGroup
  have : IsTopologicalAddGroup F := (addGroupFilterBasis F).isTopologicalAddGroup
  rw [show Continuous T ↔ ContinuousAt T 0 from
    ⟨fun h ↦ h.continuousAt, continuous_of_continuousAt_zero T⟩,
    IsQuasiSeminorm.continuousAt_iff_norm_sub]
  simp only [map_zero, sub_zero]

/-- An additive map bounded above by a nonnegative multiple of the source
quasi-seminorm is uniformly continuous for the induced uniformities. -/
theorem uniformContinuous_of_quasiNorm_le_mul
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @UniformContinuous E F (uniformSpace E) (uniformSpace F) T := by
  exact IsQuasiSeminorm.uniformContinuous_of_norm_sub_le_mul hC
    (fun x y ↦ by simpa only [map_sub] using hupper (x - y))

/-- A uniformly continuous additive map with a positive lower quasi-seminorm
bound induces the source uniformity. -/
theorem isUniformInducing_of_uniformContinuous_of_le_quasiNorm
    (hT : @UniformContinuous E F (uniformSpace E) (uniformSpace F) T)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) T := by
  exact IsQuasiSeminorm.isUniformInducing_of_uniformContinuous_of_le_norm_sub hT hc
    (fun x y ↦ by simpa only [map_sub] using hlower (x - y))

/-- Upper and positive lower quasi-seminorm bounds on an additive map make
the source uniformity the uniformity induced by the map. -/
theorem isUniformInducing_of_le_quasiNorm_of_quasiNorm_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) T := by
  exact isUniformInducing_of_uniformContinuous_of_le_quasiNorm T
    (uniformContinuous_of_quasiNorm_le_mul T hC hupper) hc hlower

/-- An additive map from a complete source satisfying upper and positive lower
quasi-seminorm bounds has complete range. -/
theorem isComplete_range_of_le_quasiNorm_of_quasiNorm_le
    [QuasiSeminormCompleteSpace E]
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsComplete F (uniformSpace F) (Set.range T) := by
  exact IsQuasiSeminorm.isComplete_range_of_isUniformInducing
    (isUniformInducing_of_le_quasiNorm_of_quasiNorm_le T hc hC hlower hupper)

end QuasiSeminorm

section QuasiNorm

variable [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] (T : 𝓕)

/-- Upper and positive lower quasi-norm bounds on an additive map give a uniform
embedding when the source quasi-norm separates points. -/
theorem isUniformEmbedding_of_le_quasiNorm_of_quasiNorm_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsUniformEmbedding E F (uniformSpace E) (uniformSpace F) T := by
  exact IsQuasiSeminorm.isUniformEmbedding_of_le_norm_sub_of_norm_sub_le hc hC
    (fun x y ↦ by simpa only [map_sub] using hlower (x - y))
    (fun x y ↦ by simpa only [map_sub] using hupper (x - y))

end QuasiNorm

section ClosedRange

variable [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]
  [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] (T : 𝓕)

/-- An additive map from a complete source satisfying upper and positive lower
bounds has closed range when the target quasi-norm separates points. -/
theorem isClosed_range_of_le_quasiNorm_of_quasiNorm_le
    [QuasiSeminormCompleteSpace E]
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * ‖x‖ ≤ ‖T x‖)
    (hupper : ∀ x, ‖T x‖ ≤ C * ‖x‖) :
    @IsClosed F (topology F) (Set.range T) := by
  exact IsQuasiSeminorm.isClosed_range_of_isUniformInducing
    (isUniformInducing_of_le_quasiNorm_of_quasiNorm_le T hc hC hlower hupper)

end ClosedRange

end AddMonoidHom
