/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.QuasiNormed.Maps.LinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.UniformSpace.Equiv

/-!
# Isometries between quasi-seminormed spaces

For maps between quasi-seminormed spaces, this file introduces:

* Quasi-isometries, as those maps preserving quasi-seminorms of differences.
* Linear quasi-norm isometries and linear quasi-norm isometric equivalences.

It also establishes uniform continuity, injectivity when the source is quasi-normed,
and closedness of the range when the source is complete and the target is quasi-normed.
For linear quasi-norm isometries, it also identifies the range with the closed linear
span of the image of a family whose linear span is dense in the source.
-/

open IsQuasiSeminorm

attribute [local instance] IsQuasiSeminorm.topology

/-- A map preserving quasi-seminorms of differences exactly. -/
structure QuasiIsometry (E F : Type*)
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F] where
  toFun : E → F
  norm_sub_map' : ∀ x y, ‖toFun x - toFun y‖ = ‖x - y‖

namespace QuasiIsometry

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-- Quasi-isometries can be evaluated as functions. -/
instance instFunLike : FunLike (QuasiIsometry E F) E F where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/-- A quasi-isometry preserves quasi-seminorms of differences. -/
@[simp]
theorem norm_sub_map (f : QuasiIsometry E F) (x y : E) :
    ‖f x - f y‖ = ‖x - y‖ := by
  exact f.norm_sub_map' x y

/-- Bundle an additive map preserving quasi-seminorms as a quasi-isometry. -/
def ofAddMonoidHom {𝓕 : Type*} [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F]
    (T : 𝓕) (hT : ∀ x, ‖T x‖ = ‖x‖) : QuasiIsometry E F where
  toFun := T
  norm_sub_map' x y := by simpa only [map_sub] using hT (x - y)

/-- A quasi-isometry induces the source quasi-seminorm uniformity. -/
protected theorem isUniformInducing (f : QuasiIsometry E F) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f := by
  exact isUniformInducing_of_le_norm_sub_of_norm_sub_le zero_lt_one zero_le_one
    (fun x y ↦ by rw [one_mul, f.norm_sub_map])
    (fun x y ↦ by rw [one_mul, f.norm_sub_map])

/-- A quasi-isometry is uniformly continuous for the induced uniformities. -/
protected theorem uniformContinuous (f : QuasiIsometry E F) :
    @UniformContinuous E F (uniformSpace E) (uniformSpace F) f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact f.isUniformInducing.uniformContinuous

/-- A quasi-isometry is continuous for the induced topologies. -/
protected theorem continuous (f : QuasiIsometry E F) : Continuous f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact f.uniformContinuous.continuous

end QuasiIsometry

namespace QuasiIsometry

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-- A quasi-isometry with a genuine source quasi-norm is injective. -/
theorem injective (f : QuasiIsometry E F) : Function.Injective f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact f.isUniformInducing.isUniformEmbedding.injective

end QuasiIsometry

namespace QuasiIsometry

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]

/-- A quasi-isometry from a complete source has closed range in a genuine target. -/
theorem isClosed_range [QuasiSeminormCompleteSpace E] (f : QuasiIsometry E F) :
    IsClosed (Set.range f) := by
  exact isClosed_range_of_isUniformInducing f.isUniformInducing

end QuasiIsometry

/-- An equivalence preserving quasi-seminorms of differences exactly. -/
structure QuasiIsometryEquiv (E F : Type*)
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F] extends E ≃ F where
  norm_sub_map' : ∀ x y, ‖toEquiv x - toEquiv y‖ = ‖x - y‖

namespace QuasiIsometryEquiv

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-- Quasi-isometric equivalences can be evaluated and inverted as equivalences. -/
instance instEquivLike : EquivLike (QuasiIsometryEquiv E F) E F where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact DFunLike.coe_injective h

/-- A quasi-isometric equivalence preserves quasi-seminorms of differences. -/
@[simp]
theorem norm_sub_map (e : QuasiIsometryEquiv E F) (x y : E) :
    ‖e x - e y‖ = ‖x - y‖ := by
  exact e.norm_sub_map' x y

/-- Forget the inverse of a quasi-isometric equivalence. -/
def toQuasiIsometry (e : QuasiIsometryEquiv E F) : QuasiIsometry E F where
  toFun := e
  norm_sub_map' := e.norm_sub_map

/-- The inverse quasi-isometric equivalence. -/
def symm (e : QuasiIsometryEquiv E F) : QuasiIsometryEquiv F E where
  toEquiv := e.toEquiv.symm
  norm_sub_map' x y := by
    simpa only [Equiv.apply_symm_apply] using
      (e.norm_sub_map' (e.toEquiv.symm x) (e.toEquiv.symm y)).symm

/-- Regard a quasi-isometric equivalence as an equivalence of induced uniform spaces. -/
def toUniformEquiv (e : QuasiIsometryEquiv E F) :
    @UniformEquiv E F (uniformSpace E) (uniformSpace F) := by
  exact @UniformEquiv.mk E F (uniformSpace E) (uniformSpace F) e.toEquiv
    e.toQuasiIsometry.uniformContinuous e.symm.toQuasiIsometry.uniformContinuous

/-- Completeness is preserved and reflected by a quasi-isometric equivalence. -/
theorem quasiSeminormCompleteSpace_iff (e : QuasiIsometryEquiv E F) :
    QuasiSeminormCompleteSpace E ↔ QuasiSeminormCompleteSpace F := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact e.toUniformEquiv.completeSpace_iff

end QuasiIsometryEquiv

/-- A linear map preserving the quasi-seminorm exactly. -/
structure QuasiLinearIsometry (R E F : Type*) [Semiring R]
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
    [Module R E] [Module R F] extends E →ₗ[R] F where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖

namespace QuasiLinearIsometry

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]

/-- Quasi-linear isometries can be evaluated as functions. -/
instance instFunLike : FunLike (QuasiLinearIsometry R E F) E F where
  coe T := T.toLinearMap
  coe_injective T S h := by
    cases T
    cases S
    congr
    exact DFunLike.coe_injective h

/-- Quasi-linear isometries satisfy the existing linear-map interface. -/
instance instLinearMapClass :
    LinearMapClass (QuasiLinearIsometry R E F) R E F where
  map_add T := T.toLinearMap.map_add
  map_smulₛₗ T := T.toLinearMap.map_smul

/-- A quasi-linear isometry preserves quasi-seminorms. -/
@[simp]
theorem norm_map (T : QuasiLinearIsometry R E F) (x : E) :
    ‖T x‖ = ‖x‖ := by
  exact T.norm_map' x

/-- Forget the linear structure of a quasi-linear isometry. -/
def toQuasiIsometry (T : QuasiLinearIsometry R E F) : QuasiIsometry E F := by
  exact QuasiIsometry.ofAddMonoidHom T T.norm_map

/-- A quasi-linear isometry is continuous for the induced topologies. -/
protected theorem continuous (T : QuasiLinearIsometry R E F) : Continuous T := by
  exact T.toQuasiIsometry.continuous

end QuasiLinearIsometry

namespace QuasiLinearIsometry

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]

/-- A quasi-linear isometry with a genuine source quasi-norm is injective. -/
theorem injective (T : QuasiLinearIsometry R E F) : Function.Injective T := by
  exact T.toQuasiIsometry.injective

end QuasiLinearIsometry

namespace QuasiLinearIsometry

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]
  [Module R E] [Module R F]

/-- A quasi-linear isometry from a complete source has closed range in a genuine target. -/
theorem isClosed_range [QuasiSeminormCompleteSpace E] (T : QuasiLinearIsometry R E F) :
    IsClosed (Set.range T) := by
  exact T.toQuasiIsometry.isClosed_range

end QuasiLinearIsometry

/-- A linear equivalence preserving the quasi-seminorm exactly. -/
structure QuasiLinearIsometryEquiv (R E F : Type*) [Semiring R]
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
    [Module R E] [Module R F] extends E ≃ₗ[R] F where
  norm_map' : ∀ x, ‖toLinearEquiv x‖ = ‖x‖

namespace QuasiLinearIsometryEquiv

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]

/-- Quasi-linear isometric equivalences can be evaluated and inverted as equivalences. -/
instance instEquivLike : EquivLike (QuasiLinearIsometryEquiv R E F) E F where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact DFunLike.coe_injective h

/-- Quasi-linear isometric equivalences satisfy the existing linear-map interface. -/
instance instLinearMapClass :
    LinearMapClass (QuasiLinearIsometryEquiv R E F) R E F where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

/-- A quasi-linear isometric equivalence preserves quasi-seminorms. -/
@[simp]
theorem norm_map (e : QuasiLinearIsometryEquiv R E F) (x : E) :
    ‖e x‖ = ‖x‖ := by
  exact e.norm_map' x

/-- Forget linearity while retaining the quasi-isometric equivalence. -/
def toQuasiIsometryEquiv (e : QuasiLinearIsometryEquiv R E F) :
    QuasiIsometryEquiv E F where
  toEquiv := e.toLinearEquiv.toEquiv
  norm_sub_map' x y := by
    change ‖e.toLinearEquiv x - e.toLinearEquiv y‖ = ‖x - y‖
    simpa only [map_sub] using e.norm_map' (x - y)

end QuasiLinearIsometryEquiv

namespace QuasiLinearIsometry

open scoped QuasiNormedSubmodule

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Norm E] [IsQuasiNorm E] [QuasiNormedSpace 𝕜 E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F] [QuasiNormedSpace 𝕜 F]

/-- A quasi-linear isometry identifies a genuine source with its linear range. -/
noncomputable def equivRange (T : QuasiLinearIsometry 𝕜 E F) :
    QuasiLinearIsometryEquiv 𝕜 E (LinearMap.range T.toLinearMap) where
  toLinearEquiv := LinearEquiv.ofInjective T.toLinearMap T.injective
  norm_map' := T.norm_map'

/-- The equivalence with the linear range has the original ambient-space values. -/
@[simp]
theorem equivRange_apply_coe (T : QuasiLinearIsometry 𝕜 E F) (x : E) :
    ((T.equivRange x : LinearMap.range T.toLinearMap) : F) = T x := by
  rfl

end QuasiLinearIsometry

section Seminormed

variable {R E F : Type*} [Semiring R]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- Regard an ordinary linear isometry as a quasi-linear isometry. -/
def QuasiLinearIsometry.ofLinearIsometry (T : E →ₗᵢ[R] F) :
    QuasiLinearIsometry R E F where
  toLinearMap := T.toLinearMap
  norm_map' := T.norm_map

/-- Regard a quasi-linear isometry between seminormed groups as an ordinary linear isometry. -/
def QuasiLinearIsometry.toLinearIsometry (T : QuasiLinearIsometry R E F) :
    E →ₗᵢ[R] F where
  toLinearMap := T.toLinearMap
  norm_map' := T.norm_map

/-- Regard a quasi-linear isometric equivalence as an ordinary linear isometric equivalence. -/
def QuasiLinearIsometryEquiv.toLinearIsometryEquiv (e : QuasiLinearIsometryEquiv R E F) :
    E ≃ₗᵢ[R] F where
  toLinearEquiv := e.toLinearEquiv
  norm_map' := e.norm_map

end Seminormed

namespace QuasiLinearIsometry

section ClosedSpan

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [QuasiNormedSpace 𝕜 E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F] [QuasiNormedSpace 𝕜 F]

/-- Let `T : E → F` be a linear quasi-norm isometry from a complete quasi-seminormed space `E`
to a quasi-normed space `F`. If `closure(span(s)) = E`, then `range(T) = closure(span(T(s)))`. -/
theorem range_eq_quasiTopologicalClosure_span_image
    [QuasiSeminormCompleteSpace E]
    (T : QuasiLinearIsometry 𝕜 E F) (s : Set E)
    (hs : @Dense E (IsQuasiSeminorm.topology E)
      (Submodule.span 𝕜 s : Set E)) :
    LinearMap.range T.toLinearMap =
      (Submodule.span 𝕜 (T '' s)).quasiTopologicalClosure := by
  have : IsTopologicalAddGroup F := (IsQuasiSeminorm.addGroupFilterBasis F).isTopologicalAddGroup
  have : ContinuousConstSMul 𝕜 F :=
    @ContinuousSMul.continuousConstSMul 𝕜 F
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ _ IsQuasiSeminorm.continuousSMul
  let S : E →L[𝕜] F := { T.toLinearMap with cont := T.continuous }
  exact S.range_eq_topologicalClosure_span_image s hs T.isClosed_range

/-- Let `T : E → F` be a linear quasi-norm isometry from a complete quasi-seminormed space `E`
to a quasi-normed space `F`. If `closure(span{eᵢ | i ∈ ι}) = E` and `T(eᵢ) = c • fᵢ` for a
fixed `c ≠ 0`, then `range(T) = closure(span{fᵢ | i ∈ ι})`. -/
theorem range_eq_quasiTopologicalClosure_span_of_smul {ι : Type*}
    [QuasiSeminormCompleteSpace E]
    (T : QuasiLinearIsometry 𝕜 E F) (e : ι → E) (f : ι → F)
    (he : @Dense E (IsQuasiSeminorm.topology E)
      (Submodule.span 𝕜 (Set.range e) : Set E))
    (c : 𝕜) (hc : c ≠ 0) (hT : ∀ i, T (e i) = c • f i) :
    LinearMap.range T.toLinearMap =
      (Submodule.span 𝕜 (Set.range f)).quasiTopologicalClosure := by
  rw [T.range_eq_quasiTopologicalClosure_span_image (Set.range e) he]
  simp_rw [← Set.range_comp, Function.comp_def, hT]
  rw [Set.range_smul, Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr hc)]

end ClosedSpan

end QuasiLinearIsometry
