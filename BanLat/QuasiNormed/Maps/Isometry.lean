/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.QuasiNormed.Maps.LinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.UniformSpace.Equiv

/-!
# Isometries between quasi-seminormed spaces

For maps between quasi-seminormed spaces, this file introduces:

* Isometries between quasi-seminormed spaces, preserving quasi-seminorms of differences.
* Linear isometries and linear isometric equivalences between quasi-seminormed spaces.

It also establishes uniform continuity, injectivity when the source is quasi-normed,
and closedness of the range when the source is complete and the target is quasi-normed.
For linear isometries between quasi-seminormed spaces, it also identifies the range with the
closed linear span of the image of a family whose linear span is dense in the source.
-/

open IsQuasiSeminorm

attribute [local instance] IsQuasiSeminorm.topology

/-- An isometry between quasi-seminormed spaces preserves quasi-seminorms of differences. -/
structure QuasiSeminormIsometry (E F : Type*)
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F] where
  /-- The underlying function of an isometry between quasi-seminormed spaces. -/
  toFun : E → F
  norm_sub_map' : ∀ x y, ‖toFun x - toFun y‖ = ‖x - y‖

namespace QuasiSeminormIsometry

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-- Isometries between quasi-seminormed spaces can be evaluated as functions. -/
instance instFunLike : FunLike (QuasiSeminormIsometry E F) E F where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/-- An isometry between quasi-seminormed spaces preserves quasi-seminorms of differences. -/
@[simp]
theorem norm_sub_map (f : QuasiSeminormIsometry E F) (x y : E) :
    ‖f x - f y‖ = ‖x - y‖ := by
  exact f.norm_sub_map' x y

/-- Bundle an additive map preserving quasi-seminorms as an isometry between quasi-seminormed
spaces. -/
def ofAddMonoidHom {𝓕 : Type*} [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F]
    (T : 𝓕) (hT : ∀ x, ‖T x‖ = ‖x‖) : QuasiSeminormIsometry E F where
  toFun := T
  norm_sub_map' x y := by simpa only [map_sub] using hT (x - y)

/-- An isometry between quasi-seminormed spaces induces the source quasi-seminorm uniformity. -/
protected theorem isUniformInducing (f : QuasiSeminormIsometry E F) :
    @IsUniformInducing E F (uniformSpace E) (uniformSpace F) f := by
  exact isUniformInducing_of_le_norm_sub_of_norm_sub_le zero_lt_one zero_le_one
    (fun x y ↦ by rw [one_mul, f.norm_sub_map])
    (fun x y ↦ by rw [one_mul, f.norm_sub_map])

/-- An isometry between quasi-seminormed spaces is uniformly continuous for the induced
uniformities. -/
protected theorem uniformContinuous (f : QuasiSeminormIsometry E F) :
    @UniformContinuous E F (uniformSpace E) (uniformSpace F) f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact f.isUniformInducing.uniformContinuous

/-- An isometry between quasi-seminormed spaces is continuous for the induced topologies. -/
protected theorem continuous (f : QuasiSeminormIsometry E F) : Continuous f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact f.uniformContinuous.continuous

end QuasiSeminormIsometry

namespace QuasiSeminormIsometry

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-- An isometry between quasi-seminormed spaces is injective when the source
quasi-seminorm is a quasi-norm. -/
theorem injective (f : QuasiSeminormIsometry E F) : Function.Injective f := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact f.isUniformInducing.isUniformEmbedding.injective

end QuasiSeminormIsometry

namespace QuasiSeminormIsometry

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]

/-- An isometry between quasi-seminormed spaces from a complete source has closed range
when the target quasi-seminorm is a quasi-norm. -/
theorem isClosed_range [QuasiSeminormCompleteSpace E] (f : QuasiSeminormIsometry E F) :
    IsClosed (Set.range f) := by
  exact isClosed_range_of_isUniformInducing f.isUniformInducing

end QuasiSeminormIsometry

/-- An isometric equivalence between quasi-seminormed spaces preserves quasi-seminorms
of differences. -/
structure QuasiSeminormIsometryEquiv (E F : Type*)
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F] extends E ≃ F where
  norm_sub_map' : ∀ x y, ‖toEquiv x - toEquiv y‖ = ‖x - y‖

namespace QuasiSeminormIsometryEquiv

variable {E F : Type*}
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]

/-- Isometric equivalences between quasi-seminormed spaces can be evaluated and inverted as
equivalences. -/
instance instEquivLike : EquivLike (QuasiSeminormIsometryEquiv E F) E F where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact DFunLike.coe_injective h

/-- An isometric equivalence between quasi-seminormed spaces preserves quasi-seminorms of
differences. -/
@[simp]
theorem norm_sub_map (e : QuasiSeminormIsometryEquiv E F) (x y : E) :
    ‖e x - e y‖ = ‖x - y‖ := by
  exact e.norm_sub_map' x y

/-- Forget the inverse of an isometric equivalence between quasi-seminormed spaces. -/
def toQuasiSeminormIsometry (e : QuasiSeminormIsometryEquiv E F) : QuasiSeminormIsometry E F where
  toFun := e
  norm_sub_map' := e.norm_sub_map

/-- The inverse isometric equivalence between quasi-seminormed spaces. -/
def symm (e : QuasiSeminormIsometryEquiv E F) : QuasiSeminormIsometryEquiv F E where
  toEquiv := e.toEquiv.symm
  norm_sub_map' x y := by
    simpa only [Equiv.apply_symm_apply] using
      (e.norm_sub_map' (e.toEquiv.symm x) (e.toEquiv.symm y)).symm

/-- Regard an isometric equivalence between quasi-seminormed spaces as an equivalence of induced
uniform spaces. -/
def toUniformEquiv (e : QuasiSeminormIsometryEquiv E F) :
    @UniformEquiv E F (uniformSpace E) (uniformSpace F) := by
  exact @UniformEquiv.mk E F (uniformSpace E) (uniformSpace F) e.toEquiv
    e.toQuasiSeminormIsometry.uniformContinuous e.symm.toQuasiSeminormIsometry.uniformContinuous

/-- If two quasi-seminormed spaces are isometrically equivalent, then one is complete if and
only if the other is complete. -/
theorem quasiSeminormCompleteSpace_iff (e : QuasiSeminormIsometryEquiv E F) :
    QuasiSeminormCompleteSpace E ↔ QuasiSeminormCompleteSpace F := by
  let : UniformSpace E := uniformSpace E
  let : UniformSpace F := uniformSpace F
  exact e.toUniformEquiv.completeSpace_iff

end QuasiSeminormIsometryEquiv

/-- A linear isometry between quasi-seminormed spaces preserves the quasi-seminorm. -/
structure LinearQuasiSeminormIsometry (R E F : Type*) [Semiring R]
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
    [Module R E] [Module R F] extends E →ₗ[R] F where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖

namespace LinearQuasiSeminormIsometry

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]

/-- Linear isometries between quasi-seminormed spaces can be evaluated as functions. -/
instance instFunLike : FunLike (LinearQuasiSeminormIsometry R E F) E F where
  coe T := T.toLinearMap
  coe_injective T S h := by
    cases T
    cases S
    congr
    exact DFunLike.coe_injective h

/-- Linear isometries between quasi-seminormed spaces satisfy the existing linear-map interface. -/
instance instLinearMapClass :
    LinearMapClass (LinearQuasiSeminormIsometry R E F) R E F where
  map_add T := T.toLinearMap.map_add
  map_smulₛₗ T := T.toLinearMap.map_smul

/-- A linear isometry between quasi-seminormed spaces preserves quasi-seminorms. -/
@[simp]
theorem norm_map (T : LinearQuasiSeminormIsometry R E F) (x : E) :
    ‖T x‖ = ‖x‖ := by
  exact T.norm_map' x

/-- Forget the linear structure of a linear isometry between quasi-seminormed spaces. -/
def toQuasiSeminormIsometry (T : LinearQuasiSeminormIsometry R E F) :
    QuasiSeminormIsometry E F := by
  exact QuasiSeminormIsometry.ofAddMonoidHom T T.norm_map

/-- A linear isometry between quasi-seminormed spaces is continuous for the induced topologies. -/
protected theorem continuous (T : LinearQuasiSeminormIsometry R E F) : Continuous T := by
  exact T.toQuasiSeminormIsometry.continuous

end LinearQuasiSeminormIsometry

namespace LinearQuasiSeminormIsometry

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiNorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]

/-- A linear isometry between quasi-seminormed spaces is injective when the source
quasi-seminorm is a quasi-norm. -/
theorem injective (T : LinearQuasiSeminormIsometry R E F) : Function.Injective T := by
  exact T.toQuasiSeminormIsometry.injective

end LinearQuasiSeminormIsometry

namespace LinearQuasiSeminormIsometry

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F]
  [Module R E] [Module R F]

/-- A linear isometry between quasi-seminormed spaces from a complete source has closed range
when the target quasi-seminorm is a quasi-norm. -/
theorem isClosed_range [QuasiSeminormCompleteSpace E] (T : LinearQuasiSeminormIsometry R E F) :
    IsClosed (Set.range T) := by
  exact T.toQuasiSeminormIsometry.isClosed_range

end LinearQuasiSeminormIsometry

/-- A linear isometric equivalence between quasi-seminormed spaces preserves the
quasi-seminorm. -/
structure LinearQuasiSeminormIsometryEquiv (R E F : Type*) [Semiring R]
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
    [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
    [Module R E] [Module R F] extends E ≃ₗ[R] F where
  norm_map' : ∀ x, ‖toLinearEquiv x‖ = ‖x‖

namespace LinearQuasiSeminormIsometryEquiv

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F]
  [Module R E] [Module R F]

/-- Linear isometric equivalences between quasi-seminormed spaces can be evaluated and inverted as
equivalences. -/
instance instEquivLike : EquivLike (LinearQuasiSeminormIsometryEquiv R E F) E F where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact DFunLike.coe_injective h

/-- Linear isometric equivalences between quasi-seminormed spaces satisfy the existing linear-map
interface. -/
instance instLinearMapClass :
    LinearMapClass (LinearQuasiSeminormIsometryEquiv R E F) R E F where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

/-- A linear isometric equivalence between quasi-seminormed spaces preserves quasi-seminorms. -/
@[simp]
theorem norm_map (e : LinearQuasiSeminormIsometryEquiv R E F) (x : E) :
    ‖e x‖ = ‖x‖ := by
  exact e.norm_map' x

/-- Forget linearity while retaining the isometric equivalence between quasi-seminormed spaces. -/
def toQuasiSeminormIsometryEquiv (e : LinearQuasiSeminormIsometryEquiv R E F) :
    QuasiSeminormIsometryEquiv E F where
  toEquiv := e.toLinearEquiv.toEquiv
  norm_sub_map' x y := by
    change ‖e.toLinearEquiv x - e.toLinearEquiv y‖ = ‖x - y‖
    simpa only [map_sub] using e.norm_map' (x - y)

end LinearQuasiSeminormIsometryEquiv

namespace LinearQuasiSeminormIsometry

open scoped QuasiNormedSubmodule

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Norm E] [IsQuasiNorm E] [QuasiNormedSpace 𝕜 E]
  [AddCommGroup F] [Norm F] [IsQuasiSeminorm F] [QuasiNormedSpace 𝕜 F]

/-- A linear isometry between quasi-seminormed spaces defines a linear isometric equivalence
with its range when the source quasi-seminorm is a quasi-norm. -/
noncomputable def equivRange (T : LinearQuasiSeminormIsometry 𝕜 E F) :
    LinearQuasiSeminormIsometryEquiv 𝕜 E (LinearMap.range T.toLinearMap) where
  toLinearEquiv := LinearEquiv.ofInjective T.toLinearMap T.injective
  norm_map' := T.norm_map'

/-- The equivalence with the linear range has the original ambient-space values. -/
@[simp]
theorem equivRange_apply_coe (T : LinearQuasiSeminormIsometry 𝕜 E F) (x : E) :
    ((T.equivRange x : LinearMap.range T.toLinearMap) : F) = T x := by
  rfl

end LinearQuasiSeminormIsometry

section Seminormed

variable {R E F : Type*} [Semiring R]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- Regard an ordinary linear isometry as a linear isometry between quasi-seminormed spaces. -/
def LinearQuasiSeminormIsometry.ofLinearIsometry (T : E →ₗᵢ[R] F) :
    LinearQuasiSeminormIsometry R E F where
  toLinearMap := T.toLinearMap
  norm_map' := T.norm_map

/-- Regard a `LinearQuasiSeminormIsometry` between seminormed groups as an ordinary
linear isometry. -/
def LinearQuasiSeminormIsometry.toLinearIsometry (T : LinearQuasiSeminormIsometry R E F) :
    E →ₗᵢ[R] F where
  toLinearMap := T.toLinearMap
  norm_map' := T.norm_map

/-- Regard a linear isometric equivalence between quasi-seminormed spaces as an ordinary linear
isometric equivalence. -/
def LinearQuasiSeminormIsometryEquiv.toLinearIsometryEquiv
    (e : LinearQuasiSeminormIsometryEquiv R E F) :
    E ≃ₗᵢ[R] F where
  toLinearEquiv := e.toLinearEquiv
  norm_map' := e.norm_map

end Seminormed

namespace LinearQuasiSeminormIsometry

section ClosedSpan

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]
  [QuasiNormedSpace 𝕜 E]
  [AddCommGroup F] [Norm F] [IsQuasiNorm F] [QuasiNormedSpace 𝕜 F]

/-- Let `T : E → F` be a linear isometry from a complete quasi-seminormed vector
space `E` to a quasi-normed vector space `F`. If `closure(span(s)) = E`, then
`range(T) = closure(span(T(s)))`. -/
theorem range_eq_quasiTopologicalClosure_span_image
    [QuasiSeminormCompleteSpace E]
    (T : LinearQuasiSeminormIsometry 𝕜 E F) (s : Set E)
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

/-- Let `T : E → F` be a linear isometry from a complete quasi-seminormed vector
space `E` to a quasi-normed vector space `F`. If `closure(span{eᵢ | i ∈ ι}) = E` and
`T(eᵢ) = c • fᵢ` for a fixed `c ≠ 0`, then `range(T) = closure(span{fᵢ | i ∈ ι})`. -/
theorem range_eq_quasiTopologicalClosure_span_of_smul {ι : Type*}
    [QuasiSeminormCompleteSpace E]
    (T : LinearQuasiSeminormIsometry 𝕜 E F) (e : ι → E) (f : ι → F)
    (he : @Dense E (IsQuasiSeminorm.topology E)
      (Submodule.span 𝕜 (Set.range e) : Set E))
    (c : 𝕜) (hc : c ≠ 0) (hT : ∀ i, T (e i) = c • f i) :
    LinearMap.range T.toLinearMap =
      (Submodule.span 𝕜 (Set.range f)).quasiTopologicalClosure := by
  rw [T.range_eq_quasiTopologicalClosure_span_image (Set.range e) he]
  simp_rw [← Set.range_comp, Function.comp_def, hT]
  rw [Set.range_smul, Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr hc)]

end ClosedSpan

end LinearQuasiSeminormIsometry
