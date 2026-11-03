/-
Authors: Pedro Tradacete
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.ClosedSubalgebra

/-!
# Measure-preserving Boolean homomorphisms

A Boolean homomorphism `f: B → C` which preserves finite measures that are faithful, meaning that
measure zero is equivalent to the empty set, is an isometric embedding with respect to the measure
metrics.
If `A ⊆ B` is a sigma-complete subalgebra, then its image `f '' A` is a sigma-complete subalgebra
of `C`.
This can be used to transport the target of a partial measure-algebra equivalence.
-/

noncomputable section

universe u v w

namespace MeasureAlgebra

variable {B : Type u} {C : Type v}
  [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
  {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}
  (f : BoundedLatticeHom B C) (hf : ∀ b, ν (f b) = μ b)

include hf

/-- A measure-preserving Boolean homomorphism is isometric in the measure metrics. -/
theorem isometry_of_map_measure :
    letI := μ.toMetricSpace
    letI := ν.toMetricSpace
    Isometry f := by
  let := μ.toMetricSpace
  let := ν.toMetricSpace
  apply isometry_iff_dist_eq.mpr
  intro a b
  simp only [dist_eq_measure_symmDiff]
  rw [← map_symmDiff' f, hf]

/-- Measure-preserving Boolean homomorphisms send sigma-complete subalgebras
to sigma-complete subalgebras. -/
theorem isSigmaComplete_map (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) :
    (A.map f).IsSigmaComplete := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := μ.toMetricSpace
  let := ν.toMetricSpace
  let := μ.completeSpace_restrictToSubalgebra_induced A hA
  apply (ν.isClosedSubalgebra_iff_isSigmaComplete (A.map f)).mp
  change IsClosed (f '' (A : Set B))
  rw [Set.image_eq_range]
  exact ((isometry_of_map_measure f hf).comp isometry_subtype_coe).isUniformInducing
    |>.isComplete_range.isClosed

/-- A measure-preserving Boolean homomorphism identifies a sigma-complete subalgebra
with its image as a measure algebra. -/
def mapEquiv (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := (isSigmaComplete_map f hf A hA).toSigmaCompleteBooleanAlgebra
    MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
      (ν.restrictToSubalgebra (A.map f) (isSigmaComplete_map f hf A hA)) := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := (isSigmaComplete_map f hf A hA).toSigmaCompleteBooleanAlgebra
  let := μ.toMetricSpace
  let := ν.toMetricSpace
  have hinj : Function.Injective f := (isometry_of_map_measure f hf).injective
  let i : A ↪o A.map f :=
    { toFun := fun a ↦ ⟨f a, A.apply_coe_mem_map f a⟩
      inj' := fun a b h ↦ Subtype.ext (hinj (congrArg Subtype.val h))
      map_rel_iff' := (orderEmbeddingOfInjective f hinj).map_rel_iff }
  have hi : Function.Surjective i := fun ⟨c, hc⟩ ↦
    let ⟨a, ha, hac⟩ := hc
    ⟨⟨a, ha⟩, Subtype.ext hac⟩
  exact { OrderIso.ofSurjective i hi with map_measure' := fun a ↦ hf a }

/-- Applying the equivalence to an element of `A` and coercing the result to `C` gives its
image under `f`. -/
@[simp]
theorem coe_mapEquiv (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := (isSigmaComplete_map f hf A hA).toSigmaCompleteBooleanAlgebra
    (((mapEquiv f hf A hA).toRelIso a : A.map f) : C) = f a := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := (isSigmaComplete_map f hf A hA).toSigmaCompleteBooleanAlgebra
  rfl

/-- Applying the inverse equivalence to the image of an element of `A` and coercing
the result to `B` recovers the original element. -/
@[simp]
theorem coe_mapEquiv_symm_apply (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := (isSigmaComplete_map f hf A hA).toSigmaCompleteBooleanAlgebra
    (((mapEquiv f hf A hA).symm.toRelIso ⟨f a, A.apply_coe_mem_map f a⟩ : A) : B) = a := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := (isSigmaComplete_map f hf A hA).toSigmaCompleteBooleanAlgebra
  exact congrArg Subtype.val ((mapEquiv f hf A hA).left_inv a)

namespace PartialEquiv

variable {D : Type w} [SigmaCompleteBooleanAlgebra D] {ξ : MeasureAlgebra D}

/-- Transport the target of a partial equivalence through a measure-preserving
Boolean homomorphism. -/
def mapTarget (e : PartialEquiv ξ μ) : PartialEquiv ξ ν := by
  let := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let htarget := isSigmaComplete_map f hf e.target e.target_isSigmaComplete
  let := htarget.toSigmaCompleteBooleanAlgebra
  let g := mapEquiv f hf e.target e.target_isSigmaComplete
  exact
    { source := e.source
      target := e.target.map f
      source_isSigmaComplete := e.source_isSigmaComplete
      target_isSigmaComplete := htarget
      toMeasureAlgebraEquiv :=
        { e.toOrderIso.trans g.toRelIso with
          map_measure' := fun a ↦ (g.map_measure (e.toOrderIso a)).trans (e.map_measure a) } }

/-- Transporting the target leaves the source subalgebra unchanged. -/
theorem mapTarget_source (e : PartialEquiv ξ μ) :
    (mapTarget f hf e).source = e.source := rfl

/-- The transported partial equivalence acts by composing with the Boolean homomorphism. -/
@[simp]
theorem coe_mapTarget_toOrderIso (e : PartialEquiv ξ μ) (a : e.source) :
    ((mapTarget f hf e).toOrderIso a : C) = f (e.toOrderIso a : B) := rfl

omit hf in
/-- A partial equivalence defined on the entire source is a Boolean homomorphism
into the ambient target algebra. -/
def toHom (e : PartialEquiv μ ν) (he : e.source = ⊤) : BoundedLatticeHom B C where
  toFun b := (e.toOrderIso ⟨b, he ▸ BooleanSubalgebra.mem_top⟩ : C)
  map_sup' a b := congrArg Subtype.val (e.toOrderIso.map_sup ⟨a, _⟩ ⟨b, _⟩)
  map_inf' a b := congrArg Subtype.val (e.toOrderIso.map_inf ⟨a, _⟩ ⟨b, _⟩)
  map_top' := congrArg Subtype.val e.toOrderIso.map_top
  map_bot' := congrArg Subtype.val e.toOrderIso.map_bot

omit hf in
/-- The homomorphism associated with a full-source partial equivalence preserves measure. -/
@[simp]
theorem measure_toHom (e : PartialEquiv μ ν) (he : e.source = ⊤) (b : B) :
    ν (e.toHom he b) = μ b :=
  e.map_measure ⟨b, he ▸ BooleanSubalgebra.mem_top⟩

end PartialEquiv

end MeasureAlgebra
