/-
Authors: Pedro Tradacete
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.OfSubalgebra
import BanLat.Examples.Lp.MeasureAlgebra

/-!
# Embeddings induced by partial measure-algebra equivalences

A partial measure-algebra equivalence defined on its entire source induces a lattice
isometry into the target `Lᵖ` space. The construction first identifies the image
subalgebra with a sigma-algebra and then uses transport through measure-algebra equivalences.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

universe u v

namespace MeasureTheory.Lp

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

/-- Composition with a measure-preserving function as a vector lattice homomorphism. -/
def compMeasurePreservingVecLatHom (f : α → β) (hf : MeasurePreserving f μ ν) :
    VecLatHom (Lp ℝ p ν) (Lp ℝ p μ) := by
  refine VecLatHom.ofAbs (compMeasurePreservingₗ ℝ f hf) fun x ↦ ?_
  apply Lp.ext
  filter_upwards [coeFn_compMeasurePreserving |x| hf, coeFn_compMeasurePreserving x hf,
    (Lp.coeFn_abs x).comp_tendsto hf.quasiMeasurePreserving.tendsto_ae,
    Lp.coeFn_abs (compMeasurePreserving f hf x)] with a h₁ h₂ h₃ h₄
  exact h₁.trans (h₃.trans ((congrArg abs h₂).symm.trans h₄.symm))

end MeasureTheory.Lp

namespace MeasureAlgebra.PartialEquiv

private def fullSourceEquiv
    {B : Type u} {C : Type v} [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
    {μ : MeasureAlgebra B} {ν : MeasureAlgebra C} (e : PartialEquiv μ ν) (he : e.source = ⊤) :
    letI := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
    MeasureAlgebraEquiv μ (ν.restrictToSubalgebra e.target e.target_isSigmaComplete) := by
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  exact
    { toFun := fun b ↦ e.toOrderIso ⟨b, he ▸ BooleanSubalgebra.mem_top⟩
      invFun := fun c ↦ (e.toOrderIso.symm c : B)
      left_inv := fun b ↦ congrArg Subtype.val (e.toOrderIso.left_inv ⟨b, _⟩)
      right_inv := fun c ↦ e.toOrderIso.right_inv c
      map_rel_iff' := e.toOrderIso.map_rel_iff
      map_measure' := fun b ↦ e.map_measure ⟨b, _⟩ }

variable {α : Type u} {β : Type v} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (e : PartialEquiv (ofMeasure μ) (ofMeasure ν)) (he : e.source = ⊤)

private def trimmedEquiv :
    MeasureAlgebraEquiv (ofMeasure μ)
      (@ofMeasure β (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
        (subalgebraMeasure e.target e.target_isSigmaComplete) _) := by
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let f := fullSourceEquiv e he
  let g := (subalgebraMeasureEquiv e.target e.target_isSigmaComplete).symm
  exact
    { f.toRelIso.trans g.toRelIso with
      map_measure' := fun a ↦ (g.map_measure (f a)).trans (f.map_measure a) }

private lemma measurePreserving_id :
    @MeasurePreserving β β mβ (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
      id ν (subalgebraMeasure e.target e.target_isSigmaComplete) :=
  @MeasurePreserving.mk β β mβ
    (subalgebraMeasurableSpace e.target e.target_isSigmaComplete) id ν
    (subalgebraMeasure e.target e.target_isSigmaComplete)
    (measurable_id'' (subalgebraMeasurableSpace_le e.target e.target_isSigmaComplete))
    (trim_eq_map (subalgebraMeasurableSpace_le e.target e.target_isSigmaComplete)).symm

variable {p : ℝ≥0} [Fact (1 ≤ p)]

private def trimmedLpEquiv :
    BanachLatEquiv (Lp ℝ (p : ℝ≥0∞) μ)
      (@Lp β ℝ (subalgebraMeasurableSpace e.target e.target_isSigmaComplete) _ (p : ℝ≥0∞)
        (subalgebraMeasure e.target e.target_isSigmaComplete)) :=
  @MeasureAlgebraEquiv.lpEquiv α β mα
    (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
    μ (subalgebraMeasure e.target e.target_isSigmaComplete) _ _ p _ (trimmedEquiv e he)

private def trimmedInclusion :
    VecLatHom
      (@Lp β ℝ (subalgebraMeasurableSpace e.target e.target_isSigmaComplete) _ (p : ℝ≥0∞)
        (subalgebraMeasure e.target e.target_isSigmaComplete)) (Lp ℝ (p : ℝ≥0∞) ν) :=
  @Lp.compMeasurePreservingVecLatHom β β mβ
    (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
    ν (subalgebraMeasure e.target e.target_isSigmaComplete) (p : ℝ≥0∞) id
      (measurePreserving_id e)

/-- A full-source partial measure-algebra equivalence induces a vector lattice
homomorphism between the corresponding `Lᵖ` spaces. -/
def lpHom : VecLatHom (Lp ℝ (p : ℝ≥0∞) μ) (Lp ℝ (p : ℝ≥0∞) ν) :=
  (trimmedInclusion e).comp
    (trimmedLpEquiv e he).toVecLatEquiv.toVecLatHom

omit [Fact (1 ≤ p)] in
private lemma trimmedInclusion_indicatorConstLp {s : Set β}
    (hs : @MeasurableSet β
      (subalgebraMeasurableSpace e.target e.target_isSigmaComplete) s) (c : ℝ) :
    trimmedInclusion (p := p) e
      (indicatorConstLp (m := subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
        (p : ℝ≥0∞) hs
        (@MeasureTheory.measure_ne_top β
          (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
          (subalgebraMeasure e.target e.target_isSigmaComplete) _ s) c) =
      indicatorConstLp (p : ℝ≥0∞)
        (subalgebraMeasurableSpace_le e.target e.target_isSigmaComplete _ hs)
        (MeasureTheory.measure_ne_top ν s) c := by
  apply Lp.ext
  exact (@Lp.coeFn_compMeasurePreserving β ℝ mβ (p : ℝ≥0∞) ν _ β
    (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
    (subalgebraMeasure e.target e.target_isSigmaComplete) id _ (measurePreserving_id e)).trans
    ((ae_eq_of_ae_eq_trim (indicatorConstLp_coeFn (hs := hs))).trans
      indicatorConstLp_coeFn.symm)

private lemma trimmedEquiv_mk (s : MeasuredSets μ)
    (t : @MeasuredSets β (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
      (subalgebraMeasure e.target e.target_isSigmaComplete))
    (hst : (e.toOrderIso ⟨InducedBooleanAlgebra.mk μ s, he ▸ BooleanSubalgebra.mem_top⟩ :
      InducedBooleanAlgebra ν) =
        InducedBooleanAlgebra.mk ν
          ⟨t, subalgebraMeasurableSpace_le e.target e.target_isSigmaComplete _ t.property⟩) :
    trimmedEquiv e he (InducedBooleanAlgebra.mk μ s) =
      @InducedBooleanAlgebra.mk β
        (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
        (subalgebraMeasure e.target e.target_isSigmaComplete) t := by
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  apply (subalgebraMeasureEquiv e.target e.target_isSigmaComplete).toRelIso.injective
  change (subalgebraMeasureEquiv e.target e.target_isSigmaComplete).toRelIso
    ((subalgebraMeasureEquiv e.target e.target_isSigmaComplete).toRelIso.symm
      (fullSourceEquiv e he (InducedBooleanAlgebra.mk μ s))) = _
  exact ((subalgebraMeasureEquiv e.target e.target_isSigmaComplete).toRelIso.apply_symm_apply
    _).trans (Subtype.ext hst)

/-- The lattice homomorphism induced by a full-source partial equivalence is isometric. -/
theorem isometry_lpHom : Isometry (lpHom (p := p) e he) := by
  apply AddMonoidHomClass.isometry_of_norm (lpHom (p := p) e he).toLinearMap
  intro x
  exact (@Lp.norm_compMeasurePreserving β ℝ mβ (p : ℝ≥0∞) ν _ β
    (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
    (subalgebraMeasure e.target e.target_isSigmaComplete) id _ (measurePreserving_id e)).trans
    ((trimmedLpEquiv e he).toLinearIsometryEquiv.norm_map x)

/-- The induced lattice embedding sends each constant indicator to the indicator
of the image of its measure-algebra element. -/
theorem lpHom_indicatorSimpleFunc (a : InducedBooleanAlgebra μ) (c : ℝ) :
    lpHom (p := p) e he (Lp.indicatorSimpleFunc (p := p) a c) =
      (Lp.indicatorSimpleFunc (p := p)
        (e.toOrderIso ⟨a, he ▸ BooleanSubalgebra.mem_top⟩ : InducedBooleanAlgebra ν) c :
          Lp ℝ (p : ℝ≥0∞) ν) := by
  obtain ⟨s, rfl⟩ := InducedBooleanAlgebra.mk_surjective μ a
  obtain ⟨t, ht⟩ := InducedBooleanAlgebra.mk_surjective ν
    (e.toOrderIso ⟨InducedBooleanAlgebra.mk μ s, he ▸ BooleanSubalgebra.mem_top⟩ :
      InducedBooleanAlgebra ν)
  have ht' : @MeasurableSet β
      (subalgebraMeasurableSpace e.target e.target_isSigmaComplete) t :=
    ⟨t.property, ht ▸ (e.toOrderIso ⟨InducedBooleanAlgebra.mk μ s,
      he ▸ BooleanSubalgebra.mem_top⟩).property⟩
  have hmap := @MeasureAlgebraEquiv.lpEquiv_indicatorConstLp α β mα
    (subalgebraMeasurableSpace e.target e.target_isSigmaComplete)
    μ (subalgebraMeasure e.target e.target_isSigmaComplete) _ _ p _ (trimmedEquiv e he)
    s t s.property ht' (trimmedEquiv_mk e he s ⟨t, ht'⟩ ht.symm) c
  exact ((congrArg (trimmedInclusion e) hmap).trans
    (trimmedInclusion_indicatorConstLp e ht' c)).trans
    (congrArg (fun b ↦ (Lp.indicatorSimpleFunc (p := p) b c : Lp ℝ (p : ℝ≥0∞) ν)) ht)

end MeasureAlgebra.PartialEquiv
