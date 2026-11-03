/-
Authors: Pedro Tradacete
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.Embedding
import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.LebesgueCube
import BanLat.Examples.Lp.MeasureAlgebraEmbedding
import BanLat.Examples.Lp.MeasureAlgebraMap

/-!
# Amalgamation of measure-algebra identifications in `Lᵖ`

An identification of sigma-complete subalgebras of two probability measure algebras
can be realized by isometric lattice embeddings of their `Lᵖ` spaces into an `Lᵖ` space over
a Lebesgue cube (the product of `κ` copies of Lebesgue measure on the unit interval as a product
measure).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

universe u

namespace MeasureAlgebra.PartialEquiv

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {p : ℝ≥0} [Fact (1 ≤ p)]

/-- A partial equivalence of probability measure algebras is realized by compatible
isometric lattice embeddings into `Lᵖ` of a common Lebesgue cube. -/
theorem exists_lp_amalgam (e : PartialEquiv (ofMeasure μ) (ofMeasure ν)) :
    ∃ (κ : Cardinal.{u})
      (T : VecLatHom (Lp ℝ (p : ℝ≥0∞) μ) (Lp ℝ (p : ℝ≥0∞) (cubeMeasure κ)))
      (S : VecLatHom (Lp ℝ (p : ℝ≥0∞) ν) (Lp ℝ (p : ℝ≥0∞) (cubeMeasure κ))),
      Isometry T ∧ Isometry S ∧ ∀ (a : e.source) (c : ℝ),
        T (Lp.indicatorSimpleFunc (p := p) (a : InducedBooleanAlgebra μ) c) =
          S (Lp.indicatorSimpleFunc (p := p) (e.toOrderIso a : InducedBooleanAlgebra ν) c) := by
  let κ := Order.succ
    (max (Cardinal.mk (InducedBooleanAlgebra μ)) (Cardinal.mk (InducedBooleanAlgebra ν)))
  have hκ : 0 < κ := bot_lt_iff_ne_bot.mpr (Cardinal.succ_ne_zero _)
  have hcard : max (Cardinal.mk (InducedBooleanAlgebra μ))
      (Cardinal.mk (InducedBooleanAlgebra ν)) < (cubeMeasureAlgebra κ).maharamType :=
    (Order.lt_succ _).trans_le
      ((le_max_right _ κ).trans_eq (cubeMeasureAlgebra_maharamType κ hκ).symm)
  let e₀ : PartialEquiv (ofMeasure ν) (cubeMeasureAlgebra κ) :=
    ofMeasureTopEq ((ofMeasure_top ν).trans
      ((measure_univ : ν Set.univ = 1).trans (cubeMeasureAlgebra_top κ).symm))
  obtain ⟨g, _, hg⟩ := e₀.exists_extension_source_eq_top
    (cubeMeasureAlgebra_isHomogeneous κ hκ) ((le_max_right _ _).trans_lt hcard)
  let e' := mapTarget (g.toHom hg) (g.measure_toHom hg) e
  obtain ⟨f, hef, hf⟩ := e'.exists_extension_source_eq_top
    (cubeMeasureAlgebra_isHomogeneous κ hκ) ((le_max_left _ _).trans_lt hcard)
  refine ⟨κ, f.lpHom hf, g.lpHom hg, f.isometry_lpHom hf, g.isometry_lpHom hg, ?_⟩
  intro a c
  exact (f.lpHom_indicatorSimpleFunc hf a c).trans
    ((congrArg (fun b ↦ (Lp.indicatorSimpleFunc (p := p) b c :
      Lp ℝ (p : ℝ≥0∞) (cubeMeasure κ))) (hef.map_eq a)).trans
        (g.lpHom_indicatorSimpleFunc hg (e.toOrderIso a) c).symm)

private def commonRangeEquiv {B C D : Type u}
    [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
    [SigmaCompleteBooleanAlgebra D] {ξ : MeasureAlgebra B} {η : MeasureAlgebra C}
    {ζ : MeasureAlgebra D} (f : BoundedLatticeHom B C) (g : BoundedLatticeHom B D)
    (hf : ∀ b, η (f b) = ξ b) (hg : ∀ b, ζ (g b) = ξ b) : PartialEquiv η ζ := by
  let htop := BooleanSubalgebra.isSigmaComplete_top (B := B)
  let hA := isSigmaComplete_map f hf ⊤ htop
  let hD := isSigmaComplete_map g hg ⊤ htop
  let := htop.toSigmaCompleteBooleanAlgebra
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  let ef := mapEquiv f hf ⊤ htop
  let eg := mapEquiv g hg ⊤ htop
  exact
    { source := BooleanSubalgebra.map f ⊤
      target := BooleanSubalgebra.map g ⊤
      source_isSigmaComplete := hA
      target_isSigmaComplete := hD
      toMeasureAlgebraEquiv :=
        { ef.symm.toRelIso.trans eg.toRelIso with
          map_measure' := fun a ↦ (eg.map_measure (ef.symm a)).trans (ef.symm.map_measure a) } }

private lemma commonRangeEquiv_apply {B C D : Type u}
    [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
    [SigmaCompleteBooleanAlgebra D] {ξ : MeasureAlgebra B} {η : MeasureAlgebra C}
    {ζ : MeasureAlgebra D} (f : BoundedLatticeHom B C) (g : BoundedLatticeHom B D)
    (hf : ∀ b, η (f b) = ξ b) (hg : ∀ b, ζ (g b) = ξ b) (a : B) :
    ((commonRangeEquiv f g hf hg).toOrderIso
      ⟨f a, ⟨a, BooleanSubalgebra.mem_top, rfl⟩⟩ : D) = g a :=
  congrArg g (coe_mapEquiv_symm_apply f hf ⊤ BooleanSubalgebra.isSigmaComplete_top
    ⟨a, BooleanSubalgebra.mem_top⟩)

end MeasureAlgebra.PartialEquiv

namespace MeasureTheory.Lp

variable {α : Type u} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]

private lemma hom_ext_indicators (R S : VecLatHom (Lp ℝ 1 μ) Y)
    (h : ∀ (a : MeasureAlgebra.InducedBooleanAlgebra μ) (c : ℝ),
      R (indicatorSimpleFunc (p := 1) a c) = S (indicatorSimpleFunc (p := 1) a c)) :
    R = S := by
  apply DFunLike.ext
  refine Lp.induction ENNReal.one_ne_top (fun x ↦ R x = S x)
    (fun c s hs _ ↦ h (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) c) ?_
    (isClosed_eq R.toContinuousLinearMap.continuous S.toContinuousLinearMap.continuous)
  intro f g hf hg _ hRf hRg
  simp only [map_add, hRf, hRg]

/-- Isometric lattice embeddings of probability `L¹` spaces that preserve the constant one function
admit a commuting amalgam by isometric lattice embeddings. -/
theorem exists_isometric_amalgam_of_map_const
    {α₀ α₁ α₂ : Type u} [MeasurableSpace α₀] [MeasurableSpace α₁] [MeasurableSpace α₂]
    {μ₀ : Measure α₀} {μ₁ : Measure α₁} {μ₂ : Measure α₂}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (T₁ : VecLatHom (Lp ℝ 1 μ₀) (Lp ℝ 1 μ₁)) (T₂ : VecLatHom (Lp ℝ 1 μ₀) (Lp ℝ 1 μ₂))
    (h₁ : Isometry T₁) (h₂ : Isometry T₂)
    (hT₁ : T₁ (Lp.const 1 μ₀ (1 : ℝ)) = Lp.const 1 μ₁ (1 : ℝ))
    (hT₂ : T₂ (Lp.const 1 μ₀ (1 : ℝ)) = Lp.const 1 μ₂ (1 : ℝ)) :
    ∃ (κ : Cardinal.{u})
      (S₁ : VecLatHom (Lp ℝ 1 μ₁) (Lp ℝ 1 (MeasureAlgebra.cubeMeasure κ)))
      (S₂ : VecLatHom (Lp ℝ 1 μ₂) (Lp ℝ 1 (MeasureAlgebra.cubeMeasure κ))),
      Isometry S₁ ∧ Isometry S₂ ∧ S₁.comp T₁ = S₂.comp T₂ := by
  let f₁ := toMeasureAlgebraHom T₁ hT₁
  let f₂ := toMeasureAlgebraHom T₂ hT₂
  let e := MeasureAlgebra.PartialEquiv.commonRangeEquiv f₁ f₂
    (measure_toMeasureAlgebraHom T₁ hT₁ h₁) (measure_toMeasureAlgebraHom T₂ hT₂ h₂)
  obtain ⟨κ, S₁, S₂, hS₁, hS₂, hcomm⟩ := e.exists_lp_amalgam (p := 1)
  refine ⟨κ, S₁, S₂, hS₁, hS₂, hom_ext_indicators _ _ ?_⟩
  intro a c
  have h := hcomm ⟨f₁ a, ⟨a, BooleanSubalgebra.mem_top, rfl⟩⟩ c
  have he := MeasureAlgebra.PartialEquiv.commonRangeEquiv_apply f₁ f₂
    (measure_toMeasureAlgebraHom T₁ hT₁ h₁) (measure_toMeasureAlgebraHom T₂ hT₂ h₂) a
  have h' := h.trans (congrArg (fun b ↦ S₂ (indicatorSimpleFunc (p := 1) b c)) he)
  exact (congrArg S₁ (map_indicatorSimpleFunc T₁ hT₁ a c)).trans
    (h'.trans (congrArg S₂ (map_indicatorSimpleFunc T₂ hT₂ a c)).symm)

end MeasureTheory.Lp
