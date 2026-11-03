/-
Authors: Pedro Tradacete
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Hom
import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.Extension

/-!
# Extending measure-algebra embeddings

Partial measure-algebra equivalences extend to embeddings into a homogeneous measure
algebra whose Maharam type is sufficiently large. The extension
preserves the prescribed map on the initial subalgebra.
-/

noncomputable section

universe u

namespace MeasureAlgebra.PartialEquiv

variable {B C : Type u} [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
  {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

private lemma extends_antisymm {e f : PartialEquiv μ ν}
    (hef : e.Extends f) (hfe : f.Extends e) : e = f := by
  obtain ⟨A, D, hA, hD, e⟩ := e
  obtain ⟨A', D', hA', hD', f⟩ := f
  have hAA : A = A' := le_antisymm hef.source_le hfe.source_le
  have hDD : D = D' := le_antisymm hef.target_le hfe.target_le
  subst A' D'
  congr 1
  cases e
  cases f
  congr 1
  apply DFunLike.ext
  exact fun a ↦ Subtype.ext (hef.map_eq a).symm

private abbrev extensionOrder : PartialOrder (PartialEquiv μ ν) where
  le := Extends
  le_refl := Extends.refl
  le_trans _ _ _ := Extends.trans
  le_antisymm _ _ := extends_antisymm

attribute [local instance] extensionOrder

private lemma chain_bounded (s : Set (PartialEquiv μ ν))
    (hs : IsChain (· ≤ ·) s) (hne : s.Nonempty) : BddAbove s := by
  classical
  let : Nonempty s := hne.to_subtype
  let : LinearOrder s := hs.lt_of_le.linearOrder
  obtain ⟨f, hf, _⟩ := exists_extension_iUnion (fun e : s ↦ e.1) (fun _ _ h ↦ h)
  exact ⟨f, fun e he ↦ hf ⟨e, he⟩⟩

private lemma target_density_le (e : PartialEquiv μ ν) :
    ν.subalgebraDensityCharacter e.target ≤ Cardinal.mk B := by
  let := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  rw [← ν.restrictToSubalgebra_densityCharacter_eq_subalgebraDensityCharacter
      e.target e.target_isSigmaComplete]
  have h := e.toMeasureAlgebraEquiv.densityCharacter_eq
  simp only [Cardinal.lift_id] at h
  rw [h]
  let := (μ.restrictToSubalgebra e.source e.source_isSigmaComplete).toMetricSpace
  exact (TopologicalSpace.densityCharacter_le_card e.source).trans
    (Cardinal.mk_subtype_le _)

private lemma exists_extension_mem (e : PartialEquiv μ ν) (hν : ν.IsHomogeneous)
    (hcard : Cardinal.mk B < ν.maharamType) (b : B) :
    ∃ f : PartialEquiv μ ν, e.Extends f ∧ b ∈ f.source := by
  let := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  have hrel : e.target.IsRelativelyAtomless :=
    isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt
      ν e.target e.target_isSigmaComplete hν ((target_density_le e).trans_lt hcard)
  obtain ⟨c, f, hf, _⟩ := exists_extension_of_isRelativelyAtomless μ ν e.source e.target
    e.source_isSigmaComplete e.target_isSigmaComplete hrel e.toMeasureAlgebraEquiv b
  let g : PartialEquiv μ ν :=
    { source := e.source.adjoin b
      target := e.target.adjoin c
      source_isSigmaComplete := e.source_isSigmaComplete.adjoin b
      target_isSigmaComplete := e.target_isSigmaComplete.adjoin c
      toMeasureAlgebraEquiv := f }
  exact ⟨g, ⟨e.source.le_adjoin b, e.target.le_adjoin c, hf⟩, e.source.mem_adjoin b⟩

/-- A partial equivalence extends to the entire source when the target is homogeneous
and its Maharam type exceeds the cardinality of the source. -/
theorem exists_extension_source_eq_top (e : PartialEquiv μ ν) (hν : ν.IsHomogeneous)
    (hcard : Cardinal.mk B < ν.maharamType) :
    ∃ f : PartialEquiv μ ν, e.Extends f ∧ f.source = ⊤ := by
  obtain ⟨f, hef, hf⟩ := zorn_le_nonempty_Ici₀ e
    (fun s _ hs x hx ↦ chain_bounded s hs ⟨x, hx⟩) e le_rfl
  refine ⟨f, hef, top_unique fun b _ ↦ ?_⟩
  obtain ⟨g, hfg, hbg⟩ := exists_extension_mem f hν hcard b
  exact (hf hfg).source_le hbg

end MeasureAlgebra.PartialEquiv

namespace MeasureAlgebra

variable {B C : Type u} [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
  {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

/-- A partial measure-algebra equivalence extends to a measure-preserving Boolean
homomorphism into a homogeneous target of sufficiently large Maharam type. -/
theorem exists_hom_extending_partialEquiv (e : PartialEquiv μ ν) (hν : ν.IsHomogeneous)
    (hcard : Cardinal.mk B < ν.maharamType) :
    ∃ f : BoundedLatticeHom B C, (∀ b, ν (f b) = μ b) ∧
      ∀ a : e.source, f a = (e.toOrderIso a : C) := by
  obtain ⟨g, heg, hg⟩ := e.exists_extension_source_eq_top hν hcard
  exact ⟨g.toHom hg, g.measure_toHom hg, heg.map_eq⟩

end MeasureAlgebra
