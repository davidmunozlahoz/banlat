/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Atomless
import BanLat.BooleanAlgebras.MeasureAlgebras.ClosedSubalgebra
import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.MaharamType

open scoped ENNReal
open BooleanSubalgebra

/-!
# Extension machinery for Maharam's theorem

We consider extensions of partial measure-algebra equivalences between homogeneous measure
algebras `(B, μ)` and `(C, η)` with infinite Maharam types.

In particular, if the source and target of the partial measure-algebra equivalence have density
character strictly below the respective Maharam types, then, for any `b ∈ B` and `c ∈ C`, there
is an extension whose source contains `b` and whose target contains `c`, with both strict density
bounds preserved.
-/

universe u v

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- Let `A` be a `σ`-complete Boolean subalgebra of a homogeneous measure algebra
`(B, μ)`. If the density character induced on `A` is less than `μ.maharamType`,
then `B` is relatively atomless with respect to `A`. -/
theorem isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (hμ : μ.IsHomogeneous)
    (hκ : μ.subalgebraDensityCharacter A < μ.maharamType) :
    A.IsRelativelyAtomless := by
  intro b hb
  by_contra hrel
  push Not at hrel
  let := hA.toSigmaCompleteBooleanAlgebra
  let ν := μ.restrictToSubalgebra A hA
  let f : A → Set.Iic b := fun a ↦ ⟨b ⊓ (a : B), inf_le_left⟩
  let := ν.toMetricSpace
  let := (μ.restrict b).toMetricSpace
  have hf : Continuous f := by
    apply Metric.continuous_iff.2
    intro a ε hε
    refine ⟨ε, hε, ?_⟩
    intro a' ha'
    apply lt_of_le_of_lt _ ha'
    change (μ ((symmDiff (f a') (f a) : Set.Iic b) : B)).toReal ≤
      (μ ((symmDiff a' a : A) : B)).toReal
    rw [Set.Iic.coe_symmDiff]
    change (μ (symmDiff (b ⊓ (a' : B)) (b ⊓ (a : B)))).toReal ≤
      (μ (symmDiff (a' : B) (a : B))).toReal
    rw [← inf_symmDiff_distrib_left]
    exact ENNReal.toReal_mono (μ.measure_ne_top _)
      (μ.measure_mono inf_le_right)
  have hfs : Function.Surjective f := by
    intro c
    obtain ⟨a, ha⟩ := hrel (c : B) c.property
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha.symm
  have hle : (μ.restrict b).densityCharacter ≤ μ.subalgebraDensityCharacter A := by
    rw [← μ.restrictToSubalgebra_densityCharacter_eq_subalgebraDensityCharacter A hA]
    exact TopologicalSpace.densityCharacter_le_of_continuous_surjective hf hfs
  apply not_le_of_gt hκ
  rw [← hμ hb]
  exact hle

section

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
variable (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
variable (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete)

/-- Let `A ⊆ (B, μ)` and `D ⊆ (C, η)` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Suppose that `C` is relatively
atomless with respect to `D`. Then, for every `b ∈ B` there is `c ∈ C` such that
`η (d ⊓ c) = μ (e⁻¹(d) ⊓ b)` for every `d ∈ D`. -/
theorem exists_targetElement_of_isRelativelyAtomless
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete)
    (hrel : D.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B),
      ∃ c : C, ∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b) := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  intro e b
  let ρ := CountablyAdditiveFunctional.pullbackFunctional e.symm.toRelIso
    (μ.infFunctional A hA b)
  have hρ : ∀ d : D, ρ d ≤ η (d : C) := by
    intro d
    calc
      ρ d = μ.infFunctional A hA b (e.symm d) := rfl
      _ ≤ μ ((e.symm d : A) : B) := μ.infFunctional_le A hA b (e.symm d)
      _ = η (d : C) := by simpa using e.symm.map_measure d
  obtain ⟨c, hc⟩ :=
    exists_infFunctional_apply_eq_of_isRelativelyAtomless η D hD hrel ρ hρ
  refine ⟨c, ?_⟩
  intro d
  convert hc d using 1
  · exact (infFunctional_apply η D hD c d).symm
  · rfl

/-- The matching intersection measures in `exists_targetElement_of_isRelativelyAtomless`
also match for `bᶜ` and `cᶜ`, by subtracting from the measures preserved by `e`. -/
private lemma compl_inf_measure_eq_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        ∀ d : D, η ((d : C) ⊓ cᶜ) = μ (((e.symm d : A) : B) ⊓ bᶜ) := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc d
  have hη : η ((d : C) ⊓ cᶜ) = η (d : C) - η ((d : C) ⊓ c) := by
    have hsum := η.measure_sdiff_add_inf (d : C) c
    exact ENNReal.eq_sub_of_add_eq' (η.measure_ne_top _) (by
      simpa only [sdiff_eq] using hsum)
  have hμ : μ (((e.symm d : A) : B) ⊓ bᶜ) =
      μ ((e.symm d : A) : B) - μ (((e.symm d : A) : B) ⊓ b) := by
    have hsum := μ.measure_sdiff_add_inf ((e.symm d : A) : B) b
    exact ENNReal.eq_sub_of_add_eq' (μ.measure_ne_top _) (by
      simpa only [sdiff_eq] using hsum)
  have htotal : μ ((e.symm d : A) : B) = η (d : C) := by
    simpa using e.symm.map_measure d
  rw [hη, hμ, hc d, htotal]

/-- Under the same matching intersection measures, `b ⊓ a₁ ≤ b ⊓ a₂` iff
`c ⊓ e(a₁) ≤ c ⊓ e(a₂)`: the corresponding differences have equal measures,
and measure zero is equivalent to being bottom. -/
private lemma inf_le_inf_iff_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        ∀ a₁ a₂ : A,
          b ⊓ (a₁ : B) ≤ b ⊓ (a₂ : B) ↔
            c ⊓ ((e a₁ : D) : C) ≤ c ⊓ ((e a₂ : D) : C) := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc a₁ a₂
  have hm : η (c ⊓ (((e a₁ : D) : C) \ ((e a₂ : D) : C))) =
      μ (b ⊓ ((a₁ : B) \ (a₂ : B))) := by
    have hm' := hc (e (a₁ \ a₂))
    have hinv : e.symm (e (a₁ \ a₂)) = a₁ \ a₂ := e.left_inv _
    have hmap : e (a₁ \ a₂) = e a₁ \ e a₂ := map_sdiff' e.toRelIso _ _
    rw [hinv, hmap] at hm'
    simpa only [BooleanSubalgebra.val_sdiff, inf_comm] using hm'
  calc
    b ⊓ (a₁ : B) ≤ b ⊓ (a₂ : B) ↔
        μ ((b ⊓ (a₁ : B)) \ (b ⊓ (a₂ : B))) = 0 := by
          rw [μ.measure_eq_zero_iff, sdiff_eq_bot_iff]
    _ ↔ μ (b ⊓ ((a₁ : B) \ (a₂ : B))) = 0 := by
      rw [inf_sdiff_distrib_left]
    _ ↔ η (c ⊓ (((e a₁ : D) : C) \ ((e a₂ : D) : C))) = 0 := by rw [hm]
    _ ↔ η ((c ⊓ ((e a₁ : D) : C)) \ (c ⊓ ((e a₂ : D) : C))) = 0 := by
      rw [inf_sdiff_distrib_left]
    _ ↔ c ⊓ ((e a₁ : D) : C) ≤ c ⊓ ((e a₂ : D) : C) := by
      rw [η.measure_eq_zero_iff, sdiff_eq_bot_iff]

/- Let `A ⊆ (B, μ)` and `D ⊆ (C, η)` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Fix `b ∈ B` and `c ∈ C`
such that `η (d ⊓ c) = μ (e⁻¹(d) ⊓ b)` for every `d ∈ D`. Then, for every
`a₁, a₂ ∈ A`,
`η ((c ⊓ e(a₁)) ⊔ (cᶜ ⊓ e(a₂))) = μ ((b ⊓ a₁) ⊔ (bᶜ ⊓ a₂))`. -/
private lemma measure_adjoinValue_eq_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        ∀ p : A × A,
          η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) =
            μ (adjoinValue A b p) := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc p
  have hc_compl :=
    compl_inf_measure_eq_of_inf_measure_eq μ η A D hA hD e b c hc
  have h₁ := hc (e p.1)
  have h₂ := hc_compl (e p.2)
  have hinv₁ : e.symm (e p.1) = p.1 := e.left_inv _
  have hinv₂ : e.symm (e p.2) = p.2 := e.left_inv _
  rw [hinv₁] at h₁
  rw [hinv₂] at h₂
  calc
    η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) =
        η (c ⊓ ((e p.1 : D) : C)) + η (cᶜ ⊓ ((e p.2 : D) : C)) := by
      apply η.measure_sup
      exact disjoint_compl_right.mono inf_le_left inf_le_left
    _ = μ (b ⊓ (p.1 : B)) + μ (bᶜ ⊓ (p.2 : B)) := by
      rw [inf_comm c, h₁, inf_comm cᶜ, h₂]
      congr 1 <;> ac_rfl
    _ = μ (adjoinValue A b p) := by
      symm
      apply μ.measure_sup
      exact disjoint_compl_right.mono inf_le_left inf_le_left

/- Let `A ⊆ (B, μ)` and `D ⊆ (C, η)` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Fix `b ∈ B` and `c ∈ C`
such that `η (d ⊓ c) = μ (e⁻¹(d) ⊓ b)` for every `d ∈ D`. Then `e` extends to a
measure-algebra equivalence `A.adjoin b ≃ D.adjoin c` that sends `b` to `c`. -/
private theorem exists_adjoinEquiv_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        let hAb := hA.adjoin b
        let hDc := hD.adjoin c
        letI := hAb.toSigmaCompleteBooleanAlgebra
        letI := hDc.toSigmaCompleteBooleanAlgebra
        ∃ f : MeasureAlgebraEquiv
            (μ.restrictToSubalgebra (A.adjoin b) hAb)
            (η.restrictToSubalgebra (D.adjoin c) hDc),
          (∀ a : A,
            ((f ⟨a, A.le_adjoin b a.property⟩ : D.adjoin c) : C) = (e a : D)) ∧
          ((f ⟨b, A.mem_adjoin b⟩ : D.adjoin c) : C) = c := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc
  dsimp only
  let hAb := hA.adjoin b
  let hDc := hD.adjoin c
  let := hAb.toSigmaCompleteBooleanAlgebra
  let := hDc.toSigmaCompleteBooleanAlgebra
  have hc_compl : ∀ d : D,
      η ((d : C) ⊓ cᶜ) = μ (((e.symm d : A) : B) ⊓ bᶜ) :=
    compl_inf_measure_eq_of_inf_measure_eq μ η A D hA hD e b c hc
  have hcut (a₁ a₂ : A) :
      b ⊓ (a₁ : B) ≤ b ⊓ (a₂ : B) ↔
        c ⊓ ((e a₁ : D) : C) ≤ c ⊓ ((e a₂ : D) : C) :=
    inf_le_inf_iff_of_inf_measure_eq μ η A D hA hD e b c hc a₁ a₂
  have hcut_compl (a₁ a₂ : A) :
      bᶜ ⊓ (a₁ : B) ≤ bᶜ ⊓ (a₂ : B) ↔
        cᶜ ⊓ ((e a₁ : D) : C) ≤ cᶜ ⊓ ((e a₂ : D) : C) :=
    inf_le_inf_iff_of_inf_measure_eq μ η A D hA hD e bᶜ cᶜ hc_compl a₁ a₂
  have horder (p q : A × A) :
      adjoinValue A b p ≤ adjoinValue A b q ↔
        adjoinValue D c (Prod.map e.toRelIso e.toRelIso p) ≤
          adjoinValue D c (Prod.map e.toRelIso e.toRelIso q) := by
    rw [adjoinValue_le_iff, adjoinValue_le_iff]
    exact and_congr (hcut p.1 q.1) (hcut_compl p.2 q.2)
  have hmeasure (p : A × A) :
      η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) =
        μ (adjoinValue A b p) :=
    measure_adjoinValue_eq_of_inf_measure_eq μ η A D hA hD e b c hc p
  let g : A.adjoin b ≃o D.adjoin c :=
    adjoinOrderIso e.toRelIso b c horder
  have hg_measure (x : A.adjoin b) : η ((g x : D.adjoin c) : C) = μ (x : B) := by
    let p := adjoinRepresentation A b x
    calc
      η ((g x : D.adjoin c) : C) =
          η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) := by
        apply congrArg η
        exact adjoinOrderIso_apply_eq_of_eq e.toRelIso b c horder x p
          (adjoinRepresentation_spec A b x)
      _ = μ (adjoinValue A b p) := hmeasure p
      _ = μ (x : B) := congrArg μ (adjoinRepresentation_spec A b x)
  let f : MeasureAlgebraEquiv
      (μ.restrictToSubalgebra (A.adjoin b) hAb)
      (η.restrictToSubalgebra (D.adjoin c) hDc) :=
    { g with
      map_measure' := fun x ↦ by simpa using hg_measure x }
  refine ⟨f, ?_, ?_⟩
  · intro a
    let x : A.adjoin b := ⟨a, A.le_adjoin b a.property⟩
    have hx : adjoinValue A b (a, a) = (x : B) := by
      change (b ⊓ (a : B)) ⊔ (bᶜ ⊓ (a : B)) = (a : B)
      rw [← inf_sup_right]
      simp
    change ((g x : D.adjoin c) : C) = (e a : D)
    rw [adjoinOrderIso_apply_eq_of_eq e.toRelIso b c horder x (a, a) hx]
    change (c ⊓ ((e a : D) : C)) ⊔ (cᶜ ⊓ ((e a : D) : C)) = (e a : D)
    rw [← inf_sup_right]
    simp
  · let x : A.adjoin b := ⟨b, A.mem_adjoin b⟩
    have hx : adjoinValue A b (⊤, ⊥) = (x : B) := by
      change adjoinValue A b (⊤, ⊥) = b
      simp [adjoinValue]
    change ((g x : D.adjoin c) : C) = c
    rw [adjoinOrderIso_apply_eq_of_eq e.toRelIso b c horder x (⊤, ⊥) hx]
    simp [adjoinValue]

/-- Let `A ⊆ B` and `D ⊆ C` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Suppose that `C`
is relatively atomless with respect to `D`. Then, for every `b ∈ B` there are
`c ∈ C` and a measure-algebra equivalence `f : A.adjoin b ≃ D.adjoin c` such that
`f(a) = e(a)` for every `a ∈ A` and `f(b) = c`. -/
theorem exists_extension_of_isRelativelyAtomless
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete)
    (hrel : D.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B),
      ∃ c : C,
        let hAb := hA.adjoin b
        let hDc := hD.adjoin c
        letI := hAb.toSigmaCompleteBooleanAlgebra
        letI := hDc.toSigmaCompleteBooleanAlgebra
        ∃ f : MeasureAlgebraEquiv
            (μ.restrictToSubalgebra (A.adjoin b) hAb)
            (η.restrictToSubalgebra (D.adjoin c) hDc),
          (∀ a : A,
            ((f ⟨a, A.le_adjoin b a.property⟩ : D.adjoin c) : C) = (e a : D)) ∧
          ((f ⟨b, A.mem_adjoin b⟩ : D.adjoin c) : C) = c := by
  let := hA.toSigmaCompleteBooleanAlgebra
  let := hD.toSigmaCompleteBooleanAlgebra
  intro e b
  obtain ⟨c, hc⟩ := exists_targetElement_of_isRelativelyAtomless μ η A D hA hD hrel e b
  exact ⟨c, exists_adjoinEquiv_of_inf_measure_eq μ η A D hA hD e b c hc⟩

end

namespace PartialEquiv

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {η : MeasureAlgebra C}

/-- Under the hypotheses of the two-sided extension theorem, if the two sides of the
partial measure-algebra equivalence `e` have density character at most `κB` and `κC`,
where `ℵ₀ ≤ κB, κC`, then the enlarged sides satisfy the same bounds. -/
theorem exists_extension_both_of_isHomogeneous_of_densityCharacter_le
    (e : PartialEquiv μ η)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (he_source : μ.subalgebraDensityCharacter e.source < μ.maharamType)
    (he_target : η.subalgebraDensityCharacter e.target < η.maharamType)
    {κB : Cardinal.{u}} {κC : Cardinal.{v}}
    (hκB : Cardinal.aleph0 ≤ κB) (hκC : Cardinal.aleph0 ≤ κC)
    (he_source_le : μ.subalgebraDensityCharacter e.source ≤ κB)
    (he_target_le : η.subalgebraDensityCharacter e.target ≤ κC)
    (b : B) (c : C) :
    ∃ f : PartialEquiv μ η,
      e.Extends f ∧ b ∈ f.source ∧ c ∈ f.target ∧
        μ.subalgebraDensityCharacter f.source < μ.maharamType ∧
        η.subalgebraDensityCharacter f.target < η.maharamType ∧
        μ.subalgebraDensityCharacter f.source ≤ κB ∧
        η.subalgebraDensityCharacter f.target ≤ κC := by
  let := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let e₀ := e.toMeasureAlgebraEquiv
  have hrelC : e.target.IsRelativelyAtomless :=
    isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt
      η e.target e.target_isSigmaComplete hη he_target
  obtain ⟨c₁, f₁, hf₁, hb⟩ :=
    exists_extension_of_isRelativelyAtomless μ η e.source e.target
      e.source_isSigmaComplete e.target_isSigmaComplete hrelC e₀ b
  let A₁ := e.source.adjoin b
  let D₁ := e.target.adjoin c₁
  let hA₁ := e.source_isSigmaComplete.adjoin b
  let hD₁ := e.target_isSigmaComplete.adjoin c₁
  let := hA₁.toSigmaCompleteBooleanAlgebra
  let := hD₁.toSigmaCompleteBooleanAlgebra
  have hA₁_small :
      μ.subalgebraDensityCharacter A₁ < μ.maharamType :=
    subalgebraDensityCharacter_adjoin_lt μ e.source b hμ_inf he_source
  have hD₁_small :
      η.subalgebraDensityCharacter D₁ < η.maharamType :=
    subalgebraDensityCharacter_adjoin_lt η e.target c₁ hη_inf he_target
  have hA₁_le :
      μ.subalgebraDensityCharacter A₁ ≤ κB :=
    subalgebraDensityCharacter_adjoin_le μ e.source b hκB he_source_le
  have hD₁_le :
      η.subalgebraDensityCharacter D₁ ≤ κC :=
    subalgebraDensityCharacter_adjoin_le η e.target c₁ hκC he_target_le
  have hrelB : A₁.IsRelativelyAtomless :=
    isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt μ A₁ hA₁ hμ hA₁_small
  obtain ⟨b₁, g, hg, hc⟩ :=
    exists_extension_of_isRelativelyAtomless η μ D₁ A₁ hD₁ hA₁ hrelB f₁.symm c
  let A₂ := A₁.adjoin b₁
  let D₂ := D₁.adjoin c
  let hA₂ := hA₁.adjoin b₁
  let hD₂ := hD₁.adjoin c
  let := hA₂.toSigmaCompleteBooleanAlgebra
  let := hD₂.toSigmaCompleteBooleanAlgebra
  let f : PartialEquiv μ η :=
    { source := A₂
      target := D₂
      source_isSigmaComplete := hA₂
      target_isSigmaComplete := hD₂
      toMeasureAlgebraEquiv := g.symm }
  have hA₂_small :
      μ.subalgebraDensityCharacter A₂ < μ.maharamType :=
    subalgebraDensityCharacter_adjoin_lt μ A₁ b₁ hμ_inf hA₁_small
  have hD₂_small :
      η.subalgebraDensityCharacter D₂ < η.maharamType :=
    subalgebraDensityCharacter_adjoin_lt η D₁ c hη_inf hD₁_small
  have hA₂_le :
      μ.subalgebraDensityCharacter A₂ ≤ κB :=
    subalgebraDensityCharacter_adjoin_le μ A₁ b₁ hκB hA₁_le
  have hD₂_le :
      η.subalgebraDensityCharacter D₂ ≤ κC :=
    subalgebraDensityCharacter_adjoin_le η D₁ c hκC hD₁_le
  have hsource : e.source ≤ A₂ :=
    (e.source.le_adjoin b).trans (A₁.le_adjoin b₁)
  have htarget : e.target ≤ D₂ :=
    (e.target.le_adjoin c₁).trans (D₁.le_adjoin c)
  have hext : e.Extends f := by
    refine ⟨hsource, htarget, ?_⟩
    intro a
    let a₁ : A₁ := ⟨a, e.source.le_adjoin b a.property⟩
    let a₂ : A₂ := ⟨a, hsource a.property⟩
    let d₁ : D₁ := f₁ a₁
    let d₂ : D₂ := ⟨d₁, D₁.le_adjoin c d₁.property⟩
    have hga : g d₂ = a₂ := by
      apply Subtype.ext
      calc
        ((g d₂ : A₂) : B) = (f₁.symm d₁ : A₁) := hg d₁
        _ = (a₁ : B) := congrArg Subtype.val (f₁.symm_apply_apply a₁)
        _ = (a₂ : B) := rfl
    have hsymm : g.symm a₂ = d₂ := by
      calc
        g.symm a₂ = g.symm (g d₂) := congrArg g.symm hga.symm
        _ = d₂ := g.left_inv d₂
    change ((g.symm a₂ : D₂) : C) = (e₀ a : e.target)
    rw [hsymm]
    exact hf₁ a
  refine ⟨f, hext, ?_, ?_, hA₂_small, hD₂_small, hA₂_le, hD₂_le⟩
  · exact A₁.le_adjoin b₁ (e.source.mem_adjoin b)
  · exact D₁.mem_adjoin c

/-- If `μ` and `η` are homogeneous and both sides of the partial measure-algebra
equivalence `e` have density character below their infinite Maharam types, then its
partial order-isomorphism extends to include any `b ∈ B` in its source and any `c ∈ C`
in its target, while preserving both density bounds. -/
theorem exists_extension_both_of_isHomogeneous
    (e : PartialEquiv μ η)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (he_source : μ.subalgebraDensityCharacter e.source < μ.maharamType)
    (he_target : η.subalgebraDensityCharacter e.target < η.maharamType)
    (b : B) (c : C) :
    ∃ f : PartialEquiv μ η,
      e.Extends f ∧ b ∈ f.source ∧ c ∈ f.target ∧
        μ.subalgebraDensityCharacter f.source < μ.maharamType ∧
        η.subalgebraDensityCharacter f.target < η.maharamType := by
  let κB := max Cardinal.aleph0 (μ.subalgebraDensityCharacter e.source)
  let κC := max Cardinal.aleph0 (η.subalgebraDensityCharacter e.target)
  obtain ⟨f, hext, hb, hc, hfB, hfC, _, _⟩ :=
    exists_extension_both_of_isHomogeneous_of_densityCharacter_le
      e hμ hη hμ_inf hη_inf he_source he_target
      (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _) b c
  exact ⟨f, hext, hb, hc, hfB, hfC⟩

end PartialEquiv

end MeasureAlgebra
