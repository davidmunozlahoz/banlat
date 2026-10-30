/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.LebesgueCube
import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.Extension
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Maharam and Carathéodory classification theorems

For homogeneous measure algebras with equal infinite Maharam type and total mass, we
enumerate dense subsets and build partial measure-algebra equivalences in a transfinite
back-and-forth way.

The main result derived with this reasoning is:
* **Maharam's homogeneous classification theorem** identifies every atomless homogeneous
  probability measure algebra with the Lebesgue cube `([0, 1]^κ, λ^κ)` indexed by its Maharam
  type.
As a direct consequence, we also obtain:
* **Carathéodory's theorem** identifies every atomless separable probability measure
  algebra with the Lebesgue measure algebra of the unit interval `([0, 1], λ)`.
-/

universe u

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- Let `e : A ≃ D` be a partial measure-algebra equivalence between `(B, μ)` and
`(C, η)`. Then `IsDensityControlled μ η κ e` means that
`densityCharacter(A) < μ.maharamType` and `densityCharacter(A) ≤ κ`, while
`densityCharacter(D) < η.maharamType` and `densityCharacter(D) ≤ κ`. -/
private def IsDensityControlled
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C) (κ : Cardinal.{u})
    (e : PartialEquiv μ η) : Prop :=
  (μ.subalgebraDensityCharacter e.source < μ.maharamType ∧
    μ.subalgebraDensityCharacter e.source ≤ κ) ∧
  (η.subalgebraDensityCharacter e.target < η.maharamType ∧
    η.subalgebraDensityCharacter e.target ≤ κ)

/-- Let `e : A ≃ D` be a partial measure-algebra equivalence between the homogeneous
measure algebras `(B, μ)` and `(C, η)`, and fix `b ∈ B` and `c ∈ C`. If
`IsDensityControlled μ η κ e`, then `successorExtension` chooses a two-sided extension
of `e` containing `b` in its source and `c` in its target. Otherwise, it is defined
to be `e`. -/
private noncomputable def successorExtension
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (e : PartialEquiv μ η) (b : B) (c : C) : PartialEquiv μ η := by
  classical
  exact if h : IsDensityControlled μ η κ e then
      Classical.choose <|
        PartialEquiv.exists_extension_both_of_isHomogeneous_of_densityCharacter_le
          e hμ hη hμ_inf hη_inf h.1.1 h.2.1 hκ hκ h.1.2 h.2.2 b c
    else e

/-- Let `e : A ≃ D` be a partial measure-algebra equivalence between the homogeneous
measure algebras `(B, μ)` and `(C, η)`, and suppose that
`IsDensityControlled μ η κ e`.

For fixed `b ∈ B` and `c ∈ C`, if `f` is the
successor extension of `e`, then `e.Extends f`, `b ∈ f.source`, `c ∈ f.target`, and
`IsDensityControlled μ η κ f`. -/
private theorem successorExtension_spec
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (e : PartialEquiv μ η) (b : B) (c : C) (he : IsDensityControlled μ η κ e) :
    let f := successorExtension μ η hμ hη hμ_inf hη_inf κ hκ e b c
    e.Extends f ∧ b ∈ f.source ∧ c ∈ f.target ∧ IsDensityControlled μ η κ f := by
  dsimp only
  rw [successorExtension, dite_eq_left he]
  have hf := Classical.choose_spec
    (PartialEquiv.exists_extension_both_of_isHomogeneous_of_densityCharacter_le
      e hμ hη hμ_inf hη_inf he.1.1 he.2.1 hκ hκ he.1.2 he.2.2 b c)
  exact ⟨hf.1, hf.2.1, hf.2.2.1,
    ⟨⟨hf.2.2.2.1, hf.2.2.2.2.2.1⟩,
      ⟨hf.2.2.2.2.1, hf.2.2.2.2.2.2⟩⟩⟩

/-- For infinite `κ` and `|ι| ≤ κ`, choose a common extension of the increasing family `E`
when all its sources and targets have density character at most `κ`; the extension retains
both bounds. Otherwise return `e₀`. -/
private noncomputable def limitExtension
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (e₀ : PartialEquiv μ η) {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hι : Cardinal.mk ι ≤ κ) (E : ι → PartialEquiv μ η) : PartialEquiv μ η := by
  classical
  exact if h : (∀ i j, i ≤ j → (E i).Extends (E j)) ∧
      (∀ i, μ.subalgebraDensityCharacter (E i).source ≤ κ) ∧
      (∀ i, η.subalgebraDensityCharacter (E i).target ≤ κ) then
      Classical.choose <| PartialEquiv.exists_extension_iUnion_of_densityCharacter_le
        E h.1 hκ hι h.2.1 h.2.2
    else e₀

/-- For an increasing family `E` satisfying the density bounds, `limitExtension` extends
every `E i` and has source and target density characters at most `κ`. -/
private theorem limitExtension_spec
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (e₀ : PartialEquiv μ η) {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hι : Cardinal.mk ι ≤ κ) (E : ι → PartialEquiv μ η)
    (hchain : ∀ i j, i ≤ j → (E i).Extends (E j))
    (hsource : ∀ i, μ.subalgebraDensityCharacter (E i).source ≤ κ)
    (htarget : ∀ i, η.subalgebraDensityCharacter (E i).target ≤ κ) :
    let f := limitExtension μ η e₀ κ hκ hι E
    (∀ i, (E i).Extends f) ∧
      μ.subalgebraDensityCharacter f.source ≤ κ ∧
      η.subalgebraDensityCharacter f.target ≤ κ := by
  dsimp only
  rw [limitExtension, dite_eq_left ⟨hchain, hsource, htarget⟩]
  exact Classical.choose_spec
    (PartialEquiv.exists_extension_iUnion_of_densityCharacter_le
      E hchain hκ hι hsource htarget)

/-- The density bound used at stage `ξ` of the transfinite construction:
the least infinite cardinal at least as large as `ξ.card`. -/
private noncomputable def stageBound (ξ : Ordinal.{u}) : Cardinal.{u} :=
  max Cardinal.aleph0 ξ.card

/-- The density bounds `stageBound ξ` increase with the ordinal stage `ξ`. -/
private theorem stageBound_mono {ξ ζ : Ordinal.{u}} (hξζ : ξ ≤ ζ) :
    stageBound ξ ≤ stageBound ζ := by
  unfold stageBound
  exact max_le (le_max_left _ _)
    ((Ordinal.card_le_card hξζ).trans (le_max_right _ _))

/-- Before the initial ordinal of an uncountable cardinal `κ`, the stage density bound
remains strictly below `κ`. -/
private theorem stageBound_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    {ξ : Ordinal.{u}} (hξ : ξ < κ.ord) : stageBound ξ < κ := by
  exact max_lt hκ (Cardinal.lt_ord.mp hξ)

/-- Let `(B, μ)` and `(C, η)` be homogeneous measure algebras, let `e₀` be a partial
measure-algebra equivalence between them, and let `b : κ → B` and `c : κ → C`. Then
`transfiniteExtension` is the ordinal-indexed family
`(E ξ)` defined by:
* `E 0 = e₀`,
* by letting `E (ξ + 1)` be a two-sided extension of `E ξ` containing `b ξ` in its source
and `c ξ` in its target when `ξ < κ.ord`;
* for every nonzero limit ordinal `ξ`, by letting `E ξ` be the partial equivalence
obtained from the family `(E ζ)_{ζ < ξ}` using `limitExtension`. -/
private noncomputable def transfiniteExtension
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (κ : Cardinal.{u}) (e₀ : PartialEquiv μ η)
    (b : κ.ord.ToType → B) (c : κ.ord.ToType → C) :
    Ordinal.{u} → PartialEquiv μ η := fun ξ ↦
  Ordinal.limitRecOn ξ e₀
    (fun ξ e ↦ if hξ : ξ < κ.ord then
      successorExtension μ η hμ hη hμ_inf hη_inf
        (stageBound (ξ + 1)) (le_max_left _ _) e
        (b (Ordinal.ToType.mk ⟨ξ, hξ⟩)) (c (Ordinal.ToType.mk ⟨ξ, hξ⟩))
      else e)
    (fun ξ hξ E ↦
      letI : Nonempty ξ.ToType :=
        Ordinal.nonempty_toType_iff.mpr hξ.bot_lt.ne'
      limitExtension μ η e₀ (stageBound ξ) (le_max_left _ _)
        (by rw [Cardinal.mk_toType]; exact le_max_right _ _)
        (fun i : ξ.ToType ↦ E i.toOrd i.toOrd.property))

/-- If `μ` and `η` have equal total measure and common infinite Maharam type `κ`, the
initial equivalence `PartialEquiv.ofMeasureTopEq htop` satisfies `IsDensityControlled`
at `stageBound 0`: its source and target are the finite subalgebras `{⊥, ⊤}`. -/
private theorem initial_isDensityControlled
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C) {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ)
    (hμκ : μ.maharamType = κ) (hηκ : η.maharamType = κ)
    (htop : μ ⊤ = η ⊤) :
    IsDensityControlled μ η (stageBound 0) (PartialEquiv.ofMeasureTopEq htop) := by
  classical
  let e₀ := PartialEquiv.ofMeasureTopEq htop
  have hsource_finite : (e₀.source : Set B).Finite := by
    simp only [e₀, PartialEquiv.ofMeasureTopEq_source]
    change ({⊥, ⊤} : Set B).Finite
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      ({⊥, ⊤} : Finset B).finite_toSet
  have htarget_finite : (e₀.target : Set C).Finite := by
    simp only [e₀, PartialEquiv.ofMeasureTopEq_target]
    change ({⊥, ⊤} : Set C).Finite
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      ({⊥, ⊤} : Finset C).finite_toSet
  unfold IsDensityControlled subalgebraDensityCharacter
  let := μ.toMetricSpace
  let := η.toMetricSpace
  let : Finite e₀.source := hsource_finite.to_subtype
  let : Finite e₀.target := htarget_finite.to_subtype
  have hsource : TopologicalSpace.densityCharacter e₀.source < Cardinal.aleph0 :=
    TopologicalSpace.densityCharacter_lt_aleph0 e₀.source
  have htarget : TopologicalSpace.densityCharacter e₀.target < Cardinal.aleph0 :=
    TopologicalSpace.densityCharacter_lt_aleph0 e₀.target
  constructor
  · exact ⟨hsource.trans_le (hμκ ▸ hκ), hsource.le.trans (le_max_left _ _)⟩
  · exact ⟨htarget.trans_le (hηκ ▸ hκ), htarget.le.trans (le_max_left _ _)⟩

/-- At stage `ξ ≤ κ.ord`, all earlier stages extend into stage `ξ`; before the terminal
stage, its source and target remain density-controlled; and they contain the elements
enumerated before `ξ`. -/
private def IsTransfiniteExtensionStage
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hμκ : μ.maharamType = κ) (hηκ : η.maharamType = κ)
    (htop : μ ⊤ = η ⊤)
    (b : κ.ord.ToType → B) (c : κ.ord.ToType → C)
    (ξ : Ordinal.{u}) (hξ : ξ ≤ κ.ord) : Prop :=
    let e₀ := PartialEquiv.ofMeasureTopEq htop
    let E := transfiniteExtension μ η hμ hη (hκ.trans_eq hμκ.symm)
      (hκ.trans_eq hηκ.symm) κ e₀ b c
    (∀ x < ξ, (E x).Extends (E ξ)) ∧
      (ξ < κ.ord → IsDensityControlled μ η (stageBound ξ) (E ξ)) ∧
      ∀ x (hx : x < ξ),
        b (Ordinal.ToType.mk ⟨x, hx.trans_le hξ⟩) ∈ (E ξ).source ∧
          c (Ordinal.ToType.mk ⟨x, hx.trans_le hξ⟩) ∈ (E ξ).target

/-- The transfinite construction satisfies `IsTransfiniteExtensionStage` at stage zero:
the initial equivalence is density-controlled by `initial_isDensityControlled`, and
there are no earlier stages or enumerated elements to include. -/
private theorem isTransfiniteExtensionStage_zero
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hμκ : μ.maharamType = κ) (hηκ : η.maharamType = κ)
    (htop : μ ⊤ = η ⊤)
    (b : κ.ord.ToType → B) (c : κ.ord.ToType → C)
    (hzero : (0 : Ordinal.{u}) ≤ κ.ord) :
    IsTransfiniteExtensionStage μ η hμ hη κ hκ hμκ hηκ htop b c 0 hzero := by
  unfold IsTransfiniteExtensionStage
  let e₀ := PartialEquiv.ofMeasureTopEq htop
  let E := transfiniteExtension μ η hμ hη (hκ.trans_eq hμκ.symm)
    (hκ.trans_eq hηκ.symm) κ e₀ b c
  dsimp only
  refine ⟨fun _ hx ↦ (not_lt_zero hx).elim, ?_,
    fun _ hx ↦ (not_lt_zero hx).elim⟩
  intro _
  simpa only [E, transfiniteExtension, Ordinal.limitRecOn_zero] using
    initial_isDensityControlled μ η hκ hμκ hηκ htop

/-- If `IsTransfiniteExtensionStage` holds at `ξ`, it holds at `ξ + 1 ≤ κ.ord`:
`successorExtension` includes the elements indexed by `ξ` while preserving the earlier
extensions, inclusions, and required density bounds. -/
private theorem isTransfiniteExtensionStage_add_one
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hμκ : μ.maharamType = κ) (hηκ : η.maharamType = κ)
    (htop : μ ⊤ = η ⊤)
    (b : κ.ord.ToType → B) (c : κ.ord.ToType → C)
    (ξ : Ordinal.{u}) (hξ : ξ + 1 ≤ κ.ord)
    (hprev : IsTransfiniteExtensionStage μ η hμ hη κ hκ hμκ hηκ htop b c ξ
      ((lt_add_one ξ).trans_le hξ).le) :
    IsTransfiniteExtensionStage μ η hμ hη κ hκ hμκ hηκ htop b c (ξ + 1) hξ := by
  unfold IsTransfiniteExtensionStage at hprev ⊢
  let e₀ := PartialEquiv.ofMeasureTopEq htop
  let E := transfiniteExtension μ η hμ hη (hκ.trans_eq hμκ.symm)
    (hκ.trans_eq hηκ.symm) κ e₀ b c
  dsimp only at hprev ⊢
  change (∀ x < ξ + 1, (E x).Extends (E (ξ + 1))) ∧
    (ξ + 1 < κ.ord → IsDensityControlled μ η (stageBound (ξ + 1)) (E (ξ + 1))) ∧
    ∀ x (hx : x < ξ + 1),
      b (Ordinal.ToType.mk ⟨x, hx.trans_le hξ⟩) ∈ (E (ξ + 1)).source ∧
        c (Ordinal.ToType.mk ⟨x, hx.trans_le hξ⟩) ∈ (E (ξ + 1)).target
  have hξκ : ξ < κ.ord := (lt_add_one ξ).trans_le hξ
  have hadm : IsDensityControlled μ η (stageBound (ξ + 1)) (E ξ) := by
    refine ⟨⟨hprev.2.1 hξκ |>.1.1, ?_⟩, ⟨hprev.2.1 hξκ |>.2.1, ?_⟩⟩
    · exact (hprev.2.1 hξκ).1.2.trans (stageBound_mono le_self_add)
    · exact (hprev.2.1 hξκ).2.2.trans (stageBound_mono le_self_add)
  have hs := successorExtension_spec μ η hμ hη
    (hκ.trans_eq hμκ.symm) (hκ.trans_eq hηκ.symm)
    (stageBound (ξ + 1)) (le_max_left _ _) (E ξ)
    (b (Ordinal.ToType.mk ⟨ξ, hξκ⟩))
    (c (Ordinal.ToType.mk ⟨ξ, hξκ⟩)) hadm
  have hE : E (ξ + 1) = successorExtension μ η hμ hη
      (hκ.trans_eq hμκ.symm) (hκ.trans_eq hηκ.symm)
      (stageBound (ξ + 1)) (le_max_left _ _) (E ξ)
      (b (Ordinal.ToType.mk ⟨ξ, hξκ⟩))
      (c (Ordinal.ToType.mk ⟨ξ, hξκ⟩)) := by
    simp only [E, transfiniteExtension, Ordinal.limitRecOn_add_one, dite_eq_left hξκ]
  rw [hE]
  refine ⟨?_, fun _ ↦ hs.2.2.2, ?_⟩
  · intro x hx
    rw [← Order.succ_eq_add_one, Order.lt_succ_iff] at hx
    rcases hx.eq_or_lt with rfl | hxo
    · exact hs.1
    · exact (hprev.1 x hxo).trans hs.1
  · intro x hx
    rw [← Order.succ_eq_add_one, Order.lt_succ_iff] at hx
    rcases hx.eq_or_lt with rfl | hxo
    · simpa only using ⟨hs.2.1, hs.2.2.1⟩
    · exact ⟨hs.1.source_le (hprev.2.2 x hxo).1,
        hs.1.target_le (hprev.2.2 x hxo).2⟩

/-- At a nonzero limit stage `ξ ≤ κ.ord`, `IsTransfiniteExtensionStage` follows from
its validity at every earlier stage: `limitExtension` gives a common extension retaining
the earlier inclusions and the required density bounds. -/
private theorem isTransfiniteExtensionStage_limit
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hμκ : μ.maharamType = κ) (hηκ : η.maharamType = κ)
    (htop : μ ⊤ = η ⊤)
    (b : κ.ord.ToType → B) (c : κ.ord.ToType → C)
    (ξ : Ordinal.{u}) (hlim : Order.IsSuccLimit ξ) (hξ : ξ ≤ κ.ord)
    (ih : ∀ ζ (hζ : ζ < ξ),
      IsTransfiniteExtensionStage μ η hμ hη κ hκ hμκ hηκ htop b c ζ
        (hζ.le.trans hξ)) :
    IsTransfiniteExtensionStage μ η hμ hη κ hκ hμκ hηκ htop b c ξ hξ := by
  unfold IsTransfiniteExtensionStage at ih ⊢
  let e₀ := PartialEquiv.ofMeasureTopEq htop
  let E := transfiniteExtension μ η hμ hη (hκ.trans_eq hμκ.symm)
    (hκ.trans_eq hηκ.symm) κ e₀ b c
  dsimp only at ih ⊢
  change (∀ x < ξ, (E x).Extends (E ξ)) ∧
    (ξ < κ.ord → IsDensityControlled μ η (stageBound ξ) (E ξ)) ∧
    ∀ x (hx : x < ξ),
      b (Ordinal.ToType.mk ⟨x, hx.trans_le hξ⟩) ∈ (E ξ).source ∧
        c (Ordinal.ToType.mk ⟨x, hx.trans_le hξ⟩) ∈ (E ξ).target
  let : Nonempty ξ.ToType := Ordinal.nonempty_toType_iff.mpr hlim.bot_lt.ne'
  let P : ξ.ToType → PartialEquiv μ η := fun i ↦ E i.toOrd
  have hchain : ∀ i j, i ≤ j → (P i).Extends (P j) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact PartialEquiv.Extends.refl _
    · have hjlt : (j.toOrd : Ordinal) < ξ := j.toOrd.property
      exact (ih j.toOrd hjlt).1 i.toOrd
        (Ordinal.ToType.mk.symm.lt_iff_lt.mpr hij)
  have hsource : ∀ i,
      μ.subalgebraDensityCharacter (P i).source ≤ stageBound ξ := by
    intro i
    have hilt : (i.toOrd : Ordinal) < ξ := i.toOrd.property
    exact ((ih i.toOrd hilt).2.1 (hilt.trans_le hξ)).1.2.trans
      (stageBound_mono hilt.le)
  have htarget : ∀ i,
      η.subalgebraDensityCharacter (P i).target ≤ stageBound ξ := by
    intro i
    have hilt : (i.toOrd : Ordinal) < ξ := i.toOrd.property
    exact ((ih i.toOrd hilt).2.1 (hilt.trans_le hξ)).2.2.trans
      (stageBound_mono hilt.le)
  have hl := limitExtension_spec μ η e₀ (stageBound ξ) (le_max_left _ _)
    (by rw [Cardinal.mk_toType]; exact le_max_right _ _) P hchain hsource htarget
  have hE : E ξ = limitExtension μ η e₀ (stageBound ξ) (le_max_left _ _)
      (by rw [Cardinal.mk_toType]; exact le_max_right _ _) P := by
    simp only [P, E, transfiniteExtension, Ordinal.limitRecOn_limit _ _ _ _ hlim]
  rw [hE]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simpa only [P, OrderIso.symm_apply_apply] using
      hl.1 (Ordinal.ToType.mk ⟨x, hx⟩)
  · intro hξκ
    rcases hκ.eq_or_lt with hκ_eq | hκ_lt
    · rw [← hκ_eq, Cardinal.ord_aleph0] at hξκ
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hξκ
      exact (Order.not_isSuccLimit_natCast n hlim).elim
    · exact ⟨⟨hl.2.1.trans_lt (hμκ ▸ stageBound_lt hκ_lt hξκ), hl.2.1⟩,
        ⟨hl.2.2.trans_lt (hηκ ▸ stageBound_lt hκ_lt hξκ), hl.2.2⟩⟩
  · intro x hx
    have hy : x + 1 < ξ := hlim.add_one_lt hx
    let i := Ordinal.ToType.mk ⟨x + 1, hy⟩
    have hilt : (i.toOrd : Ordinal) < ξ := i.toOrd.property
    have hi := ih i.toOrd hilt
    have hxi : x < (i.toOrd : Ordinal) := by
      simpa only [i, OrderIso.symm_apply_apply] using lt_add_one x
    exact ⟨(hl.1 i).source_le (hi.2.2 x hxi).1,
      (hl.1 i).target_le (hi.2.2 x hxi).2⟩

/-- Every stage `ξ ≤ κ.ord` extends all earlier stages and contains the elements enumerated
before `ξ`. For `ξ < κ.ord`, both sides also satisfy `IsDensityControlled` with bound
`stageBound ξ`. -/
private theorem transfiniteExtension_spec
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hμκ : μ.maharamType = κ) (hηκ : η.maharamType = κ)
    (htop : μ ⊤ = η ⊤)
    (b : κ.ord.ToType → B) (c : κ.ord.ToType → C)
    (ξ : Ordinal.{u}) (hξ : ξ ≤ κ.ord) :
    IsTransfiniteExtensionStage μ η hμ hη κ hκ hμκ hηκ htop b c ξ hξ := by
  revert hξ
  induction ξ using Ordinal.limitRecOn with
  | zero =>
      intro hξ
      exact isTransfiniteExtensionStage_zero μ η hμ hη κ hκ hμκ hηκ
        htop b c hξ
  | add_one ξ ih =>
      intro hξ
      exact isTransfiniteExtensionStage_add_one μ η hμ hη κ hκ hμκ hηκ
        htop b c ξ hξ (ih ((lt_add_one ξ).trans_le hξ).le)
  | limit ξ hlim ih =>
      intro hξ
      apply isTransfiniteExtensionStage_limit μ η hμ hη κ hκ hμκ hηκ
        htop b c ξ hlim hξ
      intro ζ hζ
      exact ih ζ hζ (hζ.le.trans hξ)

/-- In a measure algebra of total mass one, the top and bottom elements are distinct. -/
private theorem top_ne_bot_of_measure_top_eq_one
    (μ : MeasureAlgebra B) (hμ : μ ⊤ = 1) :
    (⊤ : B) ≠ ⊥ := by
  intro h
  have hm := congrArg μ h
  rw [hμ, μ.measure_bot] at hm
  norm_num at hm

/-- Let `(B, μ)` and `(C, η)` be homogeneous measure algebras such that
`μ.maharamType = η.maharamType`, this common cardinal is at least `ℵ₀`,
and `μ(⊤) = η(⊤)`. Then `(B, μ)` and `(C, η)` are measure-algebra equivalent. -/
theorem nonempty_measureAlgebraEquiv_of_isHomogeneous_of_maharamType_eq_of_top_eq_top
    {C : Type u} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hκ : μ.maharamType = η.maharamType)
    (hκ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (htop : μ ⊤ = η ⊤) :
    Nonempty (MeasureAlgebraEquiv μ η) := by
  let κ := μ.maharamType
  have hηκ : η.maharamType = κ := hκ.symm
  have hμdensity : μ.densityCharacter = κ := rfl
  have hηdensity : η.densityCharacter = κ := hηκ
  let := μ.toMetricSpace
  let := η.toMetricSpace
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_denseRange_ord B κ hμdensity
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_denseRange_ord C κ hηdensity
  let e₀ := PartialEquiv.ofMeasureTopEq htop
  let E := transfiniteExtension μ η hμ hη hκ_inf
    (hκ_inf.trans_eq hκ) κ e₀ b c
  have hE := transfiniteExtension_spec μ η hμ hη κ hκ_inf rfl hηκ
    htop b c κ.ord le_rfl
  have hsource : Set.range b ⊆ (E κ.ord).source := by
    rintro _ ⟨i, rfl⟩
    have hi : (i.toOrd : Ordinal) < κ.ord := i.toOrd.property
    have hind : Ordinal.ToType.mk
        ⟨(i.toOrd : Ordinal), hi.trans_le le_rfl⟩ = i := by
      calc
        Ordinal.ToType.mk ⟨(i.toOrd : Ordinal), hi.trans_le le_rfl⟩ =
            Ordinal.ToType.mk i.toOrd := congrArg _ (Subtype.ext rfl)
        _ = i := OrderIso.apply_symm_apply _ i
    rw [← hind]
    change b (Ordinal.ToType.mk ⟨(i.toOrd : Ordinal), hi.trans_le le_rfl⟩) ∈
      (E κ.ord).source
    simpa only [E, e₀] using (hE.2.2 i.toOrd hi).1
  have htarget : Set.range c ⊆ (E κ.ord).target := by
    rintro _ ⟨i, rfl⟩
    have hi : (i.toOrd : Ordinal) < κ.ord := i.toOrd.property
    have hind : Ordinal.ToType.mk
        ⟨(i.toOrd : Ordinal), hi.trans_le le_rfl⟩ = i := by
      calc
        Ordinal.ToType.mk ⟨(i.toOrd : Ordinal), hi.trans_le le_rfl⟩ =
            Ordinal.ToType.mk i.toOrd := congrArg _ (Subtype.ext rfl)
        _ = i := OrderIso.apply_symm_apply _ i
    rw [← hind]
    change c (Ordinal.ToType.mk ⟨(i.toOrd : Ordinal), hi.trans_le le_rfl⟩) ∈
      (E κ.ord).target
    simpa only [E, e₀] using (hE.2.2 i.toOrd hi).2
  exact nonempty_measureAlgebraEquiv_of_dense_booleanSubalgebra_orderIso
    (E κ.ord).source (E κ.ord).target (hb.mono hsource) (hc.mono htarget)
    (E κ.ord).toOrderIso (E κ.ord).map_measure

/-- **Maharam's (homogeneous) classification theorem:** An atomless homogeneous measure algebra
of total mass one is equivalent to the Lebesgue cube indexed by its Maharam type. -/
theorem nonempty_measureAlgebraEquiv_cube_of_isAtomless_of_isHomogeneous_of_top_eq_one
    (μ : MeasureAlgebra B)
    (hB : BooleanAlgebra.IsAtomless B)
    (hμ : μ.IsHomogeneous)
    (htop : μ ⊤ = 1) :
    Nonempty
      (MeasureAlgebraEquiv μ
        (cubeMeasureAlgebra (μ.maharamType))) := by
  let κ := μ.maharamType
  let : Nontrivial B :=
    ⟨⟨⊥, ⊤, (top_ne_bot_of_measure_top_eq_one μ htop).symm⟩⟩
  have hκ : Cardinal.aleph0 ≤ κ :=
    aleph0_le_maharamType_of_isAtomless μ hB
  have hκ_pos : 0 < κ := Cardinal.aleph0_pos.trans_le hκ
  let η := cubeMeasureAlgebra κ
  have hη : η.IsHomogeneous := cubeMeasureAlgebra_isHomogeneous κ hκ_pos
  have hηκ : η.maharamType = κ := by
    rw [cubeMeasureAlgebra_maharamType κ hκ_pos, max_eq_right hκ]
  have htop_eq : μ ⊤ = η ⊤ := by
    rw [htop]
    exact (cubeMeasureAlgebra_top κ).symm
  exact nonempty_measureAlgebraEquiv_of_isHomogeneous_of_maharamType_eq_of_top_eq_top
    μ η hμ hη hηκ.symm hκ htop_eq

/-- **Carathéodory's theorem.** Every atomless separable measure algebra `(B, μ)`
with `μ(⊤) = 1` is measure-algebra equivalent to the one-dimensional Lebesgue
cube `[0, 1]^1`. -/
theorem nonempty_measureAlgebraEquiv_lebesgue_of_isAtomless_of_isSeparable_of_top_eq_one
    (μ : MeasureAlgebra B)
    (hB : BooleanAlgebra.IsAtomless B)
    (hμ :
      letI := μ.toMetricSpace
      TopologicalSpace.SeparableSpace B)
    (htop : μ ⊤ = 1) :
    Nonempty (MeasureAlgebraEquiv μ LebesgueMeasureAlgebra.{u}) := by
  have hhom : μ.IsHomogeneous :=
    isHomogeneous_of_isAtomless_of_isSeparable μ hB hμ
  let := μ.toMetricSpace
  let : TopologicalSpace.SeparableSpace B := hμ
  let : Nontrivial B :=
    ⟨⟨⊥, ⊤, (top_ne_bot_of_measure_top_eq_one μ htop).symm⟩⟩
  have hμκ : μ.maharamType = Cardinal.aleph0 :=
    μ.maharamType_eq_aleph0_of_isAtomless_of_densityCharacter_le hB
      (TopologicalSpace.densityCharacter_le_aleph0 B)
  have hηhom : LebesgueMeasureAlgebra.{u}.IsHomogeneous :=
    cubeMeasureAlgebra_isHomogeneous 1 (by simp)
  apply nonempty_measureAlgebraEquiv_of_isHomogeneous_of_maharamType_eq_of_top_eq_top
    μ LebesgueMeasureAlgebra.{u} hhom hηhom
  · rw [hμκ, cubeMeasureAlgebra_maharamType 1 (by simp)]
    simp
  · rw [hμκ]
  · simpa using htop

end MeasureAlgebra
