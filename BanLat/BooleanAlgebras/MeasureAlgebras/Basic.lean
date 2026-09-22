/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Functional.Basic

/-!
# Measure algebras

This file introduces **measure algebras** `(B, μ)`, where `B` is a `σ`-order complete
Boolean algebra and `μ : B → [0, ∞]` is a function satisfying that:
* `μ(b) = 0 ↔ b = ⊥`.
* `μ(⊤) < ∞`.
* `μ(∨ b i) = ∑ μ(b i)` for every pairwise disjoint sequence `b i` in `B`.

The file constructs restrictions to principal intervals and `σ`-complete Boolean subalgebras.
On every such subalgebra `A`, the maps `a ↦ μ (a ⊓ b)` define finite countably additive functionals.

It also introduces **measure-algebra equivalences**, and **partial measure-algebra equivalences**
between `σ`-complete Boolean subalgebras, together with the relation expressing that one partial
equivalence extends another.
-/

open Function
open scoped ENNReal symmDiff

universe u v

/-- A **measure algebra on `B`** is a finite faithful countably additive functional
on a `σ`-complete Boolean algebra. -/
structure MeasureAlgebra (B : Type u) [SigmaCompleteBooleanAlgebra B]
    extends CountablyAdditiveFunctional B where
  /-- The total measure is finite. -/
  isFinite : toCountablyAdditiveFunctional.IsFinite
  /-- The measure vanishes exactly at the bottom element. -/
  isFaithful : toCountablyAdditiveFunctional.IsFaithful

instance {B : Type u} [SigmaCompleteBooleanAlgebra B] :
    CoeFun (MeasureAlgebra B) (fun _ ↦ B → ℝ≥0∞) :=
  ⟨fun μ ↦ μ.toCountablyAdditiveFunctional⟩

/-! ## Construction from countably additive functionals -/

namespace CountablyAdditiveFunctional

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- A countably additive functional `ν` that vanishes only at the bottom
element and satisfies `ν ⊤ < ∞` defines a measure algebra. -/
def toMeasureAlgebra (ν : CountablyAdditiveFunctional B) (hν : ν.IsFinite)
    (hν_faith : ν.IsFaithful) : MeasureAlgebra B where
  toCountablyAdditiveFunctional := ν
  isFinite := hν
  isFaithful := hν_faith

@[simp high]
theorem toMeasureAlgebra_apply (ν : CountablyAdditiveFunctional B) (hν : ν.IsFinite)
    (hν_faith : ν.IsFaithful) (b : B) :
    ν.toMeasureAlgebra hν hν_faith b = ν b := by
  rfl

theorem toMeasureAlgebra_toCountablyAdditiveFunctional
    (ν : CountablyAdditiveFunctional B) (hν : ν.IsFinite)
    (hν_faith : ν.IsFaithful) :
    (ν.toMeasureAlgebra hν hν_faith).toCountablyAdditiveFunctional = ν := by
  rfl

end CountablyAdditiveFunctional

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-! ### Conversions and characterizations -/

@[simp]
theorem toCountablyAdditiveFunctional_toMeasureAlgebra :
    μ.toCountablyAdditiveFunctional.toMeasureAlgebra μ.isFinite μ.isFaithful = μ := by
  cases μ
  rfl

/-- Measure algebras are exactly countably additive functionals which are
finite and vanish only at the bottom element. -/
def equivFiniteFaithfulFunctional :
    MeasureAlgebra B ≃
      {ν : CountablyAdditiveFunctional B //
        ν.IsFinite ∧ ν.IsFaithful} where
  toFun μ := ⟨μ.toCountablyAdditiveFunctional, μ.isFinite, μ.isFaithful⟩
  invFun ν := ν.1.toMeasureAlgebra ν.2.1 ν.2.2
  left_inv μ := μ.toCountablyAdditiveFunctional_toMeasureAlgebra
  right_inv ν := Subtype.ext <| ν.1.toMeasureAlgebra_toCountablyAdditiveFunctional ν.2.1 ν.2.2

/-! ### Elementary properties of measure algebras -/

/-- The measure of a measure algebra maps the bottom element to zero. -/
@[simp high]
theorem measure_bot : μ ⊥ = 0 := by
  exact μ.toCountablyAdditiveFunctional.map_bot

/-- The measure of a measure algebra vanishes exactly at the bottom element. -/
theorem measure_eq_zero_iff (b : B) : μ b = 0 ↔ b = ⊥ := by
  exact μ.isFaithful b

/-- The total measure of a measure algebra is finite. -/
theorem m_top_ne_top : μ ⊤ ≠ ∞ := by
  exact μ.isFinite

/-- Every element of a measure algebra has finite measure. -/
@[simp]
theorem measure_ne_top (b : B) : μ b ≠ ∞ := by
  exact μ.toCountablyAdditiveFunctional.ne_top μ.isFinite b

/-- The measure of a measure algebra is monotone. -/
@[gcongr]
theorem measure_mono {b c : B} (hbc : b ≤ c) : μ b ≤ μ c := by
  exact μ.toCountablyAdditiveFunctional.monotone hbc

/-- The measure of a measure algebra is strictly monotone. -/
theorem measure_strictMono : StrictMono μ := by
  exact μ.toCountablyAdditiveFunctional.strictMono μ.isFinite μ.isFaithful

/-! ### Finite operations -/

/-- The measure of a measure algebra is additive on disjoint elements. -/
theorem measure_sup {b c : B} (h : Disjoint b c) :
    μ (b ⊔ c) = μ b + μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sup h

/-- In a measure algebra, the measure of the supremum of a finite pairwise disjoint
family is the sum of the measures. -/
theorem measure_finset_sup (s : Finset B)
    (hs : (s : Set B).PairwiseDisjoint id) :
    μ (s.sup id) = ∑ b ∈ s, μ b := by
  exact μ.toCountablyAdditiveFunctional.map_finset_sup s hs

/-- An element is the disjoint supremum of its difference and intersection
with another element. -/
theorem measure_sdiff_add_inf (b c : B) :
    μ (b \ c) + μ (b ⊓ c) = μ b := by
  exact μ.toCountablyAdditiveFunctional.map_sdiff_add_inf b c

/-- The measure of a difference is the difference of the measures when the
subtracted element lies below the first. -/
theorem measure_sdiff {b c : B} (hcb : c ≤ b) :
    μ (b \ c) = μ b - μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sdiff hcb (μ.measure_ne_top c)

/-- For all `b, c` in a measure algebra,
`μ (b ∆ c) = μ (b \ c) + μ (c \ b)`. -/
theorem measure_symmDiff (b c : B) :
    μ (b ∆ c) = μ (b \ c) + μ (c \ b) := by
  exact μ.toCountablyAdditiveFunctional.map_symmDiff b c

/-- In a measure algebra, the measure of a supremum is at most the sum of the measures. -/
theorem measure_sup_le (b c : B) : μ (b ⊔ c) ≤ μ b + μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sup_le b c

/-- The measure of a measure algebra is a valuation. -/
theorem measure_sup_add_inf (b c : B) :
    μ (b ⊔ c) + μ (b ⊓ c) = μ b + μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sup_add_inf b c

/-- In a measure algebra, the measures of an element and its complement add up to the
total measure. -/
theorem measure_add_measure_compl (b : B) :
    μ b + μ bᶜ = μ ⊤ := by
  exact μ.toCountablyAdditiveFunctional.map_add_map_compl b

/-! ### Countable operations -/

/-- The measure of a measure algebra is countably additive on pairwise disjoint sequences. -/
theorem measure_iSup {b : ℕ → B} (hb : Pairwise (Disjoint on b)) :
    μ (⨆ i, b i) = ∑' i, μ (b i) := by
  exact μ.toCountablyAdditiveFunctional.map_iSup hb

/-- In a measure algebra, the measure of a countable supremum is at most the sum of the
measures. -/
theorem measure_iSup_le (b : ℕ → B) :
    μ (⨆ i, b i) ≤ ∑' i, μ (b i) := by
  exact μ.toCountablyAdditiveFunctional.map_iSup_le b

/-- In a measure algebra, the measure of the supremum of an increasing sequence is the
supremum of its measures. -/
theorem measure_iSup_eq_iSup {b : ℕ → B} (hb : Monotone b) :
    μ (⨆ i, b i) = ⨆ i, μ (b i) := by
  exact μ.toCountablyAdditiveFunctional.map_iSup_eq_iSup hb

/-- The measures along an increasing sequence converge to the measure of its
supremum. -/
theorem tendsto_measure_iSup {b : ℕ → B} (hb : Monotone b) :
    Filter.Tendsto (fun n ↦ μ (b n)) Filter.atTop (nhds (μ (⨆ n, b n))) := by
  exact μ.toCountablyAdditiveFunctional.tendsto_map_iSup hb

/-! ### Restrictions and canonical induced functionals -/

/-- For `b ∈ B`, `μ.restrict b` is the measure algebra on the principal interval
`Set.Iic b = {c ∈ B | c ≤ b}` given by `(μ.restrict b) c = μ c`. -/
noncomputable def restrict (b : B) : MeasureAlgebra (Set.Iic b) :=
  (μ.toCountablyAdditiveFunctional.restrict b).toMeasureAlgebra
    (μ.toCountablyAdditiveFunctional.restrict_isFinite b (μ.measure_ne_top b))
    (μ.toCountablyAdditiveFunctional.restrict_isFaithful b μ.isFaithful)

/-- The restriction of a measure algebra to a `σ`-complete Boolean subalgebra. -/
noncomputable def restrictToSubalgebra (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    MeasureAlgebra A := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  exact (μ.toCountablyAdditiveFunctional.restrictToSubalgebra A hA).toMeasureAlgebra
    (μ.toCountablyAdditiveFunctional.restrictToSubalgebra_isFinite A hA μ.isFinite)
    (μ.toCountablyAdditiveFunctional.restrictToSubalgebra_isFaithful
      A hA μ.isFaithful)

/-- Restricting a measure algebra does not change the measure of an element. -/
@[simp]
theorem restrictToSubalgebra_apply (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    μ.restrictToSubalgebra A hA a = μ (a : B) := by
  exact μ.toCountablyAdditiveFunctional.restrictToSubalgebra_apply A hA a

/-- On every `σ`-complete Boolean subalgebra `A`, for any fixed `b ∈ B`, the map
`• ↦ μ(• ⊓ b)` defines a countably additive functional. -/
noncomputable def infFunctional (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    CountablyAdditiveFunctional A := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  exact μ.toCountablyAdditiveFunctional.infFunctional A hA b

/-- The functional `• ↦ μ(• ⊓ b)` evaluates `a` as `μ (a ⊓ b)`. -/
@[simp]
theorem infFunctional_apply (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    μ.infFunctional A hA b a = μ ((a : B) ⊓ b) := by
  exact μ.toCountablyAdditiveFunctional.infFunctional_apply A hA b a

/-- The functional obtained by intersecting with a disjoint supremum is the
sum of the functionals obtained from its two terms. -/
theorem infFunctional_sup_apply (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete)
    {b c : B} (hbc : Disjoint b c) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    μ.infFunctional A hA (b ⊔ c) a =
      μ.infFunctional A hA b a + μ.infFunctional A hA c a := by
  exact μ.toCountablyAdditiveFunctional.infFunctional_sup_apply A hA hbc a

/-- The functional `• ↦ μ(• ⊓ b)` is dominated by the restriction of the
ambient measure. -/
theorem infFunctional_le (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    μ.infFunctional A hA b a ≤ μ (a : B) := by
  exact μ.toCountablyAdditiveFunctional.infFunctional_le A hA b a

/-- Intersecting with an element of a measure algebra produces a finite
functional on every `σ`-complete Boolean subalgebra. -/
theorem infFunctional_isFinite (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (μ.infFunctional A hA b).IsFinite := by
  exact μ.toCountablyAdditiveFunctional.infFunctional_isFinite
    A hA b (μ.measure_ne_top b)

end MeasureAlgebra

/-! ## Measure algebra equivalences -/

/-- A **measure algebra equivalence** is an order isomorphism that preserves the measure. -/
structure MeasureAlgebraEquiv
    {B : Type u} {C : Type v}
    [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (ν : MeasureAlgebra C)
    extends B ≃o C where
  /-- The order isomorphism preserves the measure. -/
  map_measure' (b : B) : ν (toFun b) = μ b

namespace MeasureAlgebraEquiv

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

instance : CoeFun (MeasureAlgebraEquiv μ ν) (fun _ ↦ B → C) := by
  exact ⟨fun e ↦ e.toFun⟩

/-- A measure-algebra equivalence preserves the measure. -/
@[simp]
theorem map_measure (e : MeasureAlgebraEquiv μ ν) (b : B) :
    ν (e.toRelIso b) = μ b := by
  exact e.map_measure' b

/-- The inverse of a measure-algebra equivalence. -/
def symm (e : MeasureAlgebraEquiv μ ν) : MeasureAlgebraEquiv ν μ where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_rel_iff' := e.toRelIso.symm.map_rel_iff
  map_measure' b := by
    simpa using (e.map_measure (e.invFun b)).symm

/-- For `b ∈ B`, a measure-algebra equivalence `e : (B, μ) ≃ (C, ν)` restricts
to a measure-algebra equivalence between the principal intervals below `b`
and `e b`. -/
noncomputable def restrict (e : MeasureAlgebraEquiv μ ν) (b : B) :
    MeasureAlgebraEquiv (μ.restrict b) (ν.restrict (e.toRelIso b)) := by
  refine
    { toFun := fun c ↦ ⟨e c, e.toRelIso.map_rel_iff.mpr c.property⟩
      invFun := fun d ↦
        ⟨e.toRelIso.symm d, by simpa using e.toRelIso.symm.map_rel_iff.mpr d.property⟩
      left_inv := fun c ↦ Subtype.ext (e.toRelIso.left_inv c)
      right_inv := fun d ↦ Subtype.ext (e.toRelIso.right_inv d)
      map_rel_iff' := e.toRelIso.map_rel_iff
      map_measure' := fun c ↦ e.map_measure c }

/-- The restriction of `e` to the principal interval below `b` sends
`c ∈ Set.Iic b` to `e c ∈ Set.Iic (e b)`. -/
@[simp]
theorem restrict_apply (e : MeasureAlgebraEquiv μ ν) (b : B)
    (c : Set.Iic b) :
    (((e.restrict b).toRelIso c : Set.Iic (e.toRelIso b)) : C) = e (c : B) := by
  rfl

end MeasureAlgebraEquiv

/-! ## Partial measure algebra equivalences -/

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

section

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable (μ : MeasureAlgebra B) (η : MeasureAlgebra C)

/-- A **partial equivalence of `μ` and `η`** consists of a measure-algebra equivalence
between restrictions to `σ`-complete Boolean subalgebras. -/
structure PartialEquiv where
  /-- The source `σ`-complete Boolean subalgebra. -/
  source : BooleanSubalgebra B
  /-- The target `σ`-complete Boolean subalgebra. -/
  target : BooleanSubalgebra C
  /-- The source is closed under countable suprema computed in `B`. -/
  source_isSigmaComplete : source.IsSigmaComplete
  /-- The target is closed under countable suprema computed in `C`. -/
  target_isSigmaComplete : target.IsSigmaComplete
  /-- The measure-algebra equivalence between the two restrictions. -/
  toMeasureAlgebraEquiv :
    letI := source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
    letI := target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
    MeasureAlgebraEquiv
      (μ.restrictToSubalgebra source source_isSigmaComplete)
      (η.restrictToSubalgebra target target_isSigmaComplete)

end

namespace PartialEquiv

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {η : MeasureAlgebra C}

/-- The partial order-isomorphism underlying a partial measure-algebra equivalence. -/
noncomputable def toOrderIso (e : PartialEquiv μ η) : e.source ≃o e.target := by
  letI := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  letI := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  exact e.toMeasureAlgebraEquiv.toRelIso

/-- The partial order-isomorphism underlying a partial measure-algebra equivalence
preserves the measure. -/
@[simp]
theorem map_measure (e : PartialEquiv μ η) (a : e.source) :
    η (e.toOrderIso a : C) = μ (a : B) := by
  letI := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  letI := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  exact e.toMeasureAlgebraEquiv.map_measure a

/-- Let `B`and `C` be Boolean algebra. Suppose that `B` is trivial iff so is `C`.
Then the Boolean subalgebras `{⊥, ⊤} ⊆ B` and `{⊥, ⊤} ⊆ C` are order-isomorphic. -/
private noncomputable def orderIsoBot
    (htriv : (⊥ : B) = ⊤ ↔ (⊥ : C) = ⊤) :
    (⊥ : BooleanSubalgebra B) ≃o (⊥ : BooleanSubalgebra C) := by
  classical
  by_cases hB : (⊥ : B) = ⊤
  · have hC := htriv.mp hB
    letI : Subsingleton B := subsingleton_of_bot_eq_top hB
    letI : Subsingleton C := subsingleton_of_bot_eq_top hC
    letI : Unique (⊥ : BooleanSubalgebra B) :=
      { default := ⊥
        uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _) }
    letI : Unique (⊥ : BooleanSubalgebra C) :=
      { default := ⊥
        uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _) }
    exact OrderIso.ofUnique _ _
  · have hC : (⊥ : C) ≠ ⊤ := mt htriv.mpr hB
    letI : IsSimpleOrder (⊥ : BooleanSubalgebra B) :=
      { exists_pair_ne := ⟨⊥, ⊤, fun h ↦ hB (congrArg Subtype.val h)⟩
        eq_bot_or_eq_top := fun a ↦ by
          rcases a.property with ha | ha
          · exact Or.inl (Subtype.ext ha)
          · exact Or.inr (Subtype.ext ha) }
    letI : IsSimpleOrder (⊥ : BooleanSubalgebra C) :=
      { exists_pair_ne := ⟨⊥, ⊤, fun h ↦ hC (congrArg Subtype.val h)⟩
        eq_bot_or_eq_top := fun c ↦ by
          rcases c.property with hc | hc
          · exact Or.inl (Subtype.ext hc)
          · exact Or.inr (Subtype.ext hc) }
    exact (IsSimpleOrder.orderIsoBool : (⊥ : BooleanSubalgebra B) ≃o Bool).trans
      (IsSimpleOrder.orderIsoBool : (⊥ : BooleanSubalgebra C) ≃o Bool).symm

/-- If `μ ⊤ = η ⊤`, the trivial subalgebras `{⊥, ⊤} ⊆ B` and
`{⊥, ⊤} ⊆ C` always form a partial equivalence. -/
noncomputable def ofMeasureTopEq (h : μ ⊤ = η ⊤) : PartialEquiv μ η := by
  have htriv : (⊥ : B) = ⊤ ↔ (⊥ : C) = ⊤ := by
    constructor
    · intro hB
      symm
      apply (η.measure_eq_zero_iff ⊤).mp
      rw [← h, ← hB, μ.measure_bot]
    · intro hC
      symm
      apply (μ.measure_eq_zero_iff ⊤).mp
      rw [h, ← hC, η.measure_bot]
  let e := orderIsoBot htriv
  let hB : (⊥ : BooleanSubalgebra B).IsSigmaComplete :=
    BooleanSubalgebra.isSigmaComplete_bot
  let hC : (⊥ : BooleanSubalgebra C).IsSigmaComplete :=
    BooleanSubalgebra.isSigmaComplete_bot
  letI := hB.toSigmaCompleteBooleanAlgebra
  letI := hC.toSigmaCompleteBooleanAlgebra
  exact
    { source := ⊥
      target := ⊥
      source_isSigmaComplete := hB
      target_isSigmaComplete := hC
      toMeasureAlgebraEquiv :=
        { e with
          map_measure' := by
            intro a
            rcases BooleanSubalgebra.mem_bot.mp a.property with ha | ha
            · have ha' : a = ⊥ := Subtype.ext ha
              simp [ha']
            · have ha' : a = ⊤ := Subtype.ext ha
              simpa [ha'] using h.symm } }

@[simp]
theorem ofMeasureTopEq_source (h : μ ⊤ = η ⊤) :
    (ofMeasureTopEq h).source = (⊥ : BooleanSubalgebra B) := rfl

@[simp]
theorem ofMeasureTopEq_target (h : μ ⊤ = η ⊤) :
    (ofMeasureTopEq h).target = (⊥ : BooleanSubalgebra C) := rfl

/-- One partial measure-algebra equivalence extends another when its source and target
grow and its partial order-isomorphism agrees with the old partial order-isomorphism
on the old source. -/
structure Extends (e f : PartialEquiv μ η) : Prop where
  /-- Inclusion of the old source in the new source. -/
  source_le : e.source ≤ f.source
  /-- Inclusion of the old target in the new target. -/
  target_le : e.target ≤ f.target
  /-- The new partial order-isomorphism agrees with the old partial order-isomorphism
  on the old source. -/
  map_eq (a : e.source) :
    ((f.toOrderIso ⟨a, source_le a.property⟩ : f.target) : C) =
      (e.toOrderIso a : e.target)

/-- Every partial measure-algebra equivalence extends itself. -/
protected theorem Extends.refl (e : PartialEquiv μ η) : e.Extends e := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  intro a
  rfl

/-- Extension of partial measure-algebra equivalences is transitive. -/
protected theorem Extends.trans {e f g : PartialEquiv μ η}
    (hef : e.Extends f) (hfg : f.Extends g) : e.Extends g := by
  refine ⟨hef.source_le.trans hfg.source_le, hef.target_le.trans hfg.target_le, ?_⟩
  intro a
  exact (hfg.map_eq ⟨a, hef.source_le a.property⟩).trans (hef.map_eq a)

/-- The inverse partial order-isomorphisms of two extending partial measure-algebra
equivalences agree on the old target. -/
theorem Extends.symm_map_eq {e f : PartialEquiv μ η} (hef : e.Extends f)
    (d : e.target) :
    ((f.toOrderIso.symm ⟨d, hef.target_le d.property⟩ : f.source) : B) =
      (e.toOrderIso.symm d : e.source) := by
  let a := e.toOrderIso.symm d
  have hmap := hef.map_eq a
  have hmap' : f.toOrderIso ⟨a, hef.source_le a.property⟩ =
      ⟨d, hef.target_le d.property⟩ := by
    apply Subtype.ext
    simpa only [a, e.toOrderIso.apply_symm_apply] using hmap
  have heq : f.toOrderIso.symm ⟨d, hef.target_le d.property⟩ =
      ⟨a, hef.source_le a.property⟩ := by
    calc
      f.toOrderIso.symm ⟨d, hef.target_le d.property⟩ =
        f.toOrderIso.symm (f.toOrderIso ⟨a, hef.source_le a.property⟩) :=
        congrArg f.toOrderIso.symm hmap'.symm
      _ = ⟨a, hef.source_le a.property⟩ := f.toOrderIso.symm_apply_apply _
  exact congrArg Subtype.val heq

end PartialEquiv

end MeasureAlgebra
