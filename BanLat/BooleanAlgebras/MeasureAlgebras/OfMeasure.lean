/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Atomless
import BanLat.BooleanAlgebras.MeasureAlgebras.Metric
import BanLat.Preliminaries.HasNoAtoms
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Measure algebras induced by measures

This file constructs the measure algebra `(Σ/∼, μ₀)` induced by a finite
measure space `(Ω, Σ, μ)` as follows:

Define the equivalence relation given by `∀ A, B ∈ Σ: A ∼ B ↔ μ (A ∆ B) = 0`.

Then:
* `Σ/∼` becomes a `σ`-complete Boolean algebra.
* `μ₀ : Σ/∼ → [0, ∞], μ₀([A]) = μ(A)` is a well-defined function.
* The pair `(Σ/∼, μ₀)` becomes a measure algebra.

Several properties of this induced measure algebra are proven.
-/

open MeasureTheory
open scoped ENNReal symmDiff

universe u

namespace MeasureAlgebra

variable {α : Type u} [MeasurableSpace α]

/-- The Boolean algebra of measurable sets modulo equality almost everywhere
with respect to `μ`. -/
def InducedBooleanAlgebra (μ : Measure α) : Type u :=
  SeparationQuotient (MeasuredSets μ)

namespace InducedBooleanAlgebra

variable (μ : Measure α)

/-- Measurable sets become a Boolean algebra with the usual operations and order. -/
noncomputable instance instBooleanAlgebraMeasuredSets :
    BooleanAlgebra (MeasuredSets μ) :=
  MeasurableSet.Subtype.instBooleanAlgebra

/-- The Boolean ring operations on measurable sets are `A + B = A ∆ B`,
`A * B = A ∩ B`, `-A = A`, `0 = ∅`, and `1 = Set.univ`. -/
noncomputable instance instBooleanRingMeasuredSets :
    BooleanRing (MeasuredSets μ) :=
  BooleanAlgebra.toBooleanRing

/-- For measurable sets `A`, `B`, `C`, and `D`:
`μ ((A ∆ B) ∆ (C ∆ D)) ≤ 2 * max{μ (A ∆ C), μ (B ∆ D)}`. -/
theorem lipschitzWith_add_measuredSets :
    LipschitzWith 2 (fun p : MeasuredSets μ × MeasuredSets μ ↦ p.1 + p.2) := by
  intro p q
  rw [MeasuredSets.edist_def, Prod.edist_eq]
  change μ (((p.1 : Set α) ∆ p.2) ∆ ((q.1 : Set α) ∆ q.2)) ≤
    (2 : ℝ≥0∞) * max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2))
  calc
    μ (((p.1 : Set α) ∆ p.2) ∆ ((q.1 : Set α) ∆ q.2)) =
        μ (((p.1 : Set α) ∆ q.1) ∆ ((p.2 : Set α) ∆ q.2)) := by
      congr 1
      ext x
      simp only [Set.mem_symmDiff]
      tauto
    _ ≤ (2 : ℝ≥0∞) * max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2)) := by
      calc
        μ (((p.1 : Set α) ∆ q.1) ∆ ((p.2 : Set α) ∆ q.2)) ≤
            μ ((p.1 : Set α) ∆ q.1) + μ ((p.2 : Set α) ∆ q.2) := by
          simpa only [symmDiff_bot, bot_symmDiff] using
            measure_symmDiff_le (μ := μ) ((p.1 : Set α) ∆ q.1) (⊥ : Set α)
            ((p.2 : Set α) ∆ q.2)
        _ ≤ max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2)) +
            max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2)) :=
          add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = (2 : ℝ≥0∞) * max (μ ((p.1 : Set α) ∆ q.1))
            (μ ((p.2 : Set α) ∆ q.2)) := (two_mul _).symm

/-- For measurable sets `A`, `B`, `C`, and `D`
`μ ((A ∩ B) ∆ (C ∩ D)) ≤ 2 * max{μ (A ∆ C), μ (B ∆ D)}`. -/
theorem lipschitzWith_mul_measuredSets :
    LipschitzWith 2 (fun p : MeasuredSets μ × MeasuredSets μ ↦ p.1 * p.2) := by
  intro p q
  rw [MeasuredSets.edist_def, Prod.edist_eq]
  change μ (((p.1 : Set α) ∩ p.2) ∆ ((q.1 : Set α) ∩ q.2)) ≤
    (2 : ℝ≥0∞) * max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2))
  calc
    μ (((p.1 : Set α) ∩ p.2) ∆ ((q.1 : Set α) ∩ q.2)) ≤
        μ (((p.1 : Set α) ∆ q.1) ∪ ((p.2 : Set α) ∆ q.2)) := by
      apply MeasureTheory.measure_mono
      grind
    _ ≤ (2 : ℝ≥0∞) * max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2)) := by
      calc
        μ (((p.1 : Set α) ∆ q.1) ∪ ((p.2 : Set α) ∆ q.2)) ≤
            μ ((p.1 : Set α) ∆ q.1) + μ ((p.2 : Set α) ∆ q.2) := measure_union_le _ _
        _ ≤ max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2)) +
            max (μ ((p.1 : Set α) ∆ q.1)) (μ ((p.2 : Set α) ∆ q.2)) :=
          add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = (2 : ℝ≥0∞) * max (μ ((p.1 : Set α) ∆ q.1))
            (μ ((p.2 : Set α) ∆ q.2)) := (two_mul _).symm

/-- The Boolean ring operations on measurable sets are continuous for the topology
induced by the measure of symmetric differences. -/
private instance instIsTopologicalRingMeasuredSets : IsTopologicalRing (MeasuredSets μ) where
  continuous_add := (lipschitzWith_add_measuredSets μ).uniformContinuous.continuous
  continuous_mul := (lipschitzWith_mul_measuredSets μ).uniformContinuous.continuous
  continuous_neg := continuous_id

/-- The separation quotient inherits a ring structure, and multiplication remains
idempotent, giving the induced measure algebra a Boolean ring structure. -/
@[implicit_reducible]
private noncomputable def booleanRingInduced : BooleanRing (InducedBooleanAlgebra μ) where
  __ := (SeparationQuotient.instCommRing (R := MeasuredSets μ)).toRing
  isIdempotentElem a := by
    induction a using Quotient.inductionOn
    change SeparationQuotient.mk (_ * _) = SeparationQuotient.mk _
    exact congrArg SeparationQuotient.mk (BooleanRing.mul_self _)

/-- The Boolean algebra structure obtained from the induced Boolean ring. -/
@[implicit_reducible]
private noncomputable instance instBooleanAlgebraInduced :
    BooleanAlgebra (InducedBooleanAlgebra μ) :=
  letI := booleanRingInduced μ
  BooleanRing.toBooleanAlgebra

/-- The equivalence class of a measurable set in the
measure algebra induced by `μ`. -/
noncomputable def mk : MeasuredSets μ → InducedBooleanAlgebra μ :=
  SeparationQuotient.mk

/-- Two measurable sets determine the same element of the induced measure
algebra exactly when their symmetric difference is null. -/
@[simp]
theorem mk_eq_mk (s t : MeasuredSets μ) :
    mk μ s = mk μ t ↔ μ ((s : Set α) ∆ (t : Set α)) = 0 := by
  change SeparationQuotient.mk s = SeparationQuotient.mk t ↔
    μ ((s : Set α) ∆ (t : Set α)) = 0
  rw [SeparationQuotient.mk_eq_mk, EMetric.inseparable_iff, MeasuredSets.edist_def]

/-- The quotient map preserves infima. -/
@[simp]
theorem mk_inf (s t : MeasuredSets μ) :
    mk μ (s ⊓ t) = mk μ s ⊓ mk μ t := by
  rfl

/-- Order between equivalence classes is almost-everywhere inclusion of
their measurable representatives. -/
theorem mk_le_mk_iff (s t : MeasuredSets μ) :
    mk μ s ≤ mk μ t ↔ μ ((s : Set α) \ (t : Set α)) = 0 := by
  rw [← inf_eq_left, ← mk_inf, mk_eq_mk]
  have hset : ((s ⊓ t : MeasuredSets μ) : Set α) ∆ (s : Set α) =
      (s : Set α) \ (t : Set α) := by
    change (((s : Set α) ∩ (t : Set α)) ∆ (s : Set α)) =
      (s : Set α) \ (t : Set α)
    ext x
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [hset]

/-- The supremum of a countable set of equivalence classes, obtained by taking the union
of chosen measurable representatives; defined to be `⊥` for uncountable sets. -/
private noncomputable def countableSup (s : Set (InducedBooleanAlgebra μ)) :
    InducedBooleanAlgebra μ := by
  classical
  exact if hs : s.Countable then
      letI := hs.to_subtype
      mk μ ⟨⋃ q : s, ((Quotient.out q.1 : MeasuredSets μ) : Set α),
        MeasurableSet.iUnion fun q ↦ (Quotient.out q.1 : MeasuredSets μ).property⟩
    else
      mk μ ⊥

/-- For countable `s`, `countableSup μ s` is the least upper bound of `s` in the quotient order. -/
private theorem isLUB_countableSup (s : Set (InducedBooleanAlgebra μ)) (hs : s.Countable) :
    IsLUB s (countableSup μ s) := by
  rw [countableSup, dite_eq_left hs]
  let := hs.to_subtype
  constructor
  · rintro q hq
    have hq_out : mk μ (Quotient.out q : MeasuredSets μ) = q := by
      exact Quotient.out_eq' q
    rw [← hq_out]
    apply (mk_le_mk_iff μ _ _).2
    have hsubset : ((Quotient.out q : MeasuredSets μ) : Set α) ⊆
        ⋃ r : s, ((Quotient.out r.1 : MeasuredSets μ) : Set α) :=
      Set.subset_iUnion (fun r : s ↦ ((Quotient.out r.1 : MeasuredSets μ) : Set α))
        (⟨q, hq⟩ : s)
    change μ (((Quotient.out q : MeasuredSets μ) : Set α) \
      (⋃ r : s, ((Quotient.out r.1 : MeasuredSets μ) : Set α))) = 0
    rw [Set.sdiff_eq_empty.mpr hsubset, measure_empty]
  · intro b hb
    have hb_out : mk μ (Quotient.out b : MeasuredSets μ) = b := by
      exact Quotient.out_eq' b
    rw [← hb_out]
    apply (mk_le_mk_iff μ _ _).2
    change μ ((⋃ q : s, ((Quotient.out q.1 : MeasuredSets μ) : Set α)) \
      ((Quotient.out b : MeasuredSets μ) : Set α)) = 0
    rw [Set.iUnion_sdiff]
    apply measure_iUnion_null
    intro q
    have hq_out : mk μ (Quotient.out q.1 : MeasuredSets μ) = q.1 := by
      exact Quotient.out_eq' q.1
    have hle : mk μ (Quotient.out q.1 : MeasuredSets μ) ≤
        mk μ (Quotient.out b : MeasuredSets μ) := by
      rw [hq_out, hb_out]
      exact hb q.property
    exact (mk_le_mk_iff μ _ _).1 hle

/-- The measure algebra induced by a measure is a `σ`-complete Boolean algebra. -/
noncomputable instance instSigmaCompleteBooleanAlgebra :
    SigmaCompleteBooleanAlgebra (InducedBooleanAlgebra μ) := by
  exact
    { instBooleanAlgebraInduced μ with
      sSup := countableSup μ
      isLUB_sSup_of_countable := isLUB_countableSup μ }

/-- Every element of the induced measure algebra has a measurable
representative. -/
theorem mk_surjective : Function.Surjective (mk μ) := by
  exact SeparationQuotient.surjective_mk

/-- Inclusion of measurable representatives induces order in the measure
algebra. -/
theorem mk_le_mk_of_subset {s t : MeasuredSets μ}
    (h : (s : Set α) ⊆ (t : Set α)) :
    mk μ s ≤ mk μ t := by
  apply (mk_le_mk_iff μ s t).2
  rw [Set.sdiff_eq_empty.mpr h, measure_empty]

/-- The quotient map sends the empty measurable set to the bottom element. -/
@[simp]
theorem mk_bot :
    mk μ (⊥ : MeasuredSets μ) = ⊥ := by
  rfl

/-- Disjoint measurable sets determine disjoint elements of the induced Boolean algebra. -/
theorem mk_disjoint (s t : MeasuredSets μ) (hst : Disjoint s.val t.val) :
    Disjoint (mk μ s) (mk μ t) := by
  exact disjoint_iff_inf_le.mpr <|
    ((mk_inf μ s t).symm.trans
      ((congrArg (mk μ) (Subtype.ext hst.eq_bot)).trans (mk_bot μ))).le

/-- The quotient map sends the whole measurable space to the top element. -/
@[simp]
theorem mk_top :
    mk μ (⊤ : MeasuredSets μ) = ⊤ := by
  rfl

/-- A nonzero measure induces a nontrivial Boolean algebra. -/
theorem nontrivial_of_ne_zero (hμ : μ ≠ 0) : Nontrivial (InducedBooleanAlgebra μ) := by
  refine nontrivial_of_ne (mk μ ⊤) (mk μ ⊥) ?_
  rw [Ne, mk_eq_mk]
  change μ ((⊤ : Set α) ∆ ⊥) ≠ 0
  rw [symmDiff_bot]
  exact Measure.measure_univ_ne_zero.mpr hμ

/-- The quotient map preserves complements. -/
@[simp]
theorem mk_compl (s : MeasuredSets μ) :
    mk μ sᶜ = (mk μ s)ᶜ := by
  let := booleanRingInduced μ
  change mk μ sᶜ = 1 + mk μ s
  change mk μ sᶜ = mk μ ((⊤ : MeasuredSets μ) ∆ s)
  exact congrArg (mk μ) (top_symmDiff s).symm

/-- The quotient map preserves finite suprema. -/
@[simp]
theorem mk_sup (s t : MeasuredSets μ) :
    mk μ (s ⊔ t) = mk μ s ⊔ mk μ t := by
  calc
    mk μ (s ⊔ t) = mk μ ((sᶜ ⊓ tᶜ)ᶜ) := by simp
    _ = (mk μ (sᶜ ⊓ tᶜ))ᶜ := mk_compl μ _
    _ = (mk μ sᶜ ⊓ mk μ tᶜ)ᶜ := congrArg compl (mk_inf μ _ _)
    _ = mk μ s ⊔ mk μ t := by rw [mk_compl, mk_compl, compl_inf, compl_compl, compl_compl]

/-- The quotient map preserves Boolean differences. -/
@[simp]
theorem mk_sdiff (s t : MeasuredSets μ) :
    mk μ (s \ t) = mk μ s \ mk μ t := by
  rw [sdiff_eq, mk_inf, mk_compl, sdiff_eq]

/-- The quotient map sends countable unions to countable suprema. -/
@[simp]
theorem mk_iUnion (s : ℕ → MeasuredSets μ) :
    mk μ ⟨⋃ n, (s n : Set α), MeasurableSet.iUnion fun n ↦ (s n).property⟩ =
      ⨆ n, mk μ (s n) := by
  apply le_antisymm
  · let b : InducedBooleanAlgebra μ := ⨆ n, mk μ (s n)
    have hb_out : mk μ (Quotient.out b : MeasuredSets μ) = b := by
      exact Quotient.out_eq' b
    change mk μ ⟨⋃ n, (s n : Set α), MeasurableSet.iUnion fun n ↦ (s n).property⟩ ≤ b
    rw [← hb_out]
    apply (mk_le_mk_iff μ _ _).2
    change μ ((⋃ n, (s n : Set α)) \
      ((Quotient.out b : MeasuredSets μ) : Set α)) = 0
    rw [Set.iUnion_sdiff]
    apply measure_iUnion_null
    intro n
    apply (mk_le_mk_iff μ _ _).1
    rw [hb_out]
    exact SigmaCompleteBooleanAlgebra.le_sSup_of_countable
      (Set.countable_range fun n ↦ mk μ (s n)) ⟨n, rfl⟩
  · apply SigmaCompleteBooleanAlgebra.sSup_le_of_countable
      (Set.countable_range fun n ↦ mk μ (s n))
    rintro _ ⟨n, rfl⟩
    apply mk_le_mk_of_subset μ
    exact Set.subset_iUnion (fun n ↦ (s n : Set α)) n

/-- A measure space without measure-theoretic atoms induces
an atomless Boolean algebra. -/
theorem isAtomless_of_hasNoAtoms (μ : Measure α) (hμ : μ.HasNoAtoms) :
    BooleanAlgebra.IsAtomless (InducedBooleanAlgebra μ) := by
  intro q hq
  obtain ⟨s, rfl⟩ := mk_surjective μ q
  have hs_pos : 0 < μ (s : Set α) := by
    rw [pos_iff_ne_zero]
    intro hs_zero
    apply hq.1
    rw [← mk_bot, mk_eq_mk]
    change μ ((s : Set α) ∆ (⊥ : Set α)) = 0
    rw [symmDiff_bot]
    exact hs_zero
  apply hμ s.property hs_pos
  refine ⟨s.property, hs_pos, ?_⟩
  intro t ht_meas hts
  let t' : MeasuredSets μ := ⟨t, ht_meas⟩
  have hle : mk μ t' ≤ mk μ s := mk_le_mk_of_subset μ hts
  rcases hle.lt_or_eq with hlt | heq
  · left
    have hbot : mk μ t' = ⊥ := hq.2 (mk μ t') hlt
    rw [← mk_bot] at hbot
    have hz := (mk_eq_mk μ t' ⊥).1 hbot
    change μ ((t' : Set α) ∆ (⊥ : Set α)) = 0 at hz
    change μ (t' : Set α) = 0
    simpa only [symmDiff_bot] using hz
  · right
    apply measure_congr
    exact measure_symmDiff_eq_zero_iff.mp ((mk_eq_mk μ t' s).1 heq)

end InducedBooleanAlgebra

/-- The function on equivalence classes of measurable sets assigning to
each class the measure of any representative. -/
private noncomputable def inducedMeasureFun (μ : Measure α) :
    InducedBooleanAlgebra μ → ℝ≥0∞ :=
  Quotient.lift (fun s : MeasuredSets μ ↦ μ (s : Set α)) fun s t h ↦ by
    apply measure_congr
    apply measure_symmDiff_eq_zero_iff.mp
    rw [← MeasuredSets.edist_def]
    exact EMetric.inseparable_iff.mp h

/-- The induced measure of the class of a measurable set equals its original measure. -/
private theorem inducedMeasureFun_mk (μ : Measure α) (s : MeasuredSets μ) :
    inducedMeasureFun μ (InducedBooleanAlgebra.mk μ s) = μ (s : Set α) := by
  rfl

/-- The induced measure vanishes exactly at the bottom class. -/
private theorem inducedMeasureFun_eq_zero_iff (μ : Measure α)
    (q : InducedBooleanAlgebra μ) :
    inducedMeasureFun μ q = 0 ↔ q = ⊥ := by
  induction q using Quotient.inductionOn
  rename_i s
  change inducedMeasureFun μ (InducedBooleanAlgebra.mk μ _) = 0 ↔
    InducedBooleanAlgebra.mk μ _ = ⊥
  rw [inducedMeasureFun_mk, ← InducedBooleanAlgebra.mk_bot,
    InducedBooleanAlgebra.mk_eq_mk]
  change μ (s : Set α) = 0 ↔ μ ((s : Set α) ∆ (⊥ : Set α)) = 0
  rw [symmDiff_bot]

/-- A finite measure gives the top class finite induced measure. -/
private theorem inducedMeasureFun_top_ne_top (μ : Measure α) [IsFiniteMeasure μ] :
    inducedMeasureFun μ ⊤ ≠ ∞ := by
  rw [← InducedBooleanAlgebra.mk_top, inducedMeasureFun_mk]
  exact MeasureTheory.measure_ne_top μ Set.univ

/-- The induced measure is countably additive on pairwise disjoint classes. -/
private theorem inducedMeasureFun_iSup (μ : Measure α)
    {a : ℕ → InducedBooleanAlgebra μ}
    (ha : Pairwise fun i j ↦ Disjoint (a i) (a j)) :
    inducedMeasureFun μ (⨆ i, a i) = ∑' i, inducedMeasureFun μ (a i) := by
  let s : ℕ → MeasuredSets μ := fun n ↦ Quotient.out (a n)
  have hs (n : ℕ) : InducedBooleanAlgebra.mk μ (s n) = a n := by
    exact Quotient.out_eq' (a n)
  have had : Pairwise fun i j ↦ AEDisjoint μ (s i : Set α) (s j : Set α) := by
    intro i j hij
    change μ (((s i : MeasuredSets μ) ⊓ s j : MeasuredSets μ) : Set α) = 0
    rw [← inducedMeasureFun_mk, InducedBooleanAlgebra.mk_inf, hs, hs]
    exact (inducedMeasureFun_eq_zero_iff μ _).2 (ha hij).eq_bot
  simp_rw [← hs]
  rw [← InducedBooleanAlgebra.mk_iUnion, inducedMeasureFun_mk μ ⟨_, _⟩]
  simp_rw [inducedMeasureFun_mk]
  exact measure_iUnion₀ had fun n ↦ (s n).property.nullMeasurableSet

/-- The countably additive functional on the quotient induced by `μ`. -/
private noncomputable def inducedFunctional (μ : Measure α) :
    CountablyAdditiveFunctional (InducedBooleanAlgebra μ) where
  toFun := inducedMeasureFun μ
  map_bot' := (inducedMeasureFun_eq_zero_iff μ ⊥).2 rfl
  map_iSup' := fun {a} ha ↦ inducedMeasureFun_iSup μ (a := a) ha

/-- The measure algebra obtained from a finite measure by identifying
measurable sets that agree almost everywhere. -/
noncomputable def ofMeasure (μ : Measure α) [IsFiniteMeasure μ] :
    MeasureAlgebra (InducedBooleanAlgebra μ) := by
  exact (inducedFunctional μ).toMeasureAlgebra
    (inducedMeasureFun_top_ne_top μ) (inducedMeasureFun_eq_zero_iff μ)

/-- The induced measure of the equivalence class of a measurable set is its
original measure. -/
@[simp]
theorem ofMeasure_mk (μ : Measure α) [IsFiniteMeasure μ]
    (s : MeasuredSets μ) :
    ofMeasure μ (InducedBooleanAlgebra.mk μ s) = μ (s : Set α) := by
  exact inducedMeasureFun_mk μ s

/-- The total mass of the induced measure algebra is the mass of the whole
underlying measure space. -/
@[simp]
theorem ofMeasure_top (μ : Measure α) [IsFiniteMeasure μ] :
    ofMeasure μ ⊤ = μ Set.univ := by
  rw [← InducedBooleanAlgebra.mk_top, ofMeasure_mk]
  rfl

/-- `restrictClass` sends `[t]` modulo `μ.restrict s` to `[t ∩ s]`
modulo `μ`, viewed in the principal interval below `[s]`. -/
private noncomputable def restrictClass (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) :
    InducedBooleanAlgebra (μ.restrict s) → Set.Iic (InducedBooleanAlgebra.mk μ ⟨s, hs⟩) := by
  refine fun a ↦ Quotient.liftOn a
    (fun t : MeasuredSets (μ.restrict s) ↦
      ⟨InducedBooleanAlgebra.mk μ ⟨(t : Set α) ∩ s, t.property.inter hs⟩,
        InducedBooleanAlgebra.mk_le_mk_of_subset μ Set.inter_subset_right⟩) ?_
  intro t u h
  apply Subtype.ext
  rw [InducedBooleanAlgebra.mk_eq_mk μ ⟨_, _⟩ ⟨_, _⟩]
  change μ (((t : Set α) ∩ s) ∆ ((u : Set α) ∩ s)) = 0
  rw [← Set.inter_symmDiff_distrib_right, ← Measure.restrict_apply' hs]
  exact (InducedBooleanAlgebra.mk_eq_mk (μ.restrict s) t u).mp (Quotient.sound h)

/-- The intersection map preserves and reflects order between equivalence classes. -/
private lemma restrictClass_le_iff (μ : Measure α) {s : Set α} (hs : MeasurableSet s)
    (a b : InducedBooleanAlgebra (μ.restrict s)) :
    restrictClass μ hs a ≤ restrictClass μ hs b ↔ a ≤ b := by
  refine Quotient.inductionOn₂ a b ?_
  intro t u
  change InducedBooleanAlgebra.mk μ ⟨(t : Set α) ∩ s, t.property.inter hs⟩ ≤
      InducedBooleanAlgebra.mk μ ⟨(u : Set α) ∩ s, u.property.inter hs⟩ ↔
    InducedBooleanAlgebra.mk (μ.restrict s) t ≤ InducedBooleanAlgebra.mk (μ.restrict s) u
  rw [InducedBooleanAlgebra.mk_le_mk_iff μ ⟨_, _⟩ ⟨_, _⟩, InducedBooleanAlgebra.mk_le_mk_iff]
  change μ (((t : Set α) ∩ s) \ ((u : Set α) ∩ s)) = 0 ↔
    μ.restrict s ((t : Set α) \ (u : Set α)) = 0
  rw [← Set.inter_sdiff_distrib_right, Measure.restrict_apply' hs]

/-- Every class below `[s]` is the image of a class modulo `μ.restrict s`. -/
private lemma restrictClass_surjective (μ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    Function.Surjective (restrictClass μ hs) := by
  rintro ⟨b, hb⟩
  obtain ⟨t, rfl⟩ := InducedBooleanAlgebra.mk_surjective μ b
  refine ⟨InducedBooleanAlgebra.mk (μ.restrict s) ⟨t.val, t.property⟩, ?_⟩
  exact Subtype.ext ((InducedBooleanAlgebra.mk_inf μ t ⟨s, hs⟩).trans (inf_eq_left.mpr hb))

/-- Restricting a finite measure to a measurable set induces a measure-algebra equivalence
with the principal interval below the class of that set. -/
noncomputable def ofMeasureRestrictEquiv (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    MeasureAlgebraEquiv (ofMeasure (μ.restrict s))
      ((ofMeasure μ).restrict (InducedBooleanAlgebra.mk μ ⟨s, hs⟩)) := by
  let e := OrderEmbedding.ofMapLEIff (restrictClass μ hs) (restrictClass_le_iff μ hs)
  refine { OrderIso.ofSurjective e (restrictClass_surjective μ hs) with map_measure' := ?_ }
  intro a
  refine Quotient.inductionOn a ?_
  intro t
  change ofMeasure μ (InducedBooleanAlgebra.mk μ ⟨(t : Set α) ∩ s, t.property.inter hs⟩) =
    ofMeasure (μ.restrict s) (InducedBooleanAlgebra.mk (μ.restrict s) t)
  rw [ofMeasure_mk μ ⟨_, _⟩, ofMeasure_mk, Measure.restrict_apply' hs]
  rfl

/-- On measurable representatives, the restriction equivalence is intersection
with the restricting set. -/
@[simp]
theorem ofMeasureRestrictEquiv_mk (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) (t : MeasuredSets (μ.restrict s)) :
    ((ofMeasureRestrictEquiv μ hs).toRelIso (InducedBooleanAlgebra.mk (μ.restrict s) t)).val =
      InducedBooleanAlgebra.mk μ ⟨(t : Set α) ∩ s, t.property.inter hs⟩ := by
  rfl

namespace InducedBooleanAlgebra

/-- A measure-dense family of measurable representatives has dense image in the
induced measure algebra. -/
theorem dense_range_mk_of_measureDense
    (μ : Measure α) [IsFiniteMeasure μ] {A : Set (Set α)}
    (hA : μ.MeasureDense A) :
    letI := (ofMeasure μ).toMetricSpace
    Dense (Set.range fun s : A ↦
      mk μ ⟨s, hA.measurable s s.property⟩) := by
  let := (ofMeasure μ).toMetricSpace
  rw [Metric.dense_iff]
  intro q r hr
  obtain ⟨s, rfl⟩ := mk_surjective μ q
  obtain ⟨t, htA, hst⟩ :=
    hA.approx (s : Set α) s.property (MeasureTheory.measure_ne_top μ s) r hr
  let tA : A := ⟨t, htA⟩
  refine ⟨mk μ ⟨t, hA.measurable t htA⟩, ⟨?_, ⟨tA, ?_⟩⟩⟩
  · rw [Metric.mem_ball, dist_comm,
      (ofMeasure μ).dist_eq_measure_symmDiff, symmDiff_def,
      ← mk_sdiff μ s ⟨_, _⟩, ← mk_sdiff μ ⟨_, _⟩ s, ← mk_sup, ← symmDiff_def s ⟨_, _⟩,
      ofMeasure_mk]
    have hreal :=
      (ENNReal.toReal_lt_toReal (ne_top_of_lt hst) ENNReal.ofReal_ne_top).2 hst
    change (μ ((s : Set α) ∆ t)).toReal < r
    simpa [ENNReal.toReal_ofReal hr.le] using hreal
  · rfl

/-- A finite separable measure induces a separable topology on its measure algebra. -/
theorem separableSpace_of_isSeparableMeasure
    (μ : Measure α) [IsFiniteMeasure μ] [MeasureTheory.IsSeparable μ] :
    letI := (ofMeasure μ).toMetricSpace
    TopologicalSpace.SeparableSpace (InducedBooleanAlgebra μ) := by
  let := (ofMeasure μ).toMetricSpace
  obtain ⟨A, hA_countable, hA_dense⟩ := exists_countable_measureDense μ
  let f : A → InducedBooleanAlgebra μ := fun t ↦
    mk μ ⟨t.1, hA_dense.measurable t.1 t.2⟩
  let D : Set (InducedBooleanAlgebra μ) := Set.range f
  let := hA_countable.to_subtype
  refine ⟨⟨D, Set.countable_range f, ?_⟩⟩
  simpa [D, f] using dense_range_mk_of_measureDense μ hA_dense

end InducedBooleanAlgebra

end MeasureAlgebra
