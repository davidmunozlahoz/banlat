/-
Authors: Pedro Tradacete
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.OfMeasure

/-!
# Measurable subalgebras of a measure algebra

A sigma-complete Boolean subalgebra of the measure algebra of a finite measure
determines a smaller sigma-algebra on the original space. Its induced measure algebra
is naturally equivalent to the prescribed Boolean subalgebra.
-/

noncomputable section

open MeasureTheory

namespace MeasureAlgebra

variable {α : Type*} [m : MeasurableSpace α] {μ : Measure α}
  (A : BooleanSubalgebra (InducedBooleanAlgebra μ)) (hA : A.IsSigmaComplete)

/-- The sigma-algebra of measurable sets whose equivalence classes lie in `A`. -/
@[instance_reducible]
def subalgebraMeasurableSpace : MeasurableSpace α where
  MeasurableSet' s := ∃ hs : MeasurableSet s, InducedBooleanAlgebra.mk μ ⟨s, hs⟩ ∈ A
  measurableSet_empty := ⟨MeasurableSet.empty, InducedBooleanAlgebra.mk_bot μ ▸ A.bot_mem⟩
  measurableSet_compl := fun s hs ↦ by
    obtain ⟨hs, hAs⟩ := hs
    exact ⟨hs.compl, InducedBooleanAlgebra.mk_compl μ ⟨s, hs⟩ ▸ A.compl_mem hAs⟩
  measurableSet_iUnion := by
    rintro s hs
    refine ⟨MeasurableSet.iUnion fun n ↦ (hs n).choose, ?_⟩
    exact (InducedBooleanAlgebra.mk_iUnion μ (fun n ↦ ⟨s n, (hs n).choose⟩)) ▸
      hA.iSup_mem _ (fun n ↦ (hs n).choose_spec)

/-- Every set measurable for the subalgebra is measurable for the original measure. -/
theorem subalgebraMeasurableSpace_le : subalgebraMeasurableSpace A hA ≤ m :=
  fun _ hs ↦ hs.choose

/-- The original measure restricted to the sigma-algebra determined by `A`. -/
def subalgebraMeasure : @Measure α (subalgebraMeasurableSpace A hA) :=
  μ.trim (subalgebraMeasurableSpace_le A hA)

private def subalgebraClass :
    letI := subalgebraMeasurableSpace A hA
    InducedBooleanAlgebra (@subalgebraMeasure α m μ A hA) → A := by
  let := subalgebraMeasurableSpace A hA
  refine Quotient.lift
    (fun s : MeasuredSets (@subalgebraMeasure α m μ A hA) ↦
      ⟨@InducedBooleanAlgebra.mk α m μ
        ⟨s, @subalgebraMeasurableSpace_le α m μ A hA _ s.property⟩, s.property.choose_spec⟩) ?_
  intro s t h
  apply Subtype.ext
  apply (@InducedBooleanAlgebra.mk_eq_mk α m μ _ _).mpr
  have hzero := (InducedBooleanAlgebra.mk_eq_mk
    (@subalgebraMeasure α m μ A hA) s t).mp (Quotient.sound h)
  exact (trim_measurableSet_eq
    (@subalgebraMeasurableSpace_le α m μ A hA) (s.property.symmDiff t.property)).symm.trans hzero

private lemma subalgebraClass_le_iff :
    letI := subalgebraMeasurableSpace A hA
    ∀ a b : InducedBooleanAlgebra (@subalgebraMeasure α m μ A hA),
      @subalgebraClass α m μ A hA a ≤ @subalgebraClass α m μ A hA b ↔ a ≤ b := by
  let := subalgebraMeasurableSpace A hA
  intro a b
  refine Quotient.inductionOn₂ a b fun s t ↦ ?_
  change @InducedBooleanAlgebra.mk α m μ ⟨s, _⟩ ≤
    @InducedBooleanAlgebra.mk α m μ ⟨t, _⟩ ↔
      InducedBooleanAlgebra.mk (@subalgebraMeasure α m μ A hA) s ≤
        InducedBooleanAlgebra.mk (@subalgebraMeasure α m μ A hA) t
  exact (@InducedBooleanAlgebra.mk_le_mk_iff α m μ _ _).trans
    ((congrArg (· = 0) (trim_measurableSet_eq
      (@subalgebraMeasurableSpace_le α m μ A hA) (s.property.diff t.property)).symm).to_iff.trans
        (InducedBooleanAlgebra.mk_le_mk_iff (@subalgebraMeasure α m μ A hA) s t).symm)

private lemma subalgebraClass_surjective :
    Function.Surjective (subalgebraClass A hA) := by
  rintro ⟨a, ha⟩
  obtain ⟨s, hs⟩ := InducedBooleanAlgebra.mk_surjective μ a
  let := subalgebraMeasurableSpace A hA
  refine ⟨InducedBooleanAlgebra.mk (@subalgebraMeasure α m μ A hA)
    ⟨s, ⟨s.property, hs ▸ ha⟩⟩, ?_⟩
  exact Subtype.ext hs

/-- Restricting a finite measure to the sigma-algebra of a Boolean subalgebra is finite. -/
instance instIsFiniteMeasureSubalgebra [IsFiniteMeasure μ] :
    @IsFiniteMeasure α (subalgebraMeasurableSpace A hA) (subalgebraMeasure A hA) :=
  inferInstanceAs (@IsFiniteMeasure α _ (μ.trim (subalgebraMeasurableSpace_le A hA)))

/-- The measure algebra of the induced sigma-algebra is equivalent to `A`. -/
def subalgebraMeasureEquiv [IsFiniteMeasure μ] :
    letI := hA.toSigmaCompleteBooleanAlgebra
    MeasureAlgebraEquiv
      (@ofMeasure α (subalgebraMeasurableSpace A hA) (subalgebraMeasure A hA) _)
      ((ofMeasure μ).restrictToSubalgebra A hA) := by
  let := hA.toSigmaCompleteBooleanAlgebra
  refine
    { OrderIso.ofSurjective
        (OrderEmbedding.ofMapLEIff (subalgebraClass A hA) (subalgebraClass_le_iff A hA))
        (subalgebraClass_surjective A hA) with
      map_measure' := ?_ }
  intro b
  refine Quotient.inductionOn b fun s ↦ ?_
  exact (trim_measurableSet_eq (subalgebraMeasurableSpace_le A hA) s.property).symm

/-- The induced equivalence sends the class of a measurable set to its original class. -/
@[simp]
theorem subalgebraMeasureEquiv_mk [IsFiniteMeasure μ]
    (s : @MeasuredSets α (subalgebraMeasurableSpace A hA) (subalgebraMeasure A hA)) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (((subalgebraMeasureEquiv A hA).toRelIso
      (@InducedBooleanAlgebra.mk α (subalgebraMeasurableSpace A hA)
        (subalgebraMeasure A hA) s) : A) : InducedBooleanAlgebra μ) =
      InducedBooleanAlgebra.mk μ ⟨s, subalgebraMeasurableSpace_le A hA _ s.property⟩ := by
  let := hA.toSigmaCompleteBooleanAlgebra
  rfl

end MeasureAlgebra
