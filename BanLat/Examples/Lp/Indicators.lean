/-
Authors: Pedro Tradacete
-/

import BanLat.Examples.Lp.MeasureAlgebra

/-!
# Indicators and components of the constant function

For a finite measure, indicators of measure-algebra elements are exactly the
components of the constant function one in `L¹`. This identifies the Boolean
structure needed to transport measure algebras through unital lattice isometries.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- The indicator map into `L¹` is injective. -/
theorem algebraIndicator_injective :
    Function.Injective (algebraIndicator (μ := μ) (p := 1)) := by
  let := (MeasureAlgebra.ofMeasure μ).toMetricSpace
  exact (isUniformEmbedding_algebraIndicator (μ := μ) (p := 1)).injective

private lemma algebraIndicator_mk_ae (s : MeasuredSets μ) :
    algebraIndicator (p := 1) (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =ᵐ[μ]
      s.val.indicator (fun _ ↦ (1 : ℝ)) :=
  indicatorConstLp_coeFn (hs := s.property) (hμs := measure_ne_top μ s)

/-- Indicators carry Boolean suprema to pointwise suprema in `L¹`. -/
theorem algebraIndicator_sup (a b : MeasureAlgebra.InducedBooleanAlgebra μ) :
    algebraIndicator (p := 1) (a ⊔ b) = algebraIndicator a ⊔ algebraIndicator b := by
  obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ a
  obtain ⟨t, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ b
  rw [← MeasureAlgebra.InducedBooleanAlgebra.mk_sup]
  apply Lp.ext
  filter_upwards [algebraIndicator_mk_ae (s ⊔ t), algebraIndicator_mk_ae s,
    algebraIndicator_mk_ae t,
    Lp.coeFn_sup (algebraIndicator (p := 1) (MeasureAlgebra.InducedBooleanAlgebra.mk μ s))
      (algebraIndicator (MeasureAlgebra.InducedBooleanAlgebra.mk μ t))] with x h₁ h₂ h₃ h₄
  suffices h : (s.val ∪ t.val).indicator (fun _ ↦ (1 : ℝ)) x =
      max (s.val.indicator (fun _ ↦ (1 : ℝ)) x)
        (t.val.indicator (fun _ ↦ (1 : ℝ)) x) from
    h₁.trans (h.trans ((congrArg₂ max h₂ h₃).symm.trans h₄.symm))
  by_cases hs : x ∈ s.val <;> by_cases ht : x ∈ t.val <;>
    simp [Set.indicator, hs, ht]

/-- Indicators carry Boolean infima to pointwise infima in `L¹`. -/
theorem algebraIndicator_inf (a b : MeasureAlgebra.InducedBooleanAlgebra μ) :
    algebraIndicator (p := 1) (a ⊓ b) = algebraIndicator a ⊓ algebraIndicator b := by
  apply add_left_cancel (a := algebraIndicator (p := 1) (a ⊔ b))
  have h := congrArg (fun g : Lp.simpleFunc ℝ (1 : ℝ≥0∞) μ ↦ (g : Lp ℝ 1 μ))
    (indicatorSimpleFunc_valuation (p := 1) a b 1)
  change algebraIndicator (p := 1) (a ⊔ b) + algebraIndicator (a ⊓ b) =
    algebraIndicator a + algebraIndicator b at h
  simpa only [← algebraIndicator_sup] using h.trans
    (((add_comm _ _).trans
      (inf_add_sup (algebraIndicator (p := 1) a) (algebraIndicator b))).symm)

/-- The indicator of the bottom element is zero. -/
@[simp]
theorem algebraIndicator_bot : algebraIndicator (μ := μ) (p := 1) ⊥ = 0 :=
  congrArg (fun g : Lp.simpleFunc ℝ (1 : ℝ≥0∞) μ ↦ (g : Lp ℝ 1 μ))
    (indicatorSimpleFunc_bot (μ := μ) (p := 1) 1)

/-- The indicator of the top element is the constant function one. -/
@[simp]
theorem algebraIndicator_top : algebraIndicator (μ := μ) (p := 1) ⊤ = Lp.const 1 μ (1 : ℝ) :=
  indicatorConstLp_univ 1 μ 1

/-- Complementary Boolean elements give complementary indicators. -/
theorem algebraIndicator_compl (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    algebraIndicator (p := 1) aᶜ = Lp.const 1 μ (1 : ℝ) - algebraIndicator a := by
  have h := congrArg (fun g : Lp.simpleFunc ℝ (1 : ℝ≥0∞) μ ↦ (g : Lp ℝ 1 μ))
    (indicatorSimpleFunc_valuation (p := 1) a aᶜ 1)
  change algebraIndicator (p := 1) (a ⊔ aᶜ) + algebraIndicator (a ⊓ aᶜ) =
    algebraIndicator a + algebraIndicator aᶜ at h
  rw [sup_compl_eq_top, inf_compl_eq_bot, algebraIndicator_bot, algebraIndicator_top,
    add_zero] at h
  exact eq_sub_of_add_eq' h.symm

/-- Every indicator is disjoint from its complement in the constant function one. -/
theorem algebraIndicator_inf_sub (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    algebraIndicator (p := 1) a ⊓ (Lp.const 1 μ (1 : ℝ) - algebraIndicator a) = 0 := by
  rw [← algebraIndicator_compl, ← algebraIndicator_inf, inf_compl_eq_bot, algebraIndicator_bot]

private lemma ae_zero_or_one (f : Lp ℝ 1 μ)
    (hf : f ⊓ (Lp.const 1 μ (1 : ℝ) - f) = 0) :
    ∀ᵐ x ∂μ, f x = 0 ∨ f x = 1 := by
  have hzero : (f ⊓ (Lp.const 1 μ (1 : ℝ) - f) : Lp ℝ 1 μ) =ᵐ[μ] (fun _ ↦ 0) :=
    hf ▸ Lp.coeFn_zero _ _ _
  filter_upwards [hzero, Lp.coeFn_inf f (Lp.const 1 μ (1 : ℝ) - f),
    Lp.coeFn_sub (Lp.const 1 μ (1 : ℝ)) f, Lp.coeFn_const (p := 1) (μ := μ) (c := (1 : ℝ))]
    with x h₀ h₁ h₂ h₃
  have hmin : min (f x) (1 - f x) = 0 :=
    (congrArg (min (f x)) (h₂.trans (congrArg (· - f x) h₃))).symm.trans
      (h₁.symm.trans h₀)
  rcases le_total (f x) (1 - f x) with hle | hle
  · exact Or.inl ((min_eq_left hle).symm.trans hmin)
  · exact Or.inr (sub_eq_zero.mp ((min_eq_right hle).symm.trans hmin)).symm

/-- Every component of the constant function one in `L¹` is an indicator. -/
theorem exists_algebraIndicator_eq (f : Lp ℝ 1 μ)
    (hf : f ⊓ (Lp.const 1 μ (1 : ℝ) - f) = 0) :
    ∃ a : MeasureAlgebra.InducedBooleanAlgebra μ, algebraIndicator (p := 1) a = f := by
  let s : Set α := {x | f x = 1}
  have hs : MeasurableSet s :=
    (Lp.stronglyMeasurable f).measurable (measurableSet_singleton 1)
  refine ⟨MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩, Lp.ext ?_⟩
  filter_upwards [algebraIndicator_mk_ae ⟨s, hs⟩, ae_zero_or_one f hf] with x hx hfx
  rcases hfx with hfx | hfx
  · simpa [s, hfx] using hx
  · simpa [s, hfx] using hx

/-- The `L¹` norm of an indicator is the measure of its Boolean element. -/
theorem norm_algebraIndicator (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
    ‖algebraIndicator (p := 1) a‖ = ((MeasureAlgebra.ofMeasure μ) a).toReal := by
  simpa [algebraIndicator] using norm_indicatorSimpleFunc (p := 1) a 1

end MeasureTheory.Lp
