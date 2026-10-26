/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.MaharamType
import BanLat.Examples.Lp.MeasureAlgebra
import BanLat.Examples.Lp.WeakUnit
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.SetTheory.Cardinal.Finsupp
import Mathlib.SetTheory.Cardinal.Rat

/-!
# Density character of real `Lᵖ` spaces

For nonzero finite measure `μ` and `1 ≤ p < ∞`, the density character of `Lᵖ(μ)`
is the maximum between `ℵ₀` and the Maharam type of the induced measure algebra
of `μ`-measurable sets.

The density character of an order interval `[f, g]` equals that of `Lᵖ(μ.restrict s)`,
where `s` is the set on which `f` and `g` differ. Moreover, When `μ` is atomless, the
following are equivalent:
* every nontrivial order interval has full density
* the induced measure algebra is homogeneous.
-/

open scoped ENNReal NNReal

universe u

namespace MeasureTheory.Lp

variable {α : Type u} [MeasurableSpace α]
variable {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0}

private lemma maharamType_le_densityCharacter [Fact (1 ≤ p)] :
    (MeasureAlgebra.ofMeasure μ).maharamType ≤
      TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) := by
  letI := (MeasureAlgebra.ofMeasure μ).toMetricSpace
  exact TopologicalSpace.densityCharacter_le_of_isEmbedding
    (isUniformEmbedding_algebraIndicator (μ := μ) (p := p)).isEmbedding

private lemma dense_span_algebraIndicator [Fact (1 ≤ p)]
    {D : Set (MeasureAlgebra.InducedBooleanAlgebra μ)}
    (hD : letI := (MeasureAlgebra.ofMeasure μ).toMetricSpace; Dense D) :
    Dense (Submodule.span ℚ (algebraIndicator (p := p) '' D) :
      Set (Lp ℝ (p : ENNReal) μ)) := by
  letI := (MeasureAlgebra.ofMeasure μ).toMetricSpace
  let S := Submodule.span ℚ (algebraIndicator (p := p) '' D)
  have hcont := (isUniformEmbedding_algebraIndicator (μ := μ) (p := p)).isEmbedding.continuous
  have hI (a : MeasureAlgebra.InducedBooleanAlgebra μ) :
      algebraIndicator (p := p) a ∈ S.topologicalClosure := by
    exact (closure_mono (Submodule.subset_span (R := ℚ)))
      (hcont.range_subset_closure_image_dense hD (Set.mem_range_self a))
  refine fun f ↦ Lp.induction ENNReal.coe_ne_top (motive := fun f ↦ f ∈ S.topologicalClosure)
    ?_ ?_ S.isClosed_topologicalClosure f
  · intro c s hs hμs
    rw [simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul]
    refine Rat.denseRange_cast.induction_on c
      (S.isClosed_topologicalClosure.preimage (continuous_id.smul continuous_const)) ?_
    intro q
    rw [Rat.cast_smul_eq_qsmul]
    exact S.topologicalClosure.smul_mem q
      (hI (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩))
  · exact fun _ _ _ _ _ hf hg ↦ S.topologicalClosure.add_mem hf hg

private lemma densityCharacter_le_max_maharamType [Fact (1 ≤ p)] :
    TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) ≤
      max Cardinal.aleph0 (MeasureAlgebra.ofMeasure μ).maharamType := by
  letI := (MeasureAlgebra.ofMeasure μ).toMetricSpace
  obtain ⟨D, hD, hcard⟩ := TopologicalSpace.exists_dense_mk_eq_densityCharacter
    (MeasureAlgebra.InducedBooleanAlgebra μ)
  letI : Nonempty D := hD.nonempty.to_subtype
  let g : D → Lp ℝ (p : ENNReal) μ := fun a ↦ algebraIndicator a.val
  have hdense : DenseRange (Finsupp.linearCombination ℚ g) := by
    change Dense (Set.range (Finsupp.linearCombination ℚ g))
    simpa only [g, Set.image_eq_range, ← Finsupp.range_linearCombination,
      LinearMap.coe_range] using (dense_span_algebraIndicator (p := p) hD)
  refine ((TopologicalSpace.densityCharacter_le_mk_of_dense hdense).trans
    Cardinal.mk_range_le).trans_eq ?_
  simp [hcard, max_comm, MeasureAlgebra.maharamType,
    MeasureAlgebra.densityCharacter]

private lemma aleph0_le_densityCharacter [Fact (1 ≤ p)] (hμ : μ ≠ 0) :
    Cardinal.aleph0 ≤ TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) := by
  letI : NeZero μ := ⟨hμ⟩
  letI : Infinite (Lp ℝ (p : ENNReal) μ) :=
    Infinite.of_injective (Lp.const (p : ENNReal) μ : ℝ → Lp ℝ (p : ENNReal) μ)
      fun c d h ↦ ((Lp.coeFn_const (p : ENNReal) μ c).symm.trans
        ((Lp.ext_iff.mp h).trans (Lp.coeFn_const (p : ENNReal) μ d))).exists.choose_spec
  exact TopologicalSpace.aleph0_le_densityCharacter _

private lemma aleph0_le_maharamType
    (hμ : μ.HasNoAtoms) (hμ_ne_zero : μ ≠ 0) :
    Cardinal.aleph0 ≤ (MeasureAlgebra.ofMeasure μ).maharamType := by
  letI : Nontrivial (MeasureAlgebra.InducedBooleanAlgebra μ) :=
    MeasureAlgebra.InducedBooleanAlgebra.nontrivial_of_ne_zero μ hμ_ne_zero
  exact MeasureAlgebra.aleph0_le_maharamType_of_isAtomless (MeasureAlgebra.ofMeasure μ)
    (MeasureAlgebra.InducedBooleanAlgebra.isAtomless_of_hasNoAtoms μ hμ)

/-- For a nonzero finite measure `μ`, `Lᵖ(μ)` has density character equal to the maximum
of `ℵ₀` and the Maharam type of the induced measure algebra. -/
theorem densityCharacter_eq_max_maharamType [Fact (1 ≤ p)] (hμ : μ ≠ 0) :
    TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) =
      max Cardinal.aleph0 (MeasureAlgebra.ofMeasure μ).maharamType := by
  exact le_antisymm densityCharacter_le_max_maharamType
    (max_le (aleph0_le_densityCharacter hμ) maharamType_le_densityCharacter)

/-- For a nonzero finite atomless measure `μ`, `Lᵖ(μ)` has density character
equal to the Maharam type of the induced measure algebra. -/
theorem densityCharacter_eq_maharamType [Fact (1 ≤ p)]
    (hμ : μ.HasNoAtoms) (hμ_ne_zero : μ ≠ 0) :
    TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) =
      (MeasureAlgebra.ofMeasure μ).maharamType := by
  rw [densityCharacter_eq_max_maharamType hμ_ne_zero,
    max_eq_right (aleph0_le_maharamType hμ hμ_ne_zero)]

/-- For a finite atomless measure `μ`, `Lᵖ(μ.restrict s)` for a positive-measure measurable set
`s` has density character equal to the Maharam type below the class of `s`. -/
theorem densityCharacter_restrict_eq_maharamTypeBelow [Fact (1 ≤ p)]
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s) (hs_ne_zero : μ s ≠ 0) :
    TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) (μ.restrict s)) =
      (MeasureAlgebra.ofMeasure μ).maharamTypeBelow
        (MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩) := by
  rw [densityCharacter_eq_maharamType (hμ.restrict hs)
    (mt Measure.restrict_eq_zero.mp hs_ne_zero)]
  simpa only [MeasureAlgebra.maharamType, MeasureAlgebra.maharamTypeBelow,
    Cardinal.lift_id] using (MeasureAlgebra.ofMeasureRestrictEquiv μ hs).map_maharamType.symm

/-- A finite atomless measure `μ` induces a homogeneous measure algebra exactly when every
positive-measure measurable restriction preserves the density character of `Lᵖ(μ)`. -/
theorem isHomogeneous_iff_densityCharacter_restrict [Fact (1 ≤ p)]
    (hμ : μ.HasNoAtoms) :
    (MeasureAlgebra.ofMeasure μ).IsHomogeneous ↔
      ∀ s : Set α, MeasurableSet s → μ s ≠ 0 →
        TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) (μ.restrict s)) =
          TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) := by
  constructor
  · intro h s hs hs_ne_zero
    rw [densityCharacter_restrict_eq_maharamTypeBelow hμ hs hs_ne_zero,
      densityCharacter_eq_maharamType hμ (ne_of_apply_ne (fun ν : Measure α ↦ ν s) hs_ne_zero)]
    exact h (mt ((MeasureAlgebra.ofMeasure μ).measure_eq_zero_iff _).mpr hs_ne_zero)
  · intro h b hb
    obtain ⟨s, rfl⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ b
    have hs : μ (s : Set α) ≠ 0 :=
      mt ((MeasureAlgebra.ofMeasure μ).measure_eq_zero_iff
        (MeasureAlgebra.InducedBooleanAlgebra.mk μ s)).mp hb
    exact (densityCharacter_restrict_eq_maharamTypeBelow (p := p) hμ s.property hs).symm.trans
      ((h s s.property hs).trans
        (densityCharacter_eq_maharamType hμ (ne_of_apply_ne (fun ν : Measure α ↦ ν s) hs)))

/-- For a finite measure `μ`, `Lᵖ(μ)` is separable if and only if the Maharam type
of the induced measure algebra is at most countable. -/
theorem separableSpace_iff_maharamType_le_aleph0 [Fact (1 ≤ p)] :
    TopologicalSpace.SeparableSpace (Lp ℝ (p : ENNReal) μ) ↔
      (MeasureAlgebra.ofMeasure μ).maharamType ≤ Cardinal.aleph0 := by
  rw [TopologicalSpace.separableSpace_iff_densityCharacter_le_aleph0]
  exact ⟨fun h ↦ maharamType_le_densityCharacter.trans h,
    fun h ↦ densityCharacter_le_max_maharamType.trans (max_le le_rfl h)⟩

/-! ### Order intervals and homogeneity -/

section

omit [IsFiniteMeasure μ]

/-- Every element of `[0, f]` in `Lᵖ(μ)` vanishes `μ`-almost everywhere outside any set
supporting `f`. -/
private lemma indicator_eq_of_mem_Icc {s : Set α}
    {f g : Lp ℝ (p : ENNReal) μ} (hfs : s.indicator (f : α → ℝ) =ᵐ[μ] f)
    (hg : g ∈ Set.Icc (0 : Lp ℝ (p : ENNReal) μ) f) :
    s.indicator (g : α → ℝ) =ᵐ[μ] g := by
  filter_upwards [(Lp.coeFn_nonneg g).mpr hg.1, (Lp.coeFn_le g f).mpr hg.2, hfs]
    with x hg0 hgf hfx
  by_cases hx : x ∈ s <;> simp_all
  linarith

/-- For `f ∈ Lᵖ(μ)` supported `μ`-almost everywhere on `s`, extension by zero
identifies the interval below its restriction in `Lᵖ(μ.restrict s)` with
`[0, f]`, preserving density character. -/
private lemma densityCharacter_Icc_restrict [Fact (1 ≤ p)]
    {s : Set α} (hs : MeasurableSet s) {f : Lp ℝ (p : ENNReal) μ}
    (hfs : s.indicator (f : α → ℝ) =ᵐ[μ] f) :
    TopologicalSpace.densityCharacter (Set.Icc (0 : Lp ℝ (p : ENNReal) μ) f) =
      TopologicalSpace.densityCharacter
        (Set.Icc (0 : Lp ℝ (p : ENNReal) (μ.restrict s))
          (((Lp.memLp f).restrict s).toLp f)) := by
  let e := ((Lp.memLp f).restrict s).toLp f
  have hext : extendRestricted hs e = f := extendRestricted_restrict hs f hfs
  let j : Set.Icc (0 : Lp ℝ (p : ENNReal) (μ.restrict s)) e →
      Set.Icc (0 : Lp ℝ (p : ENNReal) μ) f := fun g ↦
    ⟨extendRestricted hs g.val,
      (by simpa only [extendRestricted_zero] using
        (extendRestricted_le_iff hs 0 g.val).mpr g.property.1),
      ((extendRestricted_le_iff hs g.val e).mpr g.property.2).trans_eq hext⟩
  have hj : Isometry j := fun a b ↦ isometry_extendRestricted hs a.val b.val
  have hsurj : Function.Surjective j := by
    intro g
    let r := ((Lp.memLp g.val).restrict s).toLp g.val
    have hr : extendRestricted hs r = g.val :=
      extendRestricted_restrict hs g.val (indicator_eq_of_mem_Icc hfs g.property)
    exact ⟨⟨r,
      (extendRestricted_le_iff hs 0 r).mp
        (by simpa only [extendRestricted_zero, hr] using g.property.1),
      (extendRestricted_le_iff hs r e).mp
        (by simpa only [hr, hext] using g.property.2)⟩, Subtype.ext hr⟩
  let E : Set.Icc (0 : Lp ℝ (p : ENNReal) (μ.restrict s)) e ≃ᵢ
      Set.Icc (0 : Lp ℝ (p : ENNReal) μ) f :=
    { Equiv.ofBijective j ⟨hj.injective, hsurj⟩ with isometry_toFun := hj }
  simpa only [Cardinal.lift_id] using
    TopologicalSpace.densityCharacter_eq_of_homeomorph E.toHomeomorph

end

/-- If `f ∈ Lᵖ(μ)` vanishes `μ`-almost everywhere outside `s` and is strictly positive
`μ.restrict s`-almost everywhere on `s`, then `[0, f]` has the density character of
`Lᵖ(μ.restrict s)`. -/
private lemma densityCharacter_Icc_of_ae_pos [Fact (1 ≤ p)]
    {s : Set α} (hs : MeasurableSet s) {f : Lp ℝ (p : ENNReal) μ}
    (hfs : s.indicator (f : α → ℝ) =ᵐ[μ] f)
    (hpos : ∀ᵐ x ∂μ.restrict s, 0 < f x) :
    TopologicalSpace.densityCharacter (Set.Icc (0 : Lp ℝ (p : ENNReal) μ) f) =
      TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) (μ.restrict s)) := by
  refine (densityCharacter_Icc_restrict hs hfs).trans
    (QuasiInteriorPoint.densityCharacter_Icc
      (quasiInteriorPoint_iff_weakOrderUnit.mpr (weakOrderUnit_iff_ae_pos.mpr ?_)))
  exact (((Lp.memLp f).restrict s).coeFn_toLp.and hpos).mono fun _ h ↦ h.1.symm ▸ h.2

/-- In `Lᵖ(μ)`, the interval below the unit indicator of `s` has the same density
character as `Lᵖ(μ.restrict s)`. -/
theorem densityCharacter_Icc_indicatorConstLp [Fact (1 ≤ p)]
    {s : Set α} (hs : MeasurableSet s) :
    TopologicalSpace.densityCharacter
      (Set.Icc (0 : Lp ℝ (p : ENNReal) μ)
        (indicatorConstLp (p : ENNReal) hs (measure_ne_top μ s) (1 : ℝ))) =
      TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) (μ.restrict s)) := by
  refine densityCharacter_Icc_of_ae_pos hs ?_ ?_
  · filter_upwards [indicatorConstLp_coeFn (p := (p : ENNReal)) (hs := hs)
      (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx
    by_cases hxs : x ∈ s <;> simp_all
  · filter_upwards [ae_restrict_of_ae (indicatorConstLp_coeFn
      (p := (p : ENNReal)) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℝ))),
      ae_restrict_mem hs] with x hx hxs
    simpa only [hx, Set.indicator_of_mem hxs] using (zero_lt_one : (0 : ℝ) < 1)

/-- The interval below a nonnegative element `f` of `Lᵖ(μ)` has the same density character as
`Lᵖ(μ.restrict support(f))`. -/
theorem densityCharacter_Icc_zero_eq_restrict_support [Fact (1 ≤ p)]
    {f : Lp ℝ (p : ENNReal) μ} (hf : 0 ≤ f) :
    TopologicalSpace.densityCharacter (Set.Icc (0 : Lp ℝ (p : ENNReal) μ) f) =
      TopologicalSpace.densityCharacter
        (Lp ℝ (p : ENNReal) (μ.restrict (Function.support (f : α → ℝ)))) := by
  have hs : MeasurableSet (Function.support (f : α → ℝ)) :=
    measurableSet_support (Lp.stronglyMeasurable f).measurable
  refine densityCharacter_Icc_of_ae_pos hs ?_ ?_
  · exact Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : f x = 0 <;> simp [Function.mem_support, hx]
  · exact ((ae_restrict_of_ae ((Lp.coeFn_nonneg f).mpr hf)).and (ae_restrict_mem hs)).mono
      fun _ h ↦ lt_of_le_of_ne h.1 (Ne.symm h.2)

/-- An order interval in `Lᵖ(μ)` has the same density character as
`Lᵖ(μ.restrict support(g - f))`, where `f` and `g` are its endpoints. -/
theorem densityCharacter_Icc_eq_restrict_support [Fact (1 ≤ p)]
    {f g : Lp ℝ (p : ENNReal) μ} (hfg : f ≤ g) :
    TopologicalSpace.densityCharacter (Set.Icc f g) =
      TopologicalSpace.densityCharacter
        (Lp ℝ (p : ENNReal) (μ.restrict (Function.support (fun x ↦ g x - f x)))) := by
  have himage : (Homeomorph.addRight (-f)) '' Set.Icc f g =
      Set.Icc (0 : Lp ℝ (p : ENNReal) μ) (g - f) := by
    change (fun x ↦ x + -f) '' Set.Icc f g = Set.Icc 0 (g - f)
    simpa only [OrderIso.addRight_apply, add_neg_cancel, ← sub_eq_add_neg] using
      (OrderIso.addRight (-f)).image_Icc f g
  let E := ((Homeomorph.addRight (-f)).image (Set.Icc f g)).trans
    (Homeomorph.setCongr himage)
  have hdens : TopologicalSpace.densityCharacter (Set.Icc f g) =
      TopologicalSpace.densityCharacter (Set.Icc (0 : Lp ℝ (p : ENNReal) μ) (g - f)) := by
    simpa only [Cardinal.lift_id] using
      (TopologicalSpace.densityCharacter_eq_of_homeomorph E).symm
  rw [hdens, densityCharacter_Icc_zero_eq_restrict_support (sub_nonneg.mpr hfg),
    Measure.restrict_congr_set (Lp.coeFn_sub g f).support]
  rfl

/-- The order intervals of `Lᵖ(μ)` have constant density character `κ` exactly when
`Lᵖ(μ.restrict s)` has density character `κ` for every positive-measure measurable set `s`. -/
theorem isOrderIntervalHomogeneous_iff_densityCharacter_restrict [Fact (1 ≤ p)]
    (κ : Cardinal.{u}) :
    TopologicalSpace.IsOrderIntervalHomogeneous (Lp ℝ (p : ENNReal) μ) κ ↔
      ∀ s : Set α, MeasurableSet s → μ s ≠ 0 →
        TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) (μ.restrict s)) = κ := by
  constructor
  · intro h s hs hs_ne_zero
    have hI : indicatorConstLp (p : ENNReal) hs (measure_ne_top μ s) (1 : ℝ) ≠ 0 := by
      intro hzero
      exact hs_ne_zero (ae_eq_empty.mp
        ((indicatorConstLp_inj (p := (p : ENNReal)) hs (measure_ne_top μ s)
          MeasurableSet.empty (measure_ne_top μ ∅) one_ne_zero).mp
            (by simpa only [indicatorConstLp_empty] using hzero)))
    exact (densityCharacter_Icc_indicatorConstLp hs).symm.trans
      (h (lt_of_le_of_ne (indicatorConstLp_nonneg hs (measure_ne_top μ s) zero_le_one)
        (Ne.symm hI)))
  · intro h f g hfg
    rw [densityCharacter_Icc_eq_restrict_support hfg.le]
    refine h _ (measurableSet_support
      ((Lp.stronglyMeasurable g).measurable.sub (Lp.stronglyMeasurable f).measurable)) ?_
    exact fun hz ↦ hfg.ne (Lp.ext ((μ.measure_support_eq_zero_iff.mp hz).mono
      fun _ hx ↦ (sub_eq_zero.mp hx).symm))

/-- For a finite atomless measure `μ`, every nontrivial order interval in `Lᵖ(μ)` has full
density exactly when the induced measure algebra is homogeneous. -/
theorem isOrderIntervalHomogeneous_iff_isHomogeneous [Fact (1 ≤ p)]
    (hμ : μ.HasNoAtoms) :
    TopologicalSpace.IsOrderIntervalHomogeneous (Lp ℝ (p : ENNReal) μ)
        (TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ)) ↔
      (MeasureAlgebra.ofMeasure μ).IsHomogeneous := by
  rw [isOrderIntervalHomogeneous_iff_densityCharacter_restrict,
    isHomogeneous_iff_densityCharacter_restrict (p := p) hμ]

end MeasureTheory.Lp
