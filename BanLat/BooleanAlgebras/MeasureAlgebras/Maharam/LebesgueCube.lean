/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.MaharamType
import BanLat.BooleanAlgebras.MeasureAlgebras.OfMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Lebesgue measure algebra and Lebesgue cube measure algebras

This file defines the measure algebra induced by Lebesgue measure on `[0, 1]`.
For every cardinal `κ`, it also defines the product probability space and
measure algebra `([0, 1]^κ, λ^κ)` of `κ` copies of Lebesgue measure.

It is shown that the Lebesgue measure algebra on `[0, 1]` is atomless, separable,
and has total mass one.

We also show that `([0, 1]^κ, λ^κ)`:
* has total mass one,
* is atomless and homogeneous for all `κ > 0`,
* is separable for all `κ ≤ ℵ₀`,
* has density character and Maharam type exactly `max ℵ₀ κ` for all `κ > 0`.
-/

noncomputable section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal symmDiff

universe u

namespace MeasureAlgebra

/-- The product of `κ` copies of Lebesgue measure on the unit interval as a product measure -/
noncomputable abbrev cubeMeasure (κ : Cardinal.{u}) :
    Measure (κ.out → unitInterval) :=
  Measure.infinitePi
    (fun _ : κ.out ↦ (volume : Measure unitInterval))

/-- Finite-coordinate measurable cylinders are measure-dense in each Lebesgue cube. -/
theorem cubeMeasure_measureDense_measurableCylinders (κ : Cardinal.{u}) :
    (cubeMeasure κ).MeasureDense
      (MeasureTheory.measurableCylinders (fun _ : κ.out ↦ unitInterval)) := by
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (cubeMeasure κ)
    MeasureTheory.isSetAlgebra_measurableCylinders
    MeasureTheory.generateFrom_measurableCylinders.symm

/-- For each `i ∈ κ`, the event on which we have that `0 ≤ xᵢ ≤ 1/2` . -/
def cubeHalfSpace (κ : Cardinal.{u}) (i : κ.out) :
    Set (κ.out → unitInterval) :=
  Function.eval i ⁻¹' Set.Iic ⟨1 / 2, by constructor <;> norm_num⟩

/-- For each `i ∈ κ`, the cubeHalfSpace is measurable . -/
theorem measurableSet_cubeHalfSpace (κ : Cardinal.{u}) (i : κ.out) :
    MeasurableSet (cubeHalfSpace κ i) := by
  exact measurableSet_Iic.preimage (by fun_prop)

@[simp]
theorem cubeMeasure_cubeHalfSpace (κ : Cardinal.{u}) (i : κ.out) :
    cubeMeasure κ (cubeHalfSpace κ i) = (2 : ℝ≥0∞)⁻¹ := by
  unfold cubeHalfSpace
  rw [← Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.infinitePi_map_eval
      (fun _ : κ.out ↦ (volume : Measure unitInterval)) i]
  simp

/-- Distinct coordinate half-spaces have symmetric-difference measure exactly `1/2`. -/
theorem cubeMeasure_symmDiff_cubeHalfSpace (κ : Cardinal.{u})
    {i j : κ.out} (hij : i ≠ j) :
    cubeMeasure κ (cubeHalfSpace κ i ∆ cubeHalfSpace κ j) =
      (2 : ℝ≥0∞)⁻¹ := by
  have hcoord :
      iIndepFun (fun i (x : κ.out → unitInterval) ↦ x i) (cubeMeasure κ) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (by fun_prop)
  have hE_indep :
      IndepSet (cubeHalfSpace κ i) (cubeHalfSpace κ j) (cubeMeasure κ) := by
    apply (indepFun_iff_indepSet_preimage (μ := cubeMeasure κ)
      (by fun_prop) (by fun_prop)).1 (hcoord.indepFun hij)
      (Set.Iic ⟨1 / 2, by constructor <;> norm_num⟩)
      (Set.Iic ⟨1 / 2, by constructor <;> norm_num⟩)
      measurableSet_Iic measurableSet_Iic
  have hd1 :
      cubeMeasure κ (cubeHalfSpace κ i \ cubeHalfSpace κ j) =
        cubeMeasure κ (cubeHalfSpace κ i) -
          cubeMeasure κ (cubeHalfSpace κ i ∩ cubeHalfSpace κ j) := by
    rw [show cubeHalfSpace κ i \ cubeHalfSpace κ j =
      cubeHalfSpace κ i \ (cubeHalfSpace κ i ∩ cubeHalfSpace κ j) by ext; simp]
    exact MeasureTheory.measure_sdiff Set.inter_subset_left
      ((measurableSet_cubeHalfSpace κ i).inter
        (measurableSet_cubeHalfSpace κ j)).nullMeasurableSet
      (MeasureTheory.measure_ne_top (cubeMeasure κ) _)
  have hd2 :
      cubeMeasure κ (cubeHalfSpace κ j \ cubeHalfSpace κ i) =
        cubeMeasure κ (cubeHalfSpace κ j) -
          cubeMeasure κ (cubeHalfSpace κ i ∩ cubeHalfSpace κ j) := by
    rw [show cubeHalfSpace κ j \ cubeHalfSpace κ i =
      cubeHalfSpace κ j \ (cubeHalfSpace κ i ∩ cubeHalfSpace κ j) by ext; simp]
    exact MeasureTheory.measure_sdiff Set.inter_subset_right
      ((measurableSet_cubeHalfSpace κ i).inter
        (measurableSet_cubeHalfSpace κ j)).nullMeasurableSet
      (MeasureTheory.measure_ne_top (cubeMeasure κ) _)
  rw [MeasureTheory.measure_symmDiff_eq
    (measurableSet_cubeHalfSpace κ i).nullMeasurableSet
    (measurableSet_cubeHalfSpace κ j).nullMeasurableSet,
    hd1, hd2, hE_indep.measure_inter_eq_mul,
    cubeMeasure_cubeHalfSpace, cubeMeasure_cubeHalfSpace]
  have hinv : (2 : ℝ≥0∞)⁻¹ - 2⁻¹ * 2⁻¹ = 2⁻¹ * 2⁻¹ := by
    calc
      (2 : ℝ≥0∞)⁻¹ - 2⁻¹ * 2⁻¹ = 2⁻¹ * (1 - 2⁻¹) := by
        rw [ENNReal.mul_sub (by simp), mul_one]
      _ = 2⁻¹ * 2⁻¹ := by rw [ENNReal.one_sub_inv_two]
  rw [hinv, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-- A finite-coordinate cylinder is independent of the symmetric difference
of two coordinate half-spaces outside its support. -/
theorem indepSet_cylinder_symmDiff_cubeHalfSpace
    (κ : Cardinal.{u}) (s : Finset κ.out) {U : Set (s → unitInterval)}
    (hU : MeasurableSet U) {i j : κ.out}
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) :
    IndepSet (MeasureTheory.cylinder s U)
      (cubeHalfSpace κ i ∆ cubeHalfSpace κ j) (cubeMeasure κ) := by
  classical
  have hcoord :
      iIndepFun (fun i (x : κ.out → unitInterval) ↦ x i) (cubeMeasure κ) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (by fun_prop)
  let t : Finset κ.out := {i, j}
  have hst : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro k hks hkt
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hkt
    rcases hkt with rfl | rfl
    · exact hi hks
    · exact hj hks
  have hind := hcoord.indepFun_finset s t hst (fun _ ↦ by fun_prop)
  let ii : t := ⟨i, by simp [t]⟩
  let jj : t := ⟨j, by simp [t]⟩
  let H : Set unitInterval :=
    Set.Iic ⟨1 / 2, by constructor <;> norm_num⟩
  let W : Set (t → unitInterval) :=
    (Function.eval ii ⁻¹' H) ∆ (Function.eval jj ⁻¹' H)
  have hH : MeasurableSet H := measurableSet_Iic
  have hW : MeasurableSet W :=
    (hH.preimage (measurable_pi_apply ii)).symmDiff
      (hH.preimage (measurable_pi_apply jj))
  have hindSet :=
    (indepFun_iff_indepSet_preimage (μ := cubeMeasure κ)
      (by fun_prop) (by fun_prop)).1 hind U W hU hW
  convert hindSet using 1
  · rfl
  · ext x
    simp [W, H, cubeHalfSpace, ii, jj, t, Set.mem_symmDiff]

/-- `([0, 1]^κ, λ^κ)`: the measure algebra induced by the Lebesgue cube of cardinality `κ`. -/
def cubeMeasureAlgebra (κ : Cardinal.{u}) :
    MeasureAlgebra (InducedBooleanAlgebra (cubeMeasure κ)) :=
  ofMeasure (cubeMeasure κ)

/-- The total mass of the Lebesgue cube measure algebra is one. -/
@[simp]
theorem cubeMeasureAlgebra_top (κ : Cardinal.{u}) :
    cubeMeasureAlgebra κ ⊤ = 1 := by
  change (ofMeasure (cubeMeasure κ)) ⊤ = 1
  rw [ofMeasure_top]
  exact measure_univ

/-- A Lebesgue cube indexed by a nonzero cardinal has an atomless measure
algebra. -/
theorem cubeMeasureAlgebra_isAtomless
    (κ : Cardinal.{u}) (hκ : 0 < κ) :
    BooleanAlgebra.IsAtomless
      (InducedBooleanAlgebra (cubeMeasure κ)) := by
  apply InducedBooleanAlgebra.isAtomless_of_hasNoAtoms
  let : Nonempty κ.out := Cardinal.mk_ne_zero_iff.mp (by
    rw [Cardinal.mk_out]
    exact ne_of_gt hκ)
  let i : κ.out := Classical.choice inferInstance
  apply Measure.hasNoAtoms_of_map_eq (ν := (volume : Measure unitInterval))
    (f := Function.eval i)
  · fun_prop
  · exact Measure.infinitePi_map_eval
      (fun _ : κ.out ↦ (volume : Measure unitInterval)) i

/-- A Lebesgue cube indexed by a cardinal `κ ≤ ℵ₀` has a
separable measure algebra. -/
theorem cubeMeasureAlgebra_isSeparable
    (κ : Cardinal.{u}) (hκ : κ ≤ Cardinal.aleph0) :
    letI := (cubeMeasureAlgebra κ).toMetricSpace
    TopologicalSpace.SeparableSpace
      (InducedBooleanAlgebra (cubeMeasure κ)) := by
  let : Countable κ.out := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Cardinal.mk_out]
    exact hκ)
  let := MeasureTheory.isSeparable_of_sigmaFinite (cubeMeasure κ)
  exact InducedBooleanAlgebra.separableSpace_of_isSeparableMeasure (cubeMeasure κ)

/-- An infinite Lebesgue cube has a measure-dense family of measurable sets
whose cardinality is at most the cardinal indexing the cube. -/
theorem exists_measureDense_cubeMeasure_mk_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∃ C : Set (Set (κ.out → unitInterval)),
      (cubeMeasure κ).MeasureDense C ∧ Cardinal.mk C ≤ κ := by
  classical
  let ν (s : Finset κ.out) : Measure (s → unitInterval) :=
    Measure.pi (fun _ : s ↦ (volume : Measure unitInterval))
  have hν_sep (s : Finset κ.out) : MeasureTheory.IsSeparable (ν s) := by
    apply MeasureTheory.isSeparable_of_sigmaFinite
  have hν_dense (s : Finset κ.out) :
      ∃ A : Set (Set (s → unitInterval)), A.Countable ∧ (ν s).MeasureDense A := by
    let := hν_sep s
    exact MeasureTheory.exists_countable_measureDense (ν s)
  choose A hA_count hA_dense using hν_dense
  let J := Σ s : Finset κ.out, A s
  let rawCyl : J → Set (κ.out → unitInterval) := fun p ↦
    MeasureTheory.cylinder p.1 p.2
  let C : Set (Set (κ.out → unitInterval)) := Set.range rawCyl
  have hJ : Cardinal.mk J ≤ κ := by
    let : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp (by
      rw [Cardinal.mk_out]
      exact hκ)
    change Cardinal.mk (Σ s : Finset κ.out, A s) ≤ κ
    rw [Cardinal.mk_sigma]
    calc
      Cardinal.sum (fun s : Finset κ.out ↦ Cardinal.mk (A s)) ≤
          Cardinal.sum (fun _ : Finset κ.out ↦ Cardinal.aleph0) :=
        Cardinal.sum_le_sum _ _ fun s ↦ (hA_count s).le_aleph0
      _ = Cardinal.mk (Finset κ.out) * Cardinal.aleph0 := by
        rw [Cardinal.sum_const]
        simp
      _ = κ * Cardinal.aleph0 := by
        rw [Cardinal.mk_finset_of_infinite, Cardinal.mk_out]
      _ = κ := Cardinal.mul_eq_left hκ hκ Cardinal.aleph0_ne_zero
  have hC_dense : (cubeMeasure κ).MeasureDense C := by
    refine ⟨?_, ?_⟩
    · rintro S ⟨p, rfl⟩
      exact (hA_dense p.1).measurable p.2 p.2.property |>.cylinder
    · intro S hS _ r hr
      obtain ⟨T, hT_cyl, hTS⟩ :=
        (cubeMeasure_measureDense_measurableCylinders κ).approx S hS
          (MeasureTheory.measure_ne_top (cubeMeasure κ) S)
          (r / 2) (half_pos hr)
      obtain ⟨s, U, hU, rfl⟩ :=
        (MeasureTheory.mem_measurableCylinders T).mp hT_cyl
      obtain ⟨V, hVA, hUV⟩ := (hA_dense s).approx U hU
        (MeasureTheory.measure_ne_top (ν s) U) (r / 2) (half_pos hr)
      have hV : MeasurableSet V := (hA_dense s).measurable V hVA
      have hUVcyl :
          cubeMeasure κ (MeasureTheory.cylinder s U ∆ MeasureTheory.cylinder s V) <
            ENNReal.ofReal (r / 2) := by
        calc
          cubeMeasure κ
              (MeasureTheory.cylinder s U ∆ MeasureTheory.cylinder s V) =
              cubeMeasure κ (MeasureTheory.cylinder s (U ∆ V)) := by
            congr 1
          _ = ν s (U ∆ V) := by
            exact Measure.infinitePi_cylinder
              (fun _ : κ.out ↦ (volume : Measure unitInterval)) (hU.symmDiff hV)
          _ < ENNReal.ofReal (r / 2) := hUV
      let p : J := ⟨s, ⟨V, hVA⟩⟩
      refine ⟨rawCyl p, ⟨p, rfl⟩, ?_⟩
      dsimp only [rawCyl, p]
      calc
        cubeMeasure κ (S ∆ MeasureTheory.cylinder s V) ≤
            cubeMeasure κ (S ∆ MeasureTheory.cylinder s U) +
              cubeMeasure κ
                (MeasureTheory.cylinder s U ∆ MeasureTheory.cylinder s V) :=
          MeasureTheory.measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
          ENNReal.add_lt_add hTS hUVcyl
        _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le, add_halves]
  exact ⟨C, hC_dense, Cardinal.mk_range_le.trans hJ⟩

/-- For an infinite cardinal `κ`, the density character of the Lebesgue
cube measure algebra is at most `κ`. -/
private theorem cubeMeasureAlgebra_densityCharacter_le_of_aleph0_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    (cubeMeasureAlgebra κ).densityCharacter ≤ κ := by
  classical
  obtain ⟨C, hC_dense, hC_card⟩ :=
    exists_measureDense_cubeMeasure_mk_le κ hκ
  let D : Set (InducedBooleanAlgebra (cubeMeasure κ)) := Set.range fun S : C ↦
    InducedBooleanAlgebra.mk (cubeMeasure κ)
      ⟨S, hC_dense.measurable S S.property⟩
  let := (ofMeasure (cubeMeasure κ)).toMetricSpace
  have hD : Dense D := by
    simpa [D] using
      InducedBooleanAlgebra.dense_range_mk_of_measureDense (cubeMeasure κ) hC_dense
  unfold densityCharacter
  exact (TopologicalSpace.densityCharacter_le_mk_of_dense hD).trans
    (Cardinal.mk_range_le.trans hC_card)

/-- For every cardinal `κ`, the density character of the Lebesgue cube indexed
by `κ` is at most `max ℵ₀ κ`. -/
theorem cubeMeasureAlgebra_densityCharacter_le (κ : Cardinal.{u}) :
    (cubeMeasureAlgebra κ).densityCharacter ≤ max Cardinal.aleph0 κ := by
  rcases le_total Cardinal.aleph0 κ with hκ | hκ
  · exact (cubeMeasureAlgebra_densityCharacter_le_of_aleph0_le κ hκ).trans
      (le_max_right _ _)
  · let := (cubeMeasureAlgebra κ).toMetricSpace
    let : TopologicalSpace.SeparableSpace
        (InducedBooleanAlgebra (cubeMeasure κ)) :=
      cubeMeasureAlgebra_isSeparable κ hκ
    exact (TopologicalSpace.densityCharacter_le_aleph0
      (InducedBooleanAlgebra (cubeMeasure κ))).trans (le_max_left _ _)

/-- If `S ⊆ [0, 1]^κ` is measurable and `λ^κ(S) > 0`, then there exists a finite set `s ⊆ κ`
such that for all `i, j ∉ s, i ≠ j,` `λ^κ(S ∩ (E_i ∆ E_j)) ≥ λ^κ(S)/4`, where
`E_k = {0 ≤ x_k ≤ 1/2}`. -/
theorem exists_finset_cubeHalfSpace_inter_symmDiff_ge
    (κ : Cardinal.{u}) {S : Set (κ.out → unitInterval)}
    (hS : MeasurableSet S) (hS_ne_zero : cubeMeasure κ S ≠ 0) :
    ∃ s : Finset κ.out,
      ∀ {i j : κ.out}, i ∉ s → j ∉ s → i ≠ j →
        (cubeMeasure κ).real S / 4 ≤
          (cubeMeasure κ).real
            (S ∩ (cubeHalfSpace κ i ∆ cubeHalfSpace κ j)) := by
  classical
  let μ := cubeMeasure κ
  let m := μ.real S
  have hm : 0 < m :=
    ENNReal.toReal_pos hS_ne_zero (MeasureTheory.measure_ne_top μ _)
  obtain ⟨T, hT_cyl, hTS⟩ :=
    (cubeMeasure_measureDense_measurableCylinders κ).approx S hS
      (MeasureTheory.measure_ne_top μ _) (m / 16)
      (div_pos hm (by norm_num : (0 : ℝ) < 16))
  obtain ⟨s, U, hU, rfl⟩ :=
    (MeasureTheory.mem_measurableCylinders T).mp hT_cyl
  refine ⟨s, ?_⟩
  intro i j hi hj hij
  let E := cubeHalfSpace κ
  have hE_meas (k : κ.out) : MeasurableSet (E k) :=
    measurableSet_cubeHalfSpace κ k
  have hE_symmDiff : μ (E i ∆ E j) = (2 : ℝ≥0∞)⁻¹ :=
    cubeMeasure_symmDiff_cubeHalfSpace κ hij
  have hU_indep :
      IndepSet (MeasureTheory.cylinder s U) (E i ∆ E j) μ :=
    indepSet_cylinder_symmDiff_cubeHalfSpace κ s hU hi hj hij
  have hTSreal :
      μ.real (S ∆ MeasureTheory.cylinder s U) < m / 16 := by
    have hreal :=
      (ENNReal.toReal_lt_toReal (ne_top_of_lt hTS) ENNReal.ofReal_ne_top).2 hTS
    rw [ENNReal.toReal_ofReal (div_nonneg hm.le (by norm_num))] at hreal
    exact hreal
  have habsU :
      |μ.real (MeasureTheory.cylinder s U) - m| < m / 16 := by
    have habs := MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
      hU.cylinder.nullMeasurableSet hS.nullMeasurableSet
    change |μ.real (MeasureTheory.cylinder s U) - m| ≤
      μ.real (MeasureTheory.cylinder s U ∆ S) at habs
    apply habs.trans_lt
    rw [symmDiff_comm]
    exact hTSreal
  have hUlower :
      m - m / 16 < μ.real (MeasureTheory.cylinder s U) := by
    linarith [neg_le_abs (μ.real (MeasureTheory.cylinder s U) - m)]
  have hF_meas : MeasurableSet (E i ∆ E j) :=
    (hE_meas i).symmDiff (hE_meas j)
  have hUF :
      μ.real (MeasureTheory.cylinder s U ∩ (E i ∆ E j)) =
        μ.real (MeasureTheory.cylinder s U) / 2 := by
    rw [Measure.real, hU_indep.measure_inter_eq_mul,
      hE_symmDiff, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
    change (μ (MeasureTheory.cylinder s U)).toReal * (1 / 2 : ℝ) =
      (μ (MeasureTheory.cylinder s U)).toReal / 2
    ring
  have hInter_subset :
      ((S ∩ (E i ∆ E j)) ∆
        (MeasureTheory.cylinder s U ∩ (E i ∆ E j))) ⊆
          S ∆ MeasureTheory.cylinder s U := by
    rw [← Set.inter_symmDiff_distrib_right]
    exact Set.inter_subset_left
  have hInterErr :
      μ.real ((S ∩ (E i ∆ E j)) ∆
        (MeasureTheory.cylinder s U ∩ (E i ∆ E j))) < m / 16 :=
    (MeasureTheory.measureReal_mono (μ := μ) hInter_subset).trans_lt hTSreal
  have habsInter :
      |μ.real (S ∩ (E i ∆ E j)) -
          μ.real (MeasureTheory.cylinder s U ∩ (E i ∆ E j))| < m / 16 := by
    exact (MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
      (hS.inter hF_meas).nullMeasurableSet
      (hU.cylinder.inter hF_meas).nullMeasurableSet).trans_lt hInterErr
  have hSlower :
      μ.real (MeasureTheory.cylinder s U ∩ (E i ∆ E j)) - m / 16 <
        μ.real (S ∩ (E i ∆ E j)) := by
    linarith [neg_le_abs
      (μ.real (S ∩ (E i ∆ E j)) -
        μ.real (MeasureTheory.cylinder s U ∩ (E i ∆ E j)))]
  change m / 4 ≤ μ.real (S ∩ (E i ∆ E j))
  linarith

/-- For an infinite cardinal `κ`, every nonzero principal ideal of the Lebesgue cube measure
algebra has Maharam type `κ`. -/
private theorem cubeMeasureAlgebra_maharamTypeBelow_of_aleph0_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {a : InducedBooleanAlgebra (cubeMeasure κ)} (ha : a ≠ ⊥) :
    (cubeMeasureAlgebra κ).maharamTypeBelow a = κ := by
  apply le_antisymm
  · exact (maharamTypeBelow_le_densityCharacter (cubeMeasureAlgebra κ) a).trans
      (cubeMeasureAlgebra_densityCharacter_le_of_aleph0_le κ hκ)
  · classical
    let μ := cubeMeasure κ
    obtain ⟨S, rfl⟩ := InducedBooleanAlgebra.mk_surjective μ a
    have hS_ne_zero : μ (S : Set (κ.out → unitInterval)) ≠ 0 := by
      intro hS
      apply ha
      apply ((ofMeasure μ).measure_eq_zero_iff _).mp
      simpa [μ] using hS
    have hm : 0 < μ.real (S : Set (κ.out → unitInterval)) :=
      ENNReal.toReal_pos hS_ne_zero (MeasureTheory.measure_ne_top μ _)
    obtain ⟨s, hs⟩ := exists_finset_cubeHalfSpace_inter_symmDiff_ge
      κ S.property hS_ne_zero
    let I := {i : κ.out // i ∉ s}
    let : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp (by
      rw [Cardinal.mk_out]
      exact hκ)
    have hI : Cardinal.mk I = κ := by
      change Cardinal.mk {i : κ.out // i ∈ (↑s : Set κ.out)ᶜ} = κ
      rw [Cardinal.mk_compl_finset_of_infinite, Cardinal.mk_out]
    let E := cubeHalfSpace κ
    have hE_meas (i : κ.out) : MeasurableSet (E i) :=
      measurableSet_cubeHalfSpace κ i
    let b (i : I) : MeasuredSets μ :=
      ⟨(S : Set (κ.out → unitInterval)) ∩ E i,
        S.property.inter (hE_meas i)⟩
    let x (i : I) : Set.Iic (InducedBooleanAlgebra.mk μ S) :=
      ⟨InducedBooleanAlgebra.mk μ (b i),
        InducedBooleanAlgebra.mk_le_mk_of_subset μ Set.inter_subset_left⟩
    have hbound : Cardinal.mk I ≤
        (cubeMeasureAlgebra κ).maharamTypeBelow (InducedBooleanAlgebra.mk μ S) := by
      unfold maharamTypeBelow densityCharacter
      let := ((cubeMeasureAlgebra κ).restrict
        (InducedBooleanAlgebra.mk μ S)).toMetricSpace
      apply TopologicalSpace.mk_le_densityCharacter_of_pairwise_le_dist x
        (div_pos hm (by norm_num : (0 : ℝ) < 4))
      intro i j hij
      have hijv : (i : κ.out) ≠ j := by
        intro hij'
        exact hij (Subtype.ext hij')
      rw [dist_eq_measure_symmDiff]
      change μ.real (S : Set (κ.out → unitInterval)) / 4 ≤ ((cubeMeasureAlgebra κ)
        (((symmDiff (x i) (x j) : Set.Iic (InducedBooleanAlgebra.mk μ S)) :
          InducedBooleanAlgebra μ))).toReal
      rw [Set.Iic.coe_symmDiff]
      change μ.real (S : Set (κ.out → unitInterval)) / 4 ≤ ((cubeMeasureAlgebra κ)
        (InducedBooleanAlgebra.mk μ (b i) ∆
          InducedBooleanAlgebra.mk μ (b j))).toReal
      rw [symmDiff_def, ← InducedBooleanAlgebra.mk_sdiff,
        ← InducedBooleanAlgebra.mk_sdiff, ← InducedBooleanAlgebra.mk_sup,
        ← symmDiff_def]
      change μ.real (S : Set (κ.out → unitInterval)) / 4 ≤ μ.real
        (((b i ∆ b j : MeasuredSets μ) : Set (κ.out → unitInterval)))
      change μ.real (S : Set (κ.out → unitInterval)) / 4 ≤ μ.real
        (((S : Set (κ.out → unitInterval)) ∩ E i) ∆
          ((S : Set (κ.out → unitInterval)) ∩ E j))
      rw [← Set.inter_symmDiff_distrib_left]
      exact hs i.property j.property hijv
    exact hI.symm.le.trans hbound

/-- If `κ > 0`, the Maharam type of every `a ≠ ⊥` in the Lebesgue cube
indexed by `κ` is `max ℵ₀ κ`. -/
theorem cubeMeasureAlgebra_maharamTypeBelow
    (κ : Cardinal.{u}) (hκ : 0 < κ)
    {a : InducedBooleanAlgebra (cubeMeasure κ)} (ha : a ≠ ⊥) :
    (cubeMeasureAlgebra κ).maharamTypeBelow a = max Cardinal.aleph0 κ := by
  rcases le_total Cardinal.aleph0 κ with hκ_inf | hκ_count
  · simpa [max_eq_right hκ_inf] using
      cubeMeasureAlgebra_maharamTypeBelow_of_aleph0_le κ hκ_inf ha
  · have hden : (cubeMeasureAlgebra κ).densityCharacter ≤ Cardinal.aleph0 := by
      simpa [max_eq_left hκ_count] using cubeMeasureAlgebra_densityCharacter_le κ
    simpa [max_eq_left hκ_count] using
      (cubeMeasureAlgebra κ).maharamTypeBelow_eq_aleph0_of_isAtomless_of_densityCharacter_le
        (cubeMeasureAlgebra_isAtomless κ hκ) hden ha

/-- If `κ > 0`, the Maharam type of the Lebesgue cube indexed by `κ` is
`max ℵ₀ κ`. -/
theorem cubeMeasureAlgebra_maharamType
    (κ : Cardinal.{u}) (hκ : 0 < κ) :
    (cubeMeasureAlgebra κ).maharamType = max Cardinal.aleph0 κ := by
  rw [← (cubeMeasureAlgebra κ).maharamTypeBelow_top]
  apply cubeMeasureAlgebra_maharamTypeBelow κ hκ
  intro h
  have := congrArg (cubeMeasureAlgebra κ) h
  simp at this

/-- If `κ > 0`, the density character of the Lebesgue cube indexed by `κ`
is `max ℵ₀ κ`. -/
theorem cubeMeasureAlgebra_densityCharacter
    (κ : Cardinal.{u}) (hκ : 0 < κ) :
    (cubeMeasureAlgebra κ).densityCharacter = max Cardinal.aleph0 κ := by
  exact cubeMeasureAlgebra_maharamType κ hκ

/-- Every Lebesgue cube indexed by a nonzero cardinal is homogeneous. -/
theorem cubeMeasureAlgebra_isHomogeneous
    (κ : Cardinal.{u}) (hκ : 0 < κ) :
    (cubeMeasureAlgebra κ).IsHomogeneous := by
  intro a ha
  rw [cubeMeasureAlgebra_maharamTypeBelow κ hκ ha,
    cubeMeasureAlgebra_maharamType κ hκ]

/-- The Boolean algebra of the one-dimensional Lebesgue cube. -/
abbrev LebesgueBooleanAlgebra :=
  InducedBooleanAlgebra (cubeMeasure (1 : Cardinal))

/-- The measure algebra of the one-dimensional Lebesgue cube. -/
noncomputable abbrev LebesgueMeasureAlgebra :
    MeasureAlgebra LebesgueBooleanAlgebra :=
  cubeMeasureAlgebra 1

/-- The one-dimensional Lebesgue cube has an atomless measure algebra. -/
theorem isAtomless_lebesgueBooleanAlgebra :
    BooleanAlgebra.IsAtomless LebesgueBooleanAlgebra := by
  exact cubeMeasureAlgebra_isAtomless 1 (by simp)

/-- The one-dimensional Lebesgue cube has total mass one. -/
theorem lebesgueMeasureAlgebra_top :
    LebesgueMeasureAlgebra ⊤ = 1 := by
  exact cubeMeasureAlgebra_top 1

end MeasureAlgebra
