import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Zorn
import BanLat.Preliminaries.Regularity
import BanLat.Preliminaries.SignedMeasure

/-!
# Atomless measures are continuous

This file states the standard continuity property of atomless measures: inside
any measurable set `s`, one can find a measurable subset of any prescribed
measure between `0` and `μ s`.

Mathlib's typeclass `MeasureTheory.NoAtoms μ` means that every singleton has
measure zero. That is not the measure-theoretic notion used here: an atom is a
positive measurable set with no measurable subset of strictly intermediate
measure. We therefore introduce `Measure.HasNoAtoms` for the measure-theoretic
notion.
-/

open scoped ENNReal

namespace MeasureTheory

open Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Measure

/-- An atom of a measure is a measurable set of positive measure whose
measurable subsets have either zero measure or the same measure as the set. -/
def IsAtom (μ : Measure α) (s : Set α) : Prop :=
  MeasurableSet s ∧ 0 < μ s ∧
    ∀ ⦃t : Set α⦄, MeasurableSet t → t ⊆ s → μ t = 0 ∨ μ t = μ s

/-- A measure has no atoms in the measure-theoretic sense when it has no
measurable atom. -/
def HasNoAtoms (μ : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, MeasurableSet s → 0 < μ s → ¬ μ.IsAtom s

/-- A measure is continuous when every measurable set contains measurable
subsets of all smaller prescribed measures. -/
def IsContinuous (μ : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, MeasurableSet s →
    ∀ ⦃r : ℝ≥0∞⦄, r ≤ μ s →
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ μ t = r

/-- On a compact Hausdorff Borel space, a finite regular measure with no
singleton atoms has no atoms in the measure-theoretic sense. -/
theorem hasNoAtoms_of_noAtoms_of_regular {K : Type*}
    [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ : Measure K} [IsFiniteMeasure μ] [NoAtoms μ] (hμ : μ.Regular) :
    μ.HasNoAtoms := by
  classical
  haveI : μ.Regular := hμ
  intro s hs hμs hs_atom
  obtain ⟨C, hCs, hC_compact, hC_pos⟩ :=
    MeasurableSet.exists_lt_isCompact_of_ne_top (μ := μ) hs (measure_ne_top μ s) hμs
  have hC_meas : MeasurableSet C := hC_compact.isClosed.measurableSet
  have hC_eq : μ C = μ s := by
    rcases hs_atom.2.2 hC_meas hCs with hC_zero | hC_full
    · exact (hC_pos.ne' hC_zero).elim
    · exact hC_full
  choose U hU_mem hU_open hU_lt using fun x : C => by
    have hx_lt : μ ({(x : K)} : Set K) < μ C := by
      simpa using hC_pos
    exact Set.exists_isOpen_lt_of_lt (μ := μ) ({(x : K)} : Set K) (μ C) hx_lt
  let V : K → Set K := fun x => if hx : x ∈ C then U ⟨x, hx⟩ else ∅
  have hV_open : ∀ x, IsOpen (V x) := by
    intro x
    by_cases hx : x ∈ C
    · simp [V, hx, hU_open ⟨x, hx⟩]
    · simp [V, hx]
  have hV_cover : C ⊆ ⋃ x, V x := by
    intro x hx
    refine mem_iUnion.2 ⟨x, ?_⟩
    simpa [V, hx] using hU_mem ⟨x, hx⟩ rfl
  obtain ⟨F, hF_cover⟩ :=
    hC_compact.elim_finite_subcover V hV_open hV_cover
  have hC_eq_union : C = ⋃ x ∈ F, C ∩ V x := by
    ext y
    constructor
    · intro hy
      rcases mem_iUnion.1 (hF_cover hy) with ⟨x, hx⟩
      rcases mem_iUnion.1 hx with ⟨hxF, hxy⟩
      exact mem_iUnion.2 ⟨x, mem_iUnion.2 ⟨hxF, ⟨hy, hxy⟩⟩⟩
    · intro hy
      rcases mem_iUnion.1 hy with ⟨x, hx⟩
      rcases mem_iUnion.1 hx with ⟨_, hyCU⟩
      exact hyCU.1
  obtain ⟨x, hxF, hx_pos⟩ : ∃ x ∈ F, 0 < μ (C ∩ V x) := by
    by_contra! hzero
    have hμ_union : μ (⋃ x ∈ F, C ∩ V x) = 0 := by
      change μ (⋃ x ∈ (F : Set K), C ∩ V x) = 0
      rw [measure_biUnion_null_iff F.countable_toSet]
      intro x hxF
      exact nonpos_iff_eq_zero.1 (hzero x hxF)
    exact hC_pos.ne' (hC_eq_union.symm ▸ hμ_union)
  have hxC : x ∈ C := by
    by_contra hxC
    have : μ (C ∩ V x) = 0 := by simp [V, hxC]
    exact hx_pos.ne' this
  have hCU_meas : MeasurableSet (C ∩ V x) :=
    hC_meas.inter (hV_open x).measurableSet
  have hCU_subset : C ∩ V x ⊆ s := inter_subset_left.trans hCs
  have hCU_lt : μ (C ∩ V x) < μ s := by
    calc
      μ (C ∩ V x) ≤ μ (V x) := measure_mono inter_subset_right
      _ = μ (U ⟨x, hxC⟩) := by simp [V, hxC]
      _ < μ C := hU_lt ⟨x, hxC⟩
      _ = μ s := hC_eq
  rcases hs_atom.2.2 hCU_meas hCU_subset with hzero | hfull
  · exact hx_pos.ne' hzero
  · exact hCU_lt.ne hfull

end Measure

namespace SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- For a regular signed measure on a compact Hausdorff Borel space,
singleton-null total variation implies measure-theoretic atomlessness of the
total variation. This is the form needed for regular signed measures in
`M(K)`. -/
theorem IsRegular.totalVariation_hasNoAtoms_of_noAtoms {s : SignedMeasure K}
    (hs : s.IsRegular) [NoAtoms s.totalVariation] :
    s.totalVariation.HasNoAtoms :=
  Measure.hasNoAtoms_of_noAtoms_of_regular hs

end SignedMeasure

namespace Measure.HasNoAtoms

/-- If an atomless measure gives positive mass to a measurable set `s`, then
`s` contains a measurable subset whose measure is strictly between `0` and
`μ s`.

This is the direct negation of being an atom, packaged in the form used by the
splitting argument below. -/
private theorem exists_measurable_subset_measure_lt_self
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s) (hs_pos : 0 < μ s) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s := by
  classical
  by_contra h
  push_neg at h
  exact hμ hs hs_pos ⟨hs, hs_pos, fun ht htm hts => by
    by_cases ht_zero : μ ht = 0
    · exact Or.inl ht_zero
    · refine Or.inr ?_
      have ht_pos : 0 < μ ht := pos_iff_ne_zero.2 ht_zero
      exact le_antisymm (measure_mono hts) (h ht htm hts ht_pos)⟩

/-- Small-piece lemma for an atomless measure.

If `s` has positive measure, then for every positive `ε` it contains a
measurable subset of finite positive measure. -/
private theorem exists_pos_finite_measurable_subset
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s) (hs_pos : 0 < μ s) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t ≠ ∞ := by
  classical
  by_cases hs_top : μ s = ∞
  · obtain ⟨t, ht_meas, hts, ht_pos, ht_lt⟩ :=
      exists_measurable_subset_measure_lt_self hμ hs hs_pos
    refine ⟨t, ht_meas, hts, ht_pos, ?_⟩
    exact lt_top_iff_ne_top.mp (by simpa [hs_top] using ht_lt)
  · exact ⟨s, hs, Subset.rfl, hs_pos, hs_top⟩

/-- One halving step in a finite positive atomless set.

Starting from a measurable set of finite positive measure, choose a measurable
positive subset whose measure is at most half the original measure. -/
private theorem exists_pos_measurable_subset_measure_le_half
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s)
    (hs_pos : 0 < μ s) (hs_ne_top : μ s ≠ ∞) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t ≤ μ s / 2 := by
  obtain ⟨u, hu_meas, hus, hu_pos, hu_lt⟩ :=
    exists_measurable_subset_measure_lt_self hμ hs hs_pos
  by_cases hu_le : μ u ≤ μ s / 2
  · exact ⟨u, hu_meas, hus, hu_pos, hu_le⟩
  · have hu_ne_top : μ u ≠ ∞ := ne_top_of_le_ne_top hs_ne_top (measure_mono hus)
    refine ⟨s \ u, hs.diff hu_meas, diff_subset, ?_, ?_⟩
    · rw [measure_diff hus hu_meas.nullMeasurableSet hu_ne_top]
      exact tsub_pos_iff_lt.2 hu_lt
    · rw [measure_diff hus hu_meas.nullMeasurableSet hu_ne_top]
      have hhalf_lt : μ s / 2 < μ u := lt_of_not_ge hu_le
      rw [tsub_le_iff_left]
      calc
        μ s = μ s / 2 + μ s / 2 := (ENNReal.add_halves (μ s)).symm
        _ ≤ μ s / 2 + μ u := add_le_add_right hhalf_lt.le _
        _ = μ u + μ s / 2 := add_comm _ _

/-- Iterating the previous lemma gives a nested sequence of positive measurable
sets whose measures are at least halved at each step. -/
private theorem exists_halving_sequence
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s)
    (hs_pos : 0 < μ s) (hs_ne_top : μ s ≠ ∞) :
    ∃ u : ℕ → Set α,
      u 0 = s ∧
        (∀ n, MeasurableSet (u n)) ∧
        (∀ n, u n ⊆ s) ∧
        (∀ n, 0 < μ (u n)) ∧
        (∀ n, μ (u (n + 1)) ≤ μ (u n) / 2) := by
  classical
  let P : Type _ := {t : Set α // MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t ≠ ∞}
  have hstep : ∀ p : P, ∃ q : P, (q : Set α) ⊆ (p : Set α) ∧
      μ (q : Set α) ≤ μ (p : Set α) / 2 := by
    intro p
    obtain ⟨q, hq_meas, hqp, hq_pos, hq_le⟩ :=
      exists_pos_measurable_subset_measure_le_half
        (μ := μ) hμ p.2.1 p.2.2.2.1 p.2.2.2.2
    have hq_ne_top : μ q ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.div_ne_top p.2.2.2.2 two_ne_zero) hq_le
    refine ⟨⟨q, hq_meas, hqp.trans p.2.2.1, hq_pos, hq_ne_top⟩, hqp, hq_le⟩
  choose step hstep_spec using hstep
  let seq : ℕ → P := Nat.rec ⟨s, hs, Subset.rfl, hs_pos, hs_ne_top⟩ fun _ p => step p
  refine ⟨fun n => (seq n).1, ?_, ?_, ?_, ?_, ?_⟩
  · change (seq 0).1 = s
    rfl
  · exact fun n => (seq n).2.1
  · exact fun n => (seq n).2.2.1
  · exact fun n => (seq n).2.2.2.1
  · intro n
    simpa [seq] using (hstep_spec (seq n)).2

/-- A positive finite halving sequence eventually has measure at most any
positive `ε`. -/
private theorem halving_sequence_eventually_le
    {u : ℕ → Set α} (_hu_pos : ∀ n, 0 < μ (u n)) (hu0_ne_top : μ (u 0) ≠ ∞)
    (hu_halves : ∀ n, μ (u (n + 1)) ≤ μ (u n) / 2)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, μ (u n) ≤ ε := by
  classical
  have hbound : ∀ n, μ (u n) ≤ μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          μ (u (n + 1)) ≤ μ (u n) / 2 := hu_halves n
          _ ≤ (μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ n) / 2 := by
            gcongr
          _ = μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
            simp [div_eq_mul_inv, pow_succ, mul_assoc]
  by_contra h
  push_neg at h
  have hle : ∀ n : ℕ,
      ε ≤ (μ (u 0)).toNNReal * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    calc
      ε ≤ μ (u n) := (h n).le
      _ ≤ μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ n := hbound n
      _ = (μ (u 0)).toNNReal * (2⁻¹ : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_toNNReal hu0_ne_top]
  have hzero : ε = 0 :=
    ENNReal.eq_zero_of_le_mul_pow (x := ε) (r := (2⁻¹ : ℝ≥0∞))
      (ε := (μ (u 0)).toNNReal) ENNReal.one_half_lt_one hle
  exact hε.ne' hzero

/-- Small-piece lemma for an atomless measure.

If `s` has positive measure, then for every positive `ε` it contains a
measurable subset of positive measure at most `ε`. -/
private theorem exists_pos_measurable_subset_measure_le
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s) (hs_pos : 0 < μ s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t ≤ ε := by
  obtain ⟨s₀, hs₀, hs₀s, hs₀_pos, hs₀_ne_top⟩ :=
    exists_pos_finite_measurable_subset hμ hs hs_pos
  obtain ⟨u, hu_zero, hu_meas, hu_subset, hu_pos, hu_halves⟩ :=
    exists_halving_sequence hμ hs₀ hs₀_pos hs₀_ne_top
  have hu0_ne_top : μ (u 0) ≠ ∞ := by
    simpa [hu_zero] using hs₀_ne_top
  obtain ⟨n, hn⟩ :=
    halving_sequence_eventually_le (μ := μ) hu_pos hu0_ne_top hu_halves hε
  exact ⟨u n, hu_meas n, (hu_subset n).trans hs₀s, hu_pos n, hn⟩

/-- The admissible measurable subsets used in the maximality argument.

An admissible set is a measurable subset of `s` whose measure is at most the
target value `r`. -/
private def admissibleSubsets (μ : Measure α) (s : Set α) (r : ℝ≥0∞) : Set (Set α) :=
  {t | MeasurableSet t ∧ t ⊆ s ∧ μ t ≤ r}

/-- Almost-everywhere inclusion of sets with respect to a measure. -/
private def aeSubset (μ : Measure α) (u v : Set α) : Prop :=
  μ (u \ v) = 0

private theorem aeSubset_refl (μ : Measure α) (s : Set α) :
    aeSubset μ s s := by
  simp [aeSubset]

private theorem aeSubset_trans {u v w : Set α}
    (huv : aeSubset μ u v) (hvw : aeSubset μ v w) :
    aeSubset μ u w := by
  have hsubset : u \ w ⊆ (u \ v) ∪ (v \ w) := by
    intro x hx
    by_cases hxv : x ∈ v
    · exact Or.inr ⟨hxv, hx.2⟩
    · exact Or.inl ⟨hx.1, hxv⟩
  exact nonpos_iff_eq_zero.1 <|
    (measure_mono hsubset).trans <| by
      rw [measure_union_null huv hvw]

private theorem aeSubset_union {u v w : Set α}
    (huw : aeSubset μ u w) (hvw : aeSubset μ v w) :
    aeSubset μ (u ∪ v) w := by
  have hsubset : (u ∪ v) \ w ⊆ (u \ w) ∪ (v \ w) := by
    intro x hx
    rcases hx with ⟨hxuv, hxw⟩
    rcases hxuv with hxu | hxv
    · exact Or.inl ⟨hxu, hxw⟩
    · exact Or.inr ⟨hxv, hxw⟩
  exact nonpos_iff_eq_zero.1 <|
    (measure_mono hsubset).trans <| by
      rw [measure_union_null huw hvw]

private theorem measure_le_of_aeSubset {u v : Set α} (huv : aeSubset μ u v) :
    μ u ≤ μ v := by
  have hsubset : u ⊆ v ∪ (u \ v) := by
    intro x hx
    by_cases hxv : x ∈ v
    · exact Or.inl hxv
    · exact Or.inr ⟨hx, hxv⟩
  calc
    μ u ≤ μ (v ∪ (u \ v)) := measure_mono hsubset
    _ ≤ μ v + μ (u \ v) := measure_union_le _ _
    _ = μ v := by rw [huv, add_zero]

private theorem aeSubset_of_le_of_ae_mono {u : ℕ → Set α}
    (hu_ae_mono : ∀ n, aeSubset μ (u n) (u (n + 1))) :
    ∀ ⦃m n : ℕ⦄, m ≤ n → aeSubset μ (u m) (u n) := by
  intro m n hmn
  induction hmn with
  | refl => exact aeSubset_refl μ (u m)
  | @step n hmn ihn =>
      exact aeSubset_trans ihn (hu_ae_mono n)

private theorem accumulate_aeSubset_of_ae_mono {u : ℕ → Set α}
    (hu_ae_mono : ∀ n, aeSubset μ (u n) (u (n + 1))) :
    ∀ n, aeSubset μ (accumulate u n) (u n) := by
  intro n
  induction n with
  | zero =>
      rw [accumulate_zero_nat]
      exact aeSubset_refl μ (u 0)
  | succ n ih =>
      rw [accumulate_succ]
      exact aeSubset_union
        (aeSubset_trans ih (hu_ae_mono n))
        (aeSubset_refl μ (u (n + 1)))

private theorem admissible_empty {s : Set α} {r : ℝ≥0∞} :
    ∅ ∈ admissibleSubsets μ s r := by
  simp [admissibleSubsets]

/-- The measures of admissible sets are bounded above by the target value. -/
private theorem admissible_measures_bddAbove {s : Set α} {r : ℝ≥0∞}
    {c : Set (Set α)} (hc_adm : c ⊆ admissibleSubsets μ s r) :
    BddAbove ((fun t : Set α => μ t) '' c) := by
  refine ⟨r, ?_⟩
  rintro _ ⟨t, htc, rfl⟩
  exact (hc_adm htc).2.2

/-- A countable cofinal, almost-increasing sequence can be chosen inside a
nonempty chain of admissible sets. -/
private theorem exists_ae_monotone_chain_approximating_sequence
    {s : Set α} {r : ℝ≥0∞} {c : Set (Set α)}
    (hc_ne : c.Nonempty) (hc_chain : IsChain (aeSubset μ) c)
    (hc_adm : c ⊆ admissibleSubsets μ s r) :
    ∃ u : ℕ → Set α,
      (∀ n, u n ∈ c) ∧
        (∀ n, aeSubset μ (u n) (u (n + 1))) ∧
        Filter.Tendsto (fun n => μ (u n)) Filter.atTop
          (nhds (sSup ((fun t : Set α => μ t) '' c))) := by
  -- Use `exists_seq_tendsto_sSup` on the bounded nonempty set of measures,
  -- choose representatives in the chain, then replace finite initial segments
  -- by chain-maximal representatives so that the sequence is `aeSubset`
  -- increasing.
  have hbdd : BddAbove ((fun t : Set α => μ t) '' c) :=
    admissible_measures_bddAbove (μ := μ) hc_adm
  have hne : (((fun t : Set α => μ t) '' c) : Set ℝ≥0∞).Nonempty :=
    hc_ne.image _
  obtain ⟨v, _, hv_tendsto, hv_mem⟩ := exists_seq_tendsto_sSup hne hbdd
  have hv_pre : ∀ n, ∃ a : Set α, a ∈ c ∧ μ a = v n := by
    intro n
    rcases hv_mem n with ⟨a, hac, ha⟩
    exact ⟨a, hac, ha⟩
  choose a ha_mem ha_mu using hv_pre
  let P : Type _ := {t : Set α // t ∈ c}
  let aP : ℕ → P := fun n => ⟨a n, ha_mem n⟩
  have hmax : ∀ p q : P, ∃ m : P,
      aeSubset μ p.1 m.1 ∧ aeSubset μ q.1 m.1 := by
    intro p q
    by_cases hpq_eq : p.1 = q.1
    · refine ⟨q, ?_, aeSubset_refl μ q.1⟩
      simpa [hpq_eq] using aeSubset_refl μ q.1
    · rcases hc_chain p.2 q.2 hpq_eq with hpq | hqp
      · exact ⟨q, hpq, aeSubset_refl μ q.1⟩
      · exact ⟨p, aeSubset_refl μ p.1, hqp⟩
  choose max hmax_spec using hmax
  let bP : ℕ → P := Nat.rec (aP 0) fun n p => max p (aP (n + 1))
  have hb_ae_mono : ∀ n, aeSubset μ (bP n).1 (bP (n + 1)).1 := by
    intro n
    change aeSubset μ (bP n).1 (max (bP n) (aP (n + 1))).1
    exact (hmax_spec (bP n) (aP (n + 1))).1
  have ha_ae_b : ∀ n, aeSubset μ (a n) (bP n).1 := by
    intro n
    induction n with
    | zero =>
        change aeSubset μ (a 0) (aP 0).1
        exact aeSubset_refl μ (a 0)
    | succ n _ =>
        change aeSubset μ (a (n + 1)) (max (bP n) (aP (n + 1))).1
        exact (hmax_spec (bP n) (aP (n + 1))).2
  have hb_tendsto :
      Filter.Tendsto (fun n => μ (bP n).1) Filter.atTop
        (nhds (sSup ((fun t : Set α => μ t) '' c))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hv_tendsto tendsto_const_nhds ?_ ?_
    · intro n
      rw [← ha_mu n]
      exact measure_le_of_aeSubset (ha_ae_b n)
    · intro n
      exact le_sSup ⟨(bP n).1, (bP n).2, rfl⟩
  exact ⟨fun n => (bP n).1, fun n => (bP n).2, hb_ae_mono, hb_tendsto⟩

/-- The union of an almost-increasing cofinal sequence is still admissible. -/
private theorem chain_iUnion_admissible
    {s : Set α} {r : ℝ≥0∞} {c : Set (Set α)} (_hr_ne_top : r ≠ ∞)
    {u : ℕ → Set α} (hu_mem : ∀ n, u n ∈ c)
    (hu_ae_mono : ∀ n, aeSubset μ (u n) (u (n + 1)))
    (_hu_tendsto :
      Filter.Tendsto (fun n => μ (u n)) Filter.atTop
        (nhds (sSup ((fun t : Set α => μ t) '' c))))
    (hc_adm : c ⊆ admissibleSubsets μ s r) :
    (⋃ n, u n) ∈ admissibleSubsets μ s r := by
  refine ⟨MeasurableSet.iUnion fun n => (hc_adm (hu_mem n)).1, ?_, ?_⟩
  · intro x hx
    rcases mem_iUnion.1 hx with ⟨n, hxn⟩
    exact (hc_adm (hu_mem n)).2.1 hxn
  · have hacc_le : ∀ n, μ (accumulate u n) ≤ r := by
      intro n
      exact (measure_le_of_aeSubset (accumulate_aeSubset_of_ae_mono (μ := μ) hu_ae_mono n)).trans
        (hc_adm (hu_mem n)).2.2
    have hacc_tendsto :
        Filter.Tendsto (fun n => μ (accumulate u n)) Filter.atTop
          (nhds (μ (⋃ n, u n))) :=
      tendsto_measure_iUnion_accumulate (μ := μ) (f := u)
    exact le_of_tendsto' hacc_tendsto hacc_le

/-- The union of the cofinal sequence dominates every member of the chain
modulo null sets. -/
private theorem chain_iUnion_ae_dominates
    {s : Set α} {r : ℝ≥0∞} {c : Set (Set α)} (hr_ne_top : r ≠ ∞)
    (hc_chain : IsChain (aeSubset μ) c) (hc_adm : c ⊆ admissibleSubsets μ s r)
    {u : ℕ → Set α} (hu_mem : ∀ n, u n ∈ c)
    (hu_ae_mono : ∀ n, aeSubset μ (u n) (u (n + 1)))
    (hu_tendsto :
      Filter.Tendsto (fun n => μ (u n)) Filter.atTop
        (nhds (sSup ((fun t : Set α => μ t) '' c)))) :
    ∀ t ∈ c, aeSubset μ t (⋃ n, u n) := by
  intro t htc
  by_cases ht_below : ∃ n, aeSubset μ t (u n)
  · rcases ht_below with ⟨n, htn⟩
    refine aeSubset_trans htn ?_
    rw [aeSubset, diff_eq_empty.2 (subset_iUnion u n)]
    simp
  · have hu_le_t : ∀ n, aeSubset μ (u n) t := by
      intro n
      by_cases h_eq : u n = t
      · simpa [h_eq] using aeSubset_refl μ t
      · rcases hc_chain (hu_mem n) htc h_eq with hut | htu
        · exact hut
        · exact False.elim (ht_below ⟨n, htu⟩)
    have hUnion_le_t : aeSubset μ (⋃ n, u n) t := by
      have hsubset : (⋃ n, u n) \ t ⊆ ⋃ n, u n \ t := by
        intro x hx
        rcases mem_iUnion.1 hx.1 with ⟨n, hxn⟩
        exact mem_iUnion.2 ⟨n, ⟨hxn, hx.2⟩⟩
      exact nonpos_iff_eq_zero.1 <|
        (measure_mono hsubset).trans <| by
          rw [nonpos_iff_eq_zero, measure_iUnion_null_iff]
          exact hu_le_t
    have hacc_eq : ∀ n, μ (accumulate u n) = μ (u n) := by
      intro n
      exact le_antisymm
        (measure_le_of_aeSubset (accumulate_aeSubset_of_ae_mono (μ := μ) hu_ae_mono n))
        (measure_mono subset_accumulate)
    have hacc_tendsto_sup :
        Filter.Tendsto (fun n => μ (accumulate u n)) Filter.atTop
          (nhds (sSup ((fun t : Set α => μ t) '' c))) := by
      refine hu_tendsto.congr' ?_
      exact Filter.Eventually.of_forall fun n => (hacc_eq n).symm
    have hacc_tendsto_union :
        Filter.Tendsto (fun n => μ (accumulate u n)) Filter.atTop
          (nhds (μ (⋃ n, u n))) :=
      tendsto_measure_iUnion_accumulate (μ := μ) (f := u)
    have hUnion_eq_sup :
        μ (⋃ n, u n) = sSup ((fun t : Set α => μ t) '' c) :=
      tendsto_nhds_unique hacc_tendsto_union hacc_tendsto_sup
    have ht_le_union : μ t ≤ μ (⋃ n, u n) := by
      calc
        μ t ≤ sSup ((fun t : Set α => μ t) '' c) := le_sSup ⟨t, htc, rfl⟩
        _ = μ (⋃ n, u n) := hUnion_eq_sup.symm
    have hUnion_meas : MeasurableSet (⋃ n, u n) :=
      MeasurableSet.iUnion fun n => (hc_adm (hu_mem n)).1
    have ht_ne_top : μ t ≠ ∞ :=
      ne_top_of_le_ne_top hr_ne_top (hc_adm htc).2.2
    have hUnion_ae_t : (⋃ n, u n) =ᵐ[μ] t :=
      ae_eq_of_ae_subset_of_measure_ge
        (by rwa [ae_le_set])
        ht_le_union
        hUnion_meas.nullMeasurableSet
        ht_ne_top
    exact (ae_eq_set.mp hUnion_ae_t).2

/-- Every chain of admissible sets has an admissible upper bound for
`aeSubset`. -/
private theorem exists_admissible_chain_upper_bound
    {s : Set α} {r : ℝ≥0∞} (hr_ne_top : r ≠ ∞)
    {c : Set (Set α)} (hc_chain : IsChain (aeSubset μ) c)
    (hc_adm : c ⊆ admissibleSubsets μ s r) :
    ∃ ub : Set α,
      ub ∈ admissibleSubsets μ s r ∧ ∀ t ∈ c, aeSubset μ t ub := by
  classical
  by_cases hc_empty : c = ∅
  · refine ⟨∅, admissible_empty (μ := μ), ?_⟩
    intro t ht
    simp [hc_empty] at ht
  · have hc_ne : c.Nonempty := Set.nonempty_iff_ne_empty.2 hc_empty
    obtain ⟨u, hu_mem, hu_ae_mono, hu_tendsto⟩ :=
      exists_ae_monotone_chain_approximating_sequence
        (μ := μ) hc_ne hc_chain hc_adm
    refine ⟨⋃ n, u n, ?_, ?_⟩
    · exact chain_iUnion_admissible (μ := μ) hr_ne_top hu_mem hu_ae_mono hu_tendsto hc_adm
    · exact chain_iUnion_ae_dominates
        (μ := μ) hr_ne_top hc_chain hc_adm hu_mem hu_ae_mono hu_tendsto

/-- Zorn's lemma applied to admissible sets ordered by almost-everywhere
inclusion. -/
private theorem exists_maximal_admissible_for_aeSubset
    {s : Set α} (_hs : MeasurableSet s) {r : ℝ≥0∞} (hr_ne_top : r ≠ ∞) :
    ∃ m : Set α,
      m ∈ admissibleSubsets μ s r ∧
        ∀ t : Set α, t ∈ admissibleSubsets μ s r →
          aeSubset μ m t → aeSubset μ t m := by
  -- Apply `exists_maximal_of_chains_bounded` to the relation `aeSubset μ` on
  -- the subtype of admissible sets, using
  -- `exists_admissible_chain_upper_bound` for chain upper bounds.
  have hchain :
      ∀ c : Set (Set α), IsChain (aeSubset μ) c →
        c ⊆ admissibleSubsets μ s r →
          ∃ ub : Set α,
            ub ∈ admissibleSubsets μ s r ∧ ∀ t ∈ c, aeSubset μ t ub :=
    fun c hc_chain hc_adm =>
      exists_admissible_chain_upper_bound (μ := μ) hr_ne_top hc_chain hc_adm
  let A : Set (Set α) := admissibleSubsets μ s r
  let R : {t : Set α // t ∈ A} → {t : Set α // t ∈ A} → Prop :=
    fun p q => aeSubset μ p.1 q.1
  have hbounded : ∀ C : Set {t : Set α // t ∈ A}, IsChain R C →
      ∃ ub : {t : Set α // t ∈ A}, ∀ a ∈ C, R a ub := by
    intro C hC
    let c : Set (Set α) := Subtype.val '' C
    have hc_chain : IsChain (aeSubset μ) c := by
      intro x hx y hy hxy
      rcases hx with ⟨px, hpxC, rfl⟩
      rcases hy with ⟨py, hpyC, rfl⟩
      exact hC hpxC hpyC (fun hpq => hxy (congrArg Subtype.val hpq))
    have hc_adm : c ⊆ A := by
      rintro x ⟨px, -, rfl⟩
      exact px.2
    obtain ⟨ub, hub_adm, hub⟩ := hchain c hc_chain hc_adm
    refine ⟨⟨ub, hub_adm⟩, ?_⟩
    intro a haC
    exact hub a.1 ⟨a, haC, rfl⟩
  obtain ⟨m, hm⟩ :=
    exists_maximal_of_chains_bounded hbounded
      (fun {_a _b _c} hab hbc => aeSubset_trans hab hbc)
  exact ⟨m.1, m.2, fun t ht hmt => hm ⟨t, ht⟩ hmt⟩

/-- Maximal admissible set, modulo null enlargement.

The Zorn argument is carried out in the measure algebra rather than by literal
set inclusion. This avoids the measurability issue for arbitrary unions of
chains and is the formal analogue of choosing a maximal equivalence class of
admissible sets modulo almost-everywhere equality.

The conclusion says that `m` is admissible and cannot be enlarged, modulo null
sets, by another admissible measurable subset of `s`: if `m \ t` is null, then
also `t \ m` is null. -/
private theorem exists_ae_maximal_admissible_subset
    {s : Set α} (hs : MeasurableSet s) {r : ℝ≥0∞} (hr_ne_top : r ≠ ∞) :
    ∃ m : Set α,
      MeasurableSet m ∧ m ⊆ s ∧ μ m ≤ r ∧
        ∀ ⦃t : Set α⦄, MeasurableSet t → t ⊆ s → μ t ≤ r →
          μ (m \ t) = 0 → μ (t \ m) = 0 := by
  obtain ⟨m, hm_adm, hm_max⟩ :=
    exists_maximal_admissible_for_aeSubset (μ := μ) hs hr_ne_top
  refine ⟨m, hm_adm.1, hm_adm.2.1, hm_adm.2.2, ?_⟩
  intro t ht_meas hts ht_le hmt
  exact hm_max t ⟨ht_meas, hts, ht_le⟩ hmt

/-- If an admissible `m` has measure strictly below `r ≤ μ s`, then the
remaining part `s \ m` has positive measure. -/
private theorem remaining_measure_pos_of_measure_lt
    {s m : Set α} (_hs : MeasurableSet s) (hm : MeasurableSet m)
    (hms : m ⊆ s) {r : ℝ≥0∞} (hr : r ≤ μ s) (hm_lt : μ m < r) :
    0 < μ (s \ m) := by
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  have hs_eq : μ s = μ m := by
    rw [← union_diff_cancel hms, measure_union' disjoint_sdiff_right hm, hzero, add_zero]
  exact hm_lt.not_ge (hr.trans_eq hs_eq)

/-- The positive gap between the target and the current measure. -/
private theorem target_sub_measure_pos_of_lt {m : Set α} {r : ℝ≥0∞}
    (hm_lt : μ m < r) :
    0 < r - μ m := by
  exact tsub_pos_iff_lt.2 hm_lt

/-- If `μ m < r`, the remaining set contains a positive measurable piece whose
measure fits into the gap `r - μ m`. -/
private theorem exists_positive_piece_in_remaining_gap
    (hμ : μ.HasNoAtoms) {s m : Set α} (hs : MeasurableSet s)
    (hm : MeasurableSet m) (hms : m ⊆ s) {r : ℝ≥0∞}
    (hr : r ≤ μ s) (hm_lt : μ m < r) :
    ∃ n : Set α,
      MeasurableSet n ∧ n ⊆ s \ m ∧ 0 < μ n ∧ μ n ≤ r - μ m := by
  have hremaining_pos : 0 < μ (s \ m) :=
    remaining_measure_pos_of_measure_lt (μ := μ) hs hm hms hr hm_lt
  have hgap_pos : 0 < r - μ m :=
    target_sub_measure_pos_of_lt (μ := μ) hm_lt
  exact exists_pos_measurable_subset_measure_le
    (μ := μ) hμ (hs.diff hm) hremaining_pos hgap_pos

/-- Adding a remaining piece whose measure fits the gap preserves
admissibility. -/
private theorem union_admissible_of_piece_le_gap
    {s m n : Set α} (hm : MeasurableSet m) (hms : m ⊆ s)
    (hn : MeasurableSet n) (hns : n ⊆ s \ m)
    {r : ℝ≥0∞} (hm_le : μ m ≤ r) (hn_le_gap : μ n ≤ r - μ m) :
    m ∪ n ∈ admissibleSubsets μ s r := by
  refine ⟨hm.union hn, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hms hx
    · exact (hns hx).1
  · have hdisj : Disjoint m n := by
      rw [Set.disjoint_left]
      intro x hxm hxn
      exact (hns hxn).2 hxm
    calc
      μ (m ∪ n) = μ m + μ n := measure_union' hdisj hm
      _ = μ n + μ m := add_comm _ _
      _ ≤ (r - μ m) + μ m := add_le_add_left hn_le_gap _
      _ = μ m + (r - μ m) := add_comm _ _
      _ = r := add_tsub_cancel_of_le hm_le

/-- A positive remaining piece contradicts almost-everywhere maximality. -/
private theorem positive_piece_contradicts_ae_maximal
    {s m n : Set α} (hm : MeasurableSet m) (hms : m ⊆ s)
    (hm_le : μ m ≤ r)
    (hm_max :
      ∀ ⦃t : Set α⦄, MeasurableSet t → t ⊆ s → μ t ≤ r →
        μ (m \ t) = 0 → μ (t \ m) = 0)
    (hn : MeasurableSet n) (hns : n ⊆ s \ m)
    (hn_pos : 0 < μ n) (hn_le_gap : μ n ≤ r - μ m) :
    False := by
  have ht_adm : m ∪ n ∈ admissibleSubsets μ s r :=
    union_admissible_of_piece_le_gap (μ := μ) hm hms hn hns hm_le hn_le_gap
  have hm_diff_union : μ (m \ (m ∪ n)) = 0 := by
    rw [diff_eq_empty.2 subset_union_left]
    simp
  have h_union_diff_null : μ ((m ∪ n) \ m) = 0 :=
    hm_max ht_adm.1 ht_adm.2.1 ht_adm.2.2 hm_diff_union
  have hn_subset_union_diff : n ⊆ (m ∪ n) \ m := by
    intro x hx
    exact ⟨Or.inr hx, (hns hx).2⟩
  have hn_zero : μ n = 0 :=
    le_antisymm ((measure_mono hn_subset_union_diff).trans_eq h_union_diff_null) (zero_le _)
  exact hn_pos.ne' hn_zero

/-- A maximal admissible set cannot have measure strictly below the target. -/
private theorem not_measure_lt_of_ae_maximal
    (hμ : μ.HasNoAtoms) {s m : Set α} (hs : MeasurableSet s)
    (hm : MeasurableSet m) (hms : m ⊆ s) {r : ℝ≥0∞}
    (hr : r ≤ μ s) (hm_le : μ m ≤ r)
    (hm_max :
      ∀ ⦃t : Set α⦄, MeasurableSet t → t ⊆ s → μ t ≤ r →
        μ (m \ t) = 0 → μ (t \ m) = 0) :
    ¬ μ m < r := by
  intro hm_lt
  obtain ⟨n, hn, hns, hn_pos, hn_le_gap⟩ :=
    exists_positive_piece_in_remaining_gap (μ := μ) hμ hs hm hms hr hm_lt
  exact positive_piece_contradicts_ae_maximal
    (μ := μ) hm hms hm_le hm_max hn hns hn_pos hn_le_gap

/-- A maximal admissible set has exactly the target measure.

If `m` were strictly smaller than `r`, then `s \ m` would have positive measure
because `r ≤ μ s`. The small-piece lemma would give a positive measurable
`n ⊆ s \ m` with `μ n ≤ r - μ m`. Then `m ∪ n` would still be admissible and
would strictly enlarge `m` modulo null sets, contradicting maximality. -/
private theorem ae_maximal_admissible_measure_eq
    (hμ : μ.HasNoAtoms) {s m : Set α} (hs : MeasurableSet s)
    (hm : MeasurableSet m) (hms : m ⊆ s) {r : ℝ≥0∞}
    (_hr_ne_top : r ≠ ∞) (hr : r ≤ μ s) (hm_le : μ m ≤ r)
    (hm_max :
      ∀ ⦃t : Set α⦄, MeasurableSet t → t ⊆ s → μ t ≤ r →
        μ (m \ t) = 0 → μ (t \ m) = 0) :
    μ m = r := by
  exact le_antisymm hm_le <|
    le_of_not_gt <|
      not_measure_lt_of_ae_maximal (μ := μ) hμ hs hm hms hr hm_le hm_max

/-- Exact subset form of `Measure.HasNoAtoms.isContinuous`. If `s` is
measurable and `r ≤ μ s`, then `s` contains a measurable subset of measure
exactly `r`. -/
theorem exists_measurable_subset_measure_eq_of_le
    (hμ : μ.HasNoAtoms) {s : Set α} (hs : MeasurableSet s) {r : ℝ≥0∞} (hr : r ≤ μ s) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ μ t = r := by
  classical
  by_cases hr_top : r = ∞
  · refine ⟨s, hs, Subset.rfl, ?_⟩
    simpa [hr_top] using top_unique (hr_top ▸ hr)
  · obtain ⟨m, hm, hms, hm_le, hm_max⟩ :=
      exists_ae_maximal_admissible_subset (μ := μ) (s := s) hs hr_top
    exact ⟨m, hm, hms,
      ae_maximal_admissible_measure_eq (μ := μ) hμ hs hm hms hr_top hr hm_le hm_max⟩

/-- An atomless measure is continuous: below every measurable set, every
smaller measure is attained by a measurable subset. -/
theorem isContinuous (hμ : μ.HasNoAtoms) : μ.IsContinuous := by
  intro s hs r hr
  exact hμ.exists_measurable_subset_measure_eq_of_le hs hr

end Measure.HasNoAtoms

end MeasureTheory
