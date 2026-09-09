/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Atomless
import BanLat.BooleanAlgebras.MeasureAlgebras.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decompositions in atomless measure algebras

This file proves the following decomposition results:
* for every `a` in an atomless measure algebra and `0 ≤ r ≤ μ a` there exists
`b ≤ a` with `μ b = r`.
* for every `a` in an atomless measure algebra there exists `b, c ≤ a` with
`b ⊔ c = a`, `b ⊓ c = ⊥` and `μ b = μ c = μ a / 2`.
-/

open scoped ENNReal

universe u


namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

private theorem exists_nonzero_lt_of_isAtomless
    (hB : BooleanAlgebra.IsAtomless B) {s : B} (hs : s ≠ ⊥) :
    ∃ t : B, t < s ∧ t ≠ ⊥ := by
  by_contra h
  push Not at h
  exact hB s ⟨hs, h⟩

private theorem exists_positive_le_half_of_isAtomless
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    {s : B} (hs : s ≠ ⊥) :
    ∃ t ≤ s, 0 < μ t ∧ μ t ≤ μ s / 2 := by
  obtain ⟨u, hu_lt, hu_ne⟩ := exists_nonzero_lt_of_isAtomless hB hs
  by_cases hu_le : μ u ≤ μ s / 2
  · exact ⟨u, hu_lt.le, pos_iff_ne_zero.2 (mt (μ.measure_eq_zero_iff u).1 hu_ne), hu_le⟩
  · refine ⟨s \ u, sdiff_le, ?_, ?_⟩
    · exact pos_iff_ne_zero.2 (mt (μ.measure_eq_zero_iff (s \ u)).1
        (sdiff_eq_bot_iff.not.mpr (not_le_of_gt hu_lt)))
    · have hsum := μ.measure_sdiff_add_inf s u
      rw [inf_eq_right.mpr hu_lt.le] at hsum
      rw [ENNReal.eq_sub_of_add_eq' (μ.measure_ne_top s) hsum]
      calc
        μ s - μ u ≤ μ s - μ s / 2 :=
          tsub_le_tsub_left (le_of_not_ge hu_le) _
        _ = μ s / 2 := ENNReal.sub_half (μ.measure_ne_top s)

private theorem exists_halving_sequence_of_isAtomless
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    {s : B} (hs : s ≠ ⊥) :
    ∃ u : ℕ → B,
      u 0 = s ∧
        (∀ n, u n ≤ s) ∧
        (∀ n, 0 < μ (u n)) ∧
        (∀ n, μ (u (n + 1)) ≤ μ (u n) / 2) := by
  classical
  let P := {t : B // t ≤ s ∧ t ≠ ⊥}
  have hstep : ∀ p : P, ∃ q : P,
      (q : B) ≤ p ∧ μ (q : B) ≤ μ (p : B) / 2 := by
    intro p
    obtain ⟨q, hqp, hq_pos, hq_half⟩ :=
      exists_positive_le_half_of_isAtomless μ hB p.2.2
    have hq_ne : q ≠ ⊥ := fun hq ↦
      hq_pos.ne' ((μ.measure_eq_zero_iff q).2 hq)
    exact ⟨⟨q, hqp.trans p.2.1, hq_ne⟩, hqp, hq_half⟩
  choose step hstep_spec using hstep
  let seq : ℕ → P := Nat.rec ⟨s, le_rfl, hs⟩ fun _ p ↦ step p
  refine ⟨fun n ↦ (seq n).1, rfl, fun n ↦ (seq n).2.1, ?_, ?_⟩
  · intro n
    rw [pos_iff_ne_zero]
    change μ (seq n).1 ≠ 0
    exact fun hz ↦ (seq n).2.2 ((μ.measure_eq_zero_iff (seq n).1).1 hz)
  · intro n
    simpa [seq] using (hstep_spec (seq n)).2

/-- Let `ε > 0`. Every nonzero element `s` of an atomless Boolean algebra `(B, μ)`
contains  a subelement `t` with measure `0 < μ b ≤ ε`. -/
private theorem exists_positive_le_of_isAtomless
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    {s : B} (hs : s ≠ ⊥) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ≤ s, 0 < μ t ∧ μ t ≤ ε := by
  classical
  obtain ⟨u, hu_zero, hu_le, hu_pos, hu_half⟩ :=
    exists_halving_sequence_of_isAtomless μ hB hs
  have hbound : ∀ n, μ (u n) ≤ μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          μ (u (n + 1)) ≤ μ (u n) / 2 := hu_half n
          _ ≤ (μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ n) / 2 := by gcongr
          _ = μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
            simp [div_eq_mul_inv, pow_succ, mul_assoc]
  by_contra h
  push Not at h
  have hle : ∀ n : ℕ,
      ε ≤ (μ (u 0)).toNNReal * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    calc
      ε ≤ μ (u n) := (h (u n) (hu_le n) (hu_pos n)).le
      _ ≤ μ (u 0) * (2⁻¹ : ℝ≥0∞) ^ n := hbound n
      _ = (μ (u 0)).toNNReal * (2⁻¹ : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_toNNReal (μ.measure_ne_top (u 0))]
  have hzero : ε = 0 :=
    ENNReal.eq_zero_of_le_mul_pow (x := ε) (r := (2⁻¹ : ℝ≥0∞))
      (ε := (μ (u 0)).toNNReal) ENNReal.one_half_lt_one hle
  exact hε.ne' hzero

/-- Among the subelements of `a \ x` whose measure is at most `r - μ x`, there
is one whose measure is at least half that of every other such subelement. -/
private theorem exists_dominating_increment
    (μ : MeasureAlgebra B) {a x : B} {r : ℝ≥0∞} (hr_top : r ≠ ∞) :
    ∃ y ≤ a \ x, μ y ≤ r - μ x ∧
      ∀ z ≤ a \ x, μ z ≤ r - μ x → μ z / 2 ≤ μ y := by
  classical
  let C : Set B := {y | y ≤ a \ x ∧ μ y ≤ r - μ x}
  let S : Set ℝ≥0∞ := (fun y : B ↦ μ y) '' C
  have hC_bot : ⊥ ∈ C := by simp [C]
  have hS_ne : S.Nonempty := ⟨0, ⊥, hC_bot, μ.measure_bot⟩
  have hS_bdd : BddAbove S := by
    refine ⟨r - μ x, by rintro _ ⟨y, hy, rfl⟩; exact hy.2⟩
  have hsup_le : sSup S ≤ r - μ x := by
    apply csSup_le hS_ne
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  by_cases hsup_zero : sSup S = 0
  · refine ⟨⊥, bot_le, by simp, ?_⟩
    intro z hz hμz
    have hz_le : μ z ≤ sSup S := le_csSup hS_bdd ⟨z, ⟨hz, hμz⟩, rfl⟩
    rw [hsup_zero] at hz_le
    simp [nonpos_iff_eq_zero.mp hz_le]
  · have hsup_ne_top : sSup S ≠ ∞ :=
      ne_top_of_le_ne_top hr_top (hsup_le.trans tsub_le_self)
    obtain ⟨q, hqS, hhalf_q⟩ :=
      exists_lt_of_lt_csSup hS_ne (ENNReal.half_lt_self hsup_zero hsup_ne_top)
    rcases hqS with ⟨y, hyC, rfl⟩
    refine ⟨y, hyC.1, hyC.2, ?_⟩
    intro z hz hμz
    exact (ENNReal.div_le_div_right (le_csSup hS_bdd ⟨z, ⟨hz, hμz⟩, rfl⟩) 2).trans
      hhalf_q.le

private theorem exists_dominating_extension
    (μ : MeasureAlgebra B) {a x : B} {r : ℝ≥0∞}
    (hr_top : r ≠ ∞) (hx_a : x ≤ a) (hx_r : μ x ≤ r) :
    ∃ q : B, x ≤ q ∧ q ≤ a ∧ μ q ≤ r ∧
      ∀ z ≤ a \ x, μ z ≤ r - μ x → μ z / 2 ≤ μ q - μ x := by
  obtain ⟨y, hy_rem, hy_gap, hy_max⟩ := exists_dominating_increment μ hr_top
  have hdisj : Disjoint x y := disjoint_sdiff_self_right.mono_right hy_rem
  have hmeasure : μ (x ⊔ y) = μ x + μ y := μ.measure_sup hdisj
  refine ⟨x ⊔ y, le_sup_left, sup_le hx_a (hy_rem.trans sdiff_le), ?_, ?_⟩
  · rw [hmeasure]
    calc
      μ x + μ y ≤ μ x + (r - μ x) := by gcongr
      _ = r := by rw [add_comm, tsub_add_cancel_of_le hx_r]
  · intro z hz hμz
    rw [ENNReal.sub_eq_of_eq_add_rev (μ.measure_ne_top x) hmeasure]
    exact hy_max z hz hμz

/-- There is an increasing sequence `u n` below `a` with `μ (u n) ≤ r`. At each
step, its measure increases by at least half the measure of every `z ≤ a \ u n`
satisfying `μ z ≤ r - μ (u n)`. -/
private theorem exists_exhausting_sequence
    (μ : MeasureAlgebra B) (a : B) (r : ℝ≥0∞) (hr_top : r ≠ ∞) :
    ∃ u : ℕ → B,
      (∀ n, u n ≤ u (n + 1)) ∧
        (∀ n, u n ≤ a) ∧
        (∀ n, μ (u n) ≤ r) ∧
        (∀ n z, z ≤ a \ u n → μ z ≤ r - μ (u n) →
          μ z / 2 ≤ μ (u (n + 1)) - μ (u n)) := by
  classical
  let P := {x : B // x ≤ a ∧ μ x ≤ r}
  have hstep : ∀ p : P, ∃ q : P,
      (p : B) ≤ q ∧
        ∀ z ≤ a \ p, μ z ≤ r - μ p → μ z / 2 ≤ μ q - μ p := by
    intro p
    obtain ⟨q, hpq, hqa, hqr, hq_max⟩ :=
      exists_dominating_extension μ hr_top p.2.1 p.2.2
    exact ⟨⟨q, hqa, hqr⟩, hpq, hq_max⟩
  choose step hstep_spec using hstep
  let seq : ℕ → P := Nat.rec ⟨⊥, bot_le, by simp⟩ fun _ p ↦ step p
  refine ⟨fun n ↦ (seq n).1, ?_, fun n ↦ (seq n).2.1,
    fun n ↦ (seq n).2.2, ?_⟩
  · intro n
    simpa [seq] using (hstep_spec (seq n)).1
  · intro n z hz hμz
    simpa [seq] using (hstep_spec (seq n)).2 z hz hμz

/-- In an atomless measure algebra, the supremum of an exhausting sequence has
the target measure. -/
private theorem measure_iSup_eq_target_of_exhausting_sequence
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    {a : B} {r : ℝ≥0∞} (hr : r ≤ μ a) {u : ℕ → B}
    (hu_succ : ∀ n, u n ≤ u (n + 1)) (hu_r : ∀ n, μ (u n) ≤ r)
    (hu_max : ∀ n z, z ≤ a \ u n → μ z ≤ r - μ (u n) →
      μ z / 2 ≤ μ (u (n + 1)) - μ (u n)) :
    μ (⨆ n, u n) = r := by
  have hu_mono : Monotone u := monotone_nat_of_le_succ hu_succ
  let b : B := ⨆ n, u n
  have hu_le_b : ∀ n, u n ≤ b := by
    intro n
    exact SigmaCompleteBooleanAlgebra.le_sSup_of_countable
      (Set.countable_range u) ⟨n, rfl⟩
  have hb_r : μ b ≤ r := by
    rw [μ.measure_iSup_eq_iSup hu_mono]
    exact iSup_le hu_r
  change μ b = r
  refine le_antisymm hb_r ?_
  apply le_of_not_gt
  intro hb_lt
  have hrem_ne : a \ b ≠ ⊥ := by
    intro hrem
    exact (not_le_of_gt hb_lt)
      (hr.trans (μ.measure_mono (sdiff_eq_bot_iff.mp hrem)))
  obtain ⟨z, hz_rem, hz_pos, hz_gap⟩ :=
    exists_positive_le_of_isAtomless μ hB hrem_ne (tsub_pos_iff_lt.2 hb_lt)
  have hinc : ∀ n, μ z / 2 ≤ μ (u (n + 1)) - μ (u n) := by
    intro n
    apply hu_max n z (hz_rem.trans (sdiff_le_sdiff_left (hu_le_b n)))
    exact hz_gap.trans (tsub_le_tsub_left (μ.measure_mono (hu_le_b n)) r)
  have hn_lower : ∀ n : ℕ, (n : ℝ≥0∞) * (μ z / 2) ≤ μ (u n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          ((n + 1 : ℕ) : ℝ≥0∞) * (μ z / 2) =
              (n : ℝ≥0∞) * (μ z / 2) + μ z / 2 := by
                push_cast
                ring
          _ ≤ μ (u n) + μ z / 2 := by gcongr
          _ ≤ μ (u n) + (μ (u (n + 1)) - μ (u n)) := by
            gcongr
            exact hinc n
          _ = μ (u (n + 1)) := by
            rw [add_comm, tsub_add_cancel_of_le (μ.measure_mono (hu_succ n))]
  have hhalf_ne : μ z / 2 ≠ 0 :=
    (ENNReal.div_pos hz_pos.ne' (by norm_num)).ne'
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hhalf_ne (μ.measure_ne_top b)
  exact (not_le_of_gt hn) ((hn_lower n).trans (μ.measure_mono (hu_le_b n)))

/-- In an atomless measure algebra, every value below the measure of an element
is attained by one of its subelements. -/
theorem exists_measure_eq_of_isAtomless
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    {a : B} {r : ℝ≥0∞} (hr : r ≤ μ a) :
    ∃ b ≤ a, μ b = r := by
  have hr_top : r ≠ ∞ := ne_top_of_le_ne_top (μ.measure_ne_top a) hr
  obtain ⟨u, hu_succ, hu_a, hu_r, hu_max⟩ :=
    exists_exhausting_sequence μ a r hr_top
  refine ⟨⨆ n, u n, SigmaCompleteBooleanAlgebra.sSup_le_of_countable
    (Set.countable_range u) (by rintro _ ⟨n, rfl⟩; exact hu_a n), ?_⟩
  exact measure_iSup_eq_target_of_exhausting_sequence μ hB hr hu_succ hu_r hu_max

/-- Every element of an atomless measure algebra can be partitioned into two
pieces of equal measure. -/
theorem exists_bisect_of_isAtomless
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B) (a : B) :
    ∃ b c : B,
      Disjoint b c ∧ b ⊔ c = a ∧
        μ b = μ a / 2 ∧ μ c = μ a / 2 := by
  have hhalf : μ a / 2 ≤ μ a := by
    calc
      μ a / 2 ≤ μ a / 2 + μ a / 2 := self_le_add_right _ _
      _ = μ a := ENNReal.add_halves (μ a)
  obtain ⟨b, hb, hμb⟩ := exists_measure_eq_of_isAtomless μ hB hhalf
  refine ⟨b, a \ b, disjoint_sdiff_self_right, sup_sdiff_cancel_right hb, hμb, ?_⟩
  have hsum := μ.measure_sdiff_add_inf a b
  rw [inf_eq_right.mpr hb, hμb] at hsum
  rw [ENNReal.eq_sub_of_add_eq' (μ.measure_ne_top a) hsum,
    ENNReal.sub_half (μ.measure_ne_top a)]

end MeasureAlgebra
