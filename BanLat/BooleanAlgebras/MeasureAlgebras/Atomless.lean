/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Atomless
import BanLat.BooleanAlgebras.Functional.Hahn
import BanLat.BooleanAlgebras.MeasureAlgebras.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decomposition and representation results in atomless measure algebras

This file proves the following decomposition results:

* `exists_measure_eq_of_isAtomless`: for every `a` in an atomless measure algebra
and `0 ≤ r ≤ μ a` there exists `b ≤ a` with `μ b = r`.
* `exists_bisect_of_isAtomless`: for every `a` in an atomless measure algebra there
exists `b, c ≤ a` with `b ⊔ c = a`, `b ⊓ c = ⊥` and `μ b = μ c = μ a / 2`.

And also the following representation result:

* `exists_infFunctional_apply_eq_of_isRelativelyAtomless:` Let `(B, μ)` be relatively
atomless with respect to `A` and `ν : A → ℝ≥0∞` be a countably additive functional such
that `ν(a) ≤ μ(a)` for every `a ∈ A`. Then there is `b ∈ B` such that `ν(a) = μ (a ⊓ b)`
for every `a ∈ A`.
-/

open scoped ENNReal

universe u


namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

private theorem exists_positive_le_half_of_isAtomless
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    {s : B} (hs : s ≠ ⊥) :
    ∃ t ≤ s, 0 < μ t ∧ μ t ≤ μ s / 2 := by
  obtain ⟨u, hu_lt, hu_ne⟩ := hB.exists_nonzero_lt hs
  by_cases hu_le : μ u ≤ μ s / 2
  · exact ⟨u, hu_lt.le, pos_iff_ne_zero.2 (mt (μ.measure_eq_zero_iff u).1 hu_ne), hu_le⟩
  · refine ⟨s \ u, sdiff_le, ?_, ?_⟩
    · exact pos_iff_ne_zero.2 (mt (μ.measure_eq_zero_iff (s \ u)).1
        (sdiff_eq_bot_iff.not.mpr (not_le_of_gt hu_lt)))
    · rw [μ.measure_sdiff hu_lt.le]
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
  rw [μ.measure_sdiff hb, hμb,
    ENNReal.sub_half (μ.measure_ne_top a)]

section

variable (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
variable (hA : A.IsSigmaComplete)

/-- If `B` is relatively atomless with respect to `A` and `b ∈ B`, `b ≠ ⊥`,
there is `d ∈ B`, `d ≠ ⊥`, with `d ≤ b` and `μ (a ⊓ d) ≤ μ (a ⊓ b) / 2`
for every `a ∈ A`. -/
private lemma exists_nonzero_infFunctional_le_half
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ {b : B}, b ≠ ⊥ →
      ∃ d : B, d ≠ ⊥ ∧ d ≤ b ∧
        ∀ a : A, μ.infFunctional A hA d a ≤ μ.infFunctional A hA b a / 2 := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro b hb
  obtain ⟨e, heb, he⟩ := hrel hb
  let α := μ.infFunctional A hA b
  let ε := μ.infFunctional A hA e
  let ρ := ε.scaledFunctional 2
  have hα : α.IsFinite := μ.infFunctional_isFinite A hA b
  have hε : ε.IsFinite := μ.infFunctional_isFinite A hA e
  have hρ : ρ.IsFinite := ε.scaledFunctional_isFinite 2 hε
  obtain ⟨p, hp⟩ := ρ.exists_isHahnDecomposition α hρ hα
  by_cases hep : e ⊓ (p : B) ≠ ⊥
  · refine ⟨e ⊓ (p : B), hep, inf_le_left.trans heb, ?_⟩
    intro a
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    have hle := hp.le_on (show a ⊓ p ≤ p from inf_le_right)
    have hmono : α (a ⊓ p) ≤ α a := α.monotone inf_le_left
    exact le_trans (by simpa [ρ, ε, α, mul_comm, inf_assoc, inf_left_comm, inf_comm] using hle)
      (by simpa [α, inf_assoc, inf_left_comm, inf_comm] using hmono)
  · let d := b \ (e ⊔ (p : B))
    have hd_ne : d ≠ ⊥ := by
      intro hd
      have hb_le : b ≤ e ⊔ (p : B) := sdiff_eq_bot_iff.mp hd
      have hep_disj : Disjoint e (p : B) := by
        rw [disjoint_iff]
        exact not_ne_iff.mp hep
      apply he pᶜ
      apply le_antisymm
      · exact le_inf heb (le_compl_iff_disjoint_right.mpr hep_disj)
      · calc
          b ⊓ ((p : B)ᶜ) ≤ (e ⊔ (p : B)) ⊓ ((p : B)ᶜ) :=
            inf_le_inf_right _ hb_le
          _ ≤ e := by simp [inf_sup_right]
    refine ⟨d, hd_ne, sdiff_le, ?_⟩
    intro a
    let q : A := a \ p
    have hq_disj : Disjoint q p := disjoint_sdiff_self_left
    have hle := hp.ge_on_compl hq_disj
    change μ ((q : B) ⊓ b) ≤ 2 * μ ((q : B) ⊓ e) at hle
    have hqb : ((q : B) ⊓ b) ⊓ e = (q : B) ⊓ e := by
      rw [inf_assoc, inf_eq_right.mpr heb]
    have had : (a : B) ⊓ d = ((q : B) ⊓ b) \ e := by
      change (a : B) ⊓ d = (((a : B) \ (p : B)) ⊓ b) \ e
      simp only [d, sdiff_eq, compl_sup]
      ac_rfl
    have hsplit := μ.measure_sdiff_add_inf ((q : B) ⊓ b) e
    rw [hqb] at hsplit
    change μ ((a : B) ⊓ d) ≤ μ ((a : B) ⊓ b) / 2
    rw [had]
    apply (ENNReal.toReal_le_toReal (μ.measure_ne_top _)
      (ENNReal.div_ne_top (μ.measure_ne_top _) (by norm_num))).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_ofNat]
    have hsplit_real := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add (μ.measure_ne_top _) (μ.measure_ne_top _)] at hsplit_real
    have hle_real := (ENNReal.toReal_le_toReal (α.ne_top hα q) (ρ.ne_top hρ q)).mpr hle
    simp only [α, ρ, ε, CountablyAdditiveFunctional.scaledFunctional_apply,
      ENNReal.toReal_mul] at hle_real
    change (μ ((q : B) ⊓ b)).toReal ≤ 2 * (μ ((q : B) ⊓ e)).toReal at hle_real
    have hmono : μ ((q : B) ⊓ b) ≤ μ ((a : B) ⊓ b) := by
      apply μ.measure_mono
      exact inf_le_inf_right b (show (q : B) ≤ a from sdiff_le)
    have hmono_real := (ENNReal.toReal_le_toReal (μ.measure_ne_top _)
      (μ.measure_ne_top _)).mpr hmono
    linarith

/-- If `B` is relatively atomless with respect to `A`, `b ∈ B`, `b ≠ ⊥`, and
`n ∈ ℕ`, there is `d ∈ B`, `d ≠ ⊥`, with `d ≤ b` and
`μ (a ⊓ d) ≤ μ (a ⊓ b) / 2 ^ n` for every `a ∈ A`. -/
private lemma exists_nonzero_infFunctional_le_two_pow
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ {b : B}, b ≠ ⊥ → ∀ n : ℕ,
      ∃ d : B, d ≠ ⊥ ∧ d ≤ b ∧
        ∀ a : A, μ.infFunctional A hA d a ≤
          μ.infFunctional A hA b a / (2 ^ n) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro b hb n
  induction n with
  | zero =>
      exact ⟨b, hb, le_rfl, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc, hcb, hsmall⟩ := ih
      obtain ⟨d, hd, hdc, hdhalf⟩ :=
        exists_nonzero_infFunctional_le_half μ A hA hrel hc
      refine ⟨d, hd, hdc.trans hcb, fun a ↦ (hdhalf a).trans ?_⟩
      calc
        μ.infFunctional A hA c a / 2 ≤
            (μ.infFunctional A hA b a / (2 ^ n)) / 2 :=
          ENNReal.div_le_div_right (hsmall a) 2
        _ = μ.infFunctional A hA b a / (2 ^ (n + 1)) := by
          rw [pow_succ]
          simp only [ENNReal.div_eq_inv_mul]
          rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by norm_num))]
          ac_rfl

/-- Let `B` be a relatively atomless with respect to `A`, `b ∈ B`, `ν : A → ℝ≥0∞` a countably
additive functional such that `ν ⊤ ≠ 0`, and `ν a ≤ μ (a ⊓ b)` for every `a ∈ A`. Then there is
`d ∈ B`, `d ≠ ⊥`, with `d ≤ b` and `μ (a ⊓ d) ≤ ν a` for every `a ∈ A`. -/
private lemma exists_nonzero_infFunctional_le
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ {b : B} (ν : CountablyAdditiveFunctional A), ν ⊤ ≠ 0 →
      (∀ a : A, ν a ≤ μ.infFunctional A hA b a) →
        ∃ d : B, d ≠ ⊥ ∧ d ≤ b ∧
          ∀ a : A, μ.infFunctional A hA d a ≤ ν a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro b ν hν_top hν
  let α := μ.infFunctional A hA b
  have hα : α.IsFinite := μ.infFunctional_isFinite A hA b
  have hν_fin : ν.IsFinite := ne_top_of_le_ne_top hα (hν ⊤)
  obtain ⟨n, hsmall⟩ : ∃ n : ℕ, α ⊤ / 2 ^ n < ν ⊤ := by
    by_contra h
    push Not at h
    apply hν_top
    apply ENNReal.eq_zero_of_le_mul_pow (x := ν ⊤) (r := 2⁻¹)
      (ε := (α ⊤).toNNReal) ENNReal.one_half_lt_one
    intro n
    calc
      ν ⊤ ≤ α ⊤ / 2 ^ n := h n
      _ = ((α ⊤).toNNReal : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ n := by
        rw [ENNReal.coe_toNNReal (α.ne_top hα ⊤)]
        simp [div_eq_mul_inv, ENNReal.inv_pow]
  let r : NNReal := (2 ^ n)⁻¹
  let ρ := α.scaledFunctional r
  have hρ : ρ.IsFinite := α.scaledFunctional_isFinite r hα
  obtain ⟨p, hp⟩ := ρ.exists_isHahnDecomposition ν hρ hν_fin
  let c := b ⊓ (p : B)
  have hc : c ≠ ⊥ := by
    intro hc
    have hαp : α p = 0 := by
      simp only [α, infFunctional_apply]
      rw [show (p : B) ⊓ b = ⊥ by simpa [c, inf_comm] using hc, μ.measure_bot]
    have hνp : ν p = 0 := le_antisymm ((hν p).trans_eq hαp) bot_le
    have hρp : ρ p = 0 := by simp [ρ, hαp]
    have hout := hp.ge_on_compl (disjoint_compl_left : Disjoint pᶜ p)
    have hνsplit := ν.map_add_map_compl p
    have hρsplit := ρ.map_add_map_compl p
    rw [hνp, zero_add] at hνsplit
    rw [hρp, zero_add] at hρsplit
    apply (not_le_of_gt hsmall)
    calc
      ν ⊤ = ν pᶜ := hνsplit.symm
      _ ≤ ρ pᶜ := hout
      _ = ρ ⊤ := hρsplit
      _ = α ⊤ / (2 ^ n) := by simp [ρ, r, ENNReal.div_eq_inv_mul]
  obtain ⟨d, hd, hdc, hdsmall⟩ :=
    exists_nonzero_infFunctional_le_two_pow μ A hA hrel hc n
  refine ⟨d, hd, hdc.trans inf_le_left, ?_⟩
  intro a
  have hle := hp.le_on (show a ⊓ p ≤ p from inf_le_right)
  calc
    μ.infFunctional A hA d a ≤ μ.infFunctional A hA c a / (2 ^ n) := hdsmall a
    _ = ρ (a ⊓ p) := by
      simp [ρ, r, α, c, ENNReal.div_eq_inv_mul, inf_left_comm, inf_comm]
    _ ≤ ν (a ⊓ p) := hle
    _ ≤ ν a := ν.monotone inf_le_left

/-- If `ν : A → ℝ≥0∞` is a countably additive functional, there is a maximal
element `b ∈ B` satisfying `μ (a ⊓ b) ≤ ν a` for every `a ∈ A`. -/
private lemma exists_maximal_infFunctional_le :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ (ν : CountablyAdditiveFunctional A),
      ∃ b : B, (∀ a : A, μ.infFunctional A hA b a ≤ ν a) ∧
        ∀ c : B, b ≤ c → (∀ a : A, μ.infFunctional A hA c a ≤ ν a) → c = b := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro ν
  let S : Set B := {b | ∀ a : A, μ.infFunctional A hA b a ≤ ν a}
  have hbot : ⊥ ∈ S := by simp [S]
  have hchain : ∀ s ⊆ S, IsChain (· ≤ ·) s → ∃ ub ∈ S, ∀ z ∈ s, z ≤ ub := by
    intro s hsS hs
    by_cases hs_empty : s = ∅
    · exact ⟨⊥, hbot, by simp [hs_empty]⟩
    · have hs_ne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hs_empty
      let V : Set ℝ≥0∞ := μ '' s
      have hV_ne : V.Nonempty := hs_ne.image μ
      have hV_bdd : BddAbove V := by
        refine ⟨μ ⊤, ?_⟩
        rintro _ ⟨x, -, rfl⟩
        exact μ.measure_mono le_top
      obtain ⟨v, hv_mono, hv_lim, hv⟩ := exists_seq_tendsto_sSup hV_ne hV_bdd
      have hx_exists (n : ℕ) : ∃ x ∈ s, μ x = v n := by
        simpa only [V, Set.mem_image] using hv n
      choose x hx_mem hx_measure using hx_exists
      have hx_mono : Monotone x := by
        intro n m hnm
        have hmeasure : μ (x n) ≤ μ (x m) := by
          rw [hx_measure n, hx_measure m]
          exact hv_mono hnm
        rcases hs.total (hx_mem n) (hx_mem m) with hle | hle
        · exact hle
        · by_contra hge
          exact (not_lt_of_ge hmeasure) (μ.measure_strictMono (hle.lt_of_not_ge hge))
      let ub : B := ⨆ n, x n
      have hub_mem : ub ∈ S := by
        intro a
        change μ ((a : B) ⊓ ub) ≤ ν a
        rw [show (a : B) ⊓ ub = ⨆ n, (a : B) ⊓ x n by
          exact SigmaCompleteBooleanAlgebra.inf_iSup_nat (a : B) x]
        rw [μ.measure_iSup_eq_iSup]
        · exact iSup_le fun n ↦ hsS (hx_mem n) a
        · exact fun _ _ hnm ↦ inf_le_inf_left (a : B) (hx_mono hnm)
      refine ⟨ub, hub_mem, ?_⟩
      intro z hz
      by_cases hzx : ∃ n, z ≤ x n
      · obtain ⟨n, hn⟩ := hzx
        exact hn.trans (SigmaCompleteBooleanAlgebra.le_iSup_nat x n)
      · have hubz : ub ≤ z := by
          apply SigmaCompleteBooleanAlgebra.iSup_nat_le
          intro n
          exact (hs.total (hx_mem n) hz).resolve_right fun hzn ↦ hzx ⟨n, hzn⟩
        have hμx_lim : Filter.Tendsto (fun n ↦ μ (x n)) Filter.atTop (nhds (μ ub)) :=
          μ.tendsto_measure_iSup hx_mono
        have hv_lim' : Filter.Tendsto v Filter.atTop (nhds (μ ub)) :=
          hμx_lim.congr' <| Filter.Eventually.of_forall fun n ↦ hx_measure n
        have hμub : μ ub = sSup V := tendsto_nhds_unique hv_lim' hv_lim
        have hμzu : μ z ≤ μ ub := by
          rw [hμub]
          exact le_csSup hV_bdd ⟨z, hz, rfl⟩
        by_contra hge
        exact (not_lt_of_ge hμzu) (μ.measure_strictMono (hubz.lt_of_not_ge hge))
  obtain ⟨b, hb⟩ := zorn_le₀ S hchain
  refine ⟨b, hb.1, ?_⟩
  intro c hbc hc
  exact (hb.eq_of_le hc hbc).symm

/-- If `B` is relatively atomless with respect to `A` and `b ∈ B` is maximal subject to
`μ (a ⊓ b) ≤ ν a`, then `μ (a ⊓ b) = ν a` for every `a ∈ A`. -/
private theorem infFunctional_apply_eq_of_maximal
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ (ν : CountablyAdditiveFunctional A),
      (∀ a : A, ν a ≤ μ (a : B)) → ∀ b : B,
        (∀ a : A, μ.infFunctional A hA b a ≤ ν a) →
          (∀ c : B, b ≤ c →
            (∀ a : A, μ.infFunctional A hA c a ≤ ν a) → c = b) →
              ∀ a : A, μ.infFunctional A hA b a = ν a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro ν hν b hb hbmax a
  apply le_antisymm (hb a)
  by_contra hle
  let ρ := μ.infFunctional A hA b
  have hρ_fin : ρ.IsFinite := μ.infFunctional_isFinite A hA b
  let δ := ν.subFunctional ρ hρ_fin hb
  have hδa : δ a ≠ 0 := fun h ↦ hle (tsub_eq_zero_iff_le.mp h)
  have hδ_top : δ ⊤ ≠ 0 := by
    intro hzero
    apply hδa
    exact le_antisymm ((δ.monotone le_top).trans_eq hzero) bot_le
  have hδ : ∀ a : A, δ a ≤ μ.infFunctional A hA bᶜ a := by
    intro a
    simp only [δ, CountablyAdditiveFunctional.subFunctional_apply]
    rw [tsub_le_iff_right]
    calc
      ν a ≤ μ (a : B) := hν a
      _ = μ.infFunctional A hA bᶜ a + ρ a := by
        change μ (a : B) = μ ((a : B) ⊓ bᶜ) + μ ((a : B) ⊓ b)
        simpa only [sdiff_eq] using (μ.measure_sdiff_add_inf (a : B) b).symm
  obtain ⟨d, hd, hdc, hdδ⟩ :=
    exists_nonzero_infFunctional_le μ A hA hrel δ hδ_top hδ
  have hbd_disj : Disjoint b d :=
    (le_compl_iff_disjoint_right.mp hdc).symm
  have hsup : ∀ a : A, μ.infFunctional A hA (b ⊔ d) a ≤ ν a := by
    intro a
    calc
      μ.infFunctional A hA (b ⊔ d) a = ρ a + μ.infFunctional A hA d a :=
        μ.infFunctional_sup_apply A hA hbd_disj a
      _ ≤ ρ a + δ a := add_le_add le_rfl (hdδ a)
      _ = ν a := ν.add_subFunctional_apply ρ hρ_fin hb a
  have heq : b ⊔ d = b := hbmax (b ⊔ d) le_sup_left hsup
  exact hd (hbd_disj.symm.eq_bot_of_le (le_sup_right.trans_eq heq))

/-- If `B` is relatively atomless with respect to `A` and the countably additive
functional `ν : A → ℝ≥0∞` satisfies `ν a ≤ μ a` for every `a ∈ A`, there is `b ∈ B`
such that `μ (a ⊓ b) = ν a` for every `a ∈ A`. -/
theorem exists_infFunctional_apply_eq_of_isRelativelyAtomless
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ (ν : CountablyAdditiveFunctional A),
      (∀ a : A, ν a ≤ μ (a : B)) →
        ∃ b : B, ∀ a : A, μ.infFunctional A hA b a = ν a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro ν hν
  obtain ⟨b, hb, hbmax⟩ := exists_maximal_infFunctional_le μ A hA ν
  exact ⟨b, infFunctional_apply_eq_of_maximal μ A hA hrel ν hν b hb hbmax⟩

end

end MeasureAlgebra
