/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Metric structure on measure algebras

This file shows that the function `d(a, b) = μ (a ∆ b)` defines a metric
over every measure algebra `(B, μ)`. The metric space `(B, d)` is complete.
-/

open scoped ENNReal symmDiff

universe u v

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-- For all `a, b` in a measure algebra, `μ (a ∆ b) = μ (a \ b) + μ (b \ a)`. -/
theorem measure_symmDiff (a b : B) :
    μ (a ∆ b) = μ (a \ b) + μ (b \ a) := by
  exact μ.measure_sup disjoint_sdiff_sdiff

/-- The metric associated with a finite measure algebra. -/
@[implicit_reducible]
noncomputable def toMetricSpace : MetricSpace B where
  dist a b := (μ (a ∆ b)).toReal
  dist_self := by
    simp
  dist_comm := by
    intro a b
    rw [symmDiff_comm]
  dist_triangle := by
    intro a b c
    rw [← ENNReal.toReal_add (μ.measure_ne_top _) (μ.measure_ne_top _)]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨μ.measure_ne_top _, μ.measure_ne_top _⟩)
      ((μ.measure_mono (symmDiff_triangle a b c)).trans (μ.measure_sup_le _ _))
  eq_of_dist_eq_zero := by
    intro a b h
    apply symmDiff_eq_bot.mp
    apply (μ.measure_eq_zero_iff _).mp
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (μ.measure_ne_top _)

/-- The distance is the real value of the measure of the symmetric difference. -/
@[simp]
theorem dist_eq_measure_symmDiff (a b : B) :
    letI := μ.toMetricSpace
    dist a b = (μ (a ∆ b)).toReal := by
  rfl

/-- The distance from an element to the bottom element is its measure. -/
@[simp]
theorem dist_bot (a : B) :
    letI := μ.toMetricSpace
    dist a ⊥ = (μ a).toReal := by
  simp [dist_eq_measure_symmDiff]

/-- Taking complements is an isometry. -/
theorem isometry_compl :
    letI := μ.toMetricSpace
    Isometry (fun a : B ↦ aᶜ) := by
  letI := μ.toMetricSpace
  rw [isometry_iff_dist_eq]
  intro a b
  simp only [dist_eq_measure_symmDiff, compl_symmDiff_compl]

private theorem symmDiff_sup_le_sup (a b c d : B) :
    (a ⊔ b) ∆ (c ⊔ d) ≤ (a ∆ c) ⊔ (b ∆ d) := by
  apply symmDiff_le
  · have ha := le_symmDiff_sup_right a c
    have hb := le_symmDiff_sup_right b d
    order
  · have hc := le_symmDiff_sup_right c a
    have hd := le_symmDiff_sup_right d b
    rw [symmDiff_comm c a] at hc
    rw [symmDiff_comm d b] at hd
    order

/-- Supremum is Lipschitz as a binary operation. -/
theorem lipschitzWith_sup :
    letI := μ.toMetricSpace
    LipschitzWith 2 (fun p : B × B ↦ p.1 ⊔ p.2) := by
  letI := μ.toMetricSpace
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Prod.dist_eq]
  calc
    dist (p.1 ⊔ p.2) (q.1 ⊔ q.2) ≤
        (μ ((p.1 ∆ q.1) ⊔ (p.2 ∆ q.2))).toReal :=
      ENNReal.toReal_mono (μ.measure_ne_top _)
        (μ.measure_mono (symmDiff_sup_le_sup p.1 p.2 q.1 q.2))
    _ ≤ (μ (p.1 ∆ q.1) + μ (p.2 ∆ q.2)).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨μ.measure_ne_top _, μ.measure_ne_top _⟩)
        (μ.measure_sup_le _ _)
    _ = dist p.1 q.1 + dist p.2 q.2 := by
      rw [ENNReal.toReal_add (μ.measure_ne_top _) (μ.measure_ne_top _)]
      rfl
    _ ≤ 2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      linarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
        le_max_right (dist p.1 q.1) (dist p.2 q.2)]
    _ = ((2 : NNReal) : ℝ) * max (dist p.1 q.1) (dist p.2 q.2) := by norm_num

private def symmDiffTail (g : ℕ → B) (n : ℕ) : B :=
  ⨆ k, g (n + k) ∆ g (n + k + 1)

private def symmDiffLimit (g : ℕ → B) : B :=
  ⨆ n, g n \ symmDiffTail g n

private theorem symmDiff_add_le_tail (g : ℕ → B) (n k : ℕ) :
    g n ∆ g (n + k) ≤ symmDiffTail g n := by
  induction k with
  | zero => simp
  | succ k ih =>
      apply (symmDiff_triangle (g n) (g (n + k)) (g (n + (k + 1)))).trans
      apply sup_le
      · exact ih
      · simpa [symmDiffTail, Nat.add_assoc] using
          SigmaCompleteBooleanAlgebra.le_iSup_nat
            (fun j ↦ g (n + j) ∆ g (n + j + 1)) k

private theorem symmDiff_core_le_later (g : ℕ → B) {m n : ℕ} (hmn : m ≤ n) :
    g m \ symmDiffTail g m ≤ g n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  apply sdiff_le_iff.2
  calc
    g m ≤ (g m ∆ g (m + k)) ⊔ g (m + k) := le_symmDiff_sup_right _ _
    _ ≤ symmDiffTail g m ⊔ g (m + k) :=
      sup_le_sup_right (symmDiff_add_le_tail g m k) _

private theorem symmDiff_core_le_later_sup_tail
    (g : ℕ → B) {n m : ℕ} (hnm : n ≤ m) :
    g m \ symmDiffTail g m ≤ g n ⊔ symmDiffTail g n := by
  apply sdiff_le.trans
  calc
    g m ≤ (g m ∆ g n) ⊔ g n := le_symmDiff_sup_right _ _
    _ ≤ symmDiffTail g n ⊔ g n := by
      gcongr
      rw [symmDiff_comm]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact symmDiff_add_le_tail g n k
    _ = g n ⊔ symmDiffTail g n := sup_comm _ _

private theorem symmDiff_limit_le_tail (g : ℕ → B) (n : ℕ) :
    g n ∆ symmDiffLimit g ≤ symmDiffTail g n := by
  apply symmDiff_le
  · calc
      g n ≤ symmDiffTail g n ⊔ (g n \ symmDiffTail g n) := le_sup_sdiff
      _ ≤ symmDiffTail g n ⊔ symmDiffLimit g := by
        gcongr
        exact SigmaCompleteBooleanAlgebra.le_sSup_of_countable
          (Set.countable_range fun m ↦ g m \ symmDiffTail g m) ⟨n, rfl⟩
      _ = symmDiffLimit g ⊔ symmDiffTail g n := sup_comm _ _
  · apply SigmaCompleteBooleanAlgebra.sSup_le_of_countable
      (Set.countable_range fun m ↦ g m \ symmDiffTail g m)
    rintro _ ⟨m, rfl⟩
    by_cases hmn : m ≤ n
    · exact (symmDiff_core_le_later g hmn).trans le_sup_left
    · exact symmDiff_core_le_later_sup_tail g (Nat.le_of_lt (lt_of_not_ge hmn))

private theorem measure_symmDiffTail_le (g : ℕ → B)
    (h : ∀ n, μ (g n ∆ g (n + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1)) (n : ℕ) :
    μ (symmDiffTail g n) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  calc
    μ (symmDiffTail g n) ≤ ∑' k, μ (g (n + k) ∆ g (n + k + 1)) :=
      μ.measure_iSup_le _
    _ ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ (n + k + 1) :=
      ENNReal.tsum_le_tsum fun k ↦ h (n + k)
    _ = (2⁻¹ : ℝ≥0∞) ^ n := by
      have hterm : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + k + 1) =
          (2⁻¹ : ℝ≥0∞) ^ n * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
        intro k
        rw [Nat.add_assoc, pow_add]
      simp_rw [hterm]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      have hcoef : (2⁻¹ : ℝ≥0∞) * (1 - 2⁻¹)⁻¹ = 1 := by
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      rw [hcoef, mul_one]

private theorem tendsto_symmDiffLimit (g : ℕ → B)
    (h : ∀ n, μ (g n ∆ g (n + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1)) :
    (letI := μ.toMetricSpace
     Filter.Tendsto g Filter.atTop (nhds (symmDiffLimit g))) := by
  letI := μ.toMetricSpace
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist : ∀ n, dist (g n) (symmDiffLimit g) ≤
      ((2⁻¹ : ℝ≥0∞) ^ n).toReal := by
    intro n
    rw [dist_eq_measure_symmDiff]
    exact (ENNReal.toReal_mono (μ.measure_ne_top _)
      (μ.measure_mono (symmDiff_limit_le_tail g n))).trans
        (ENNReal.toReal_mono (by finiteness) (measure_symmDiffTail_le μ g h n))
  have hpow : Filter.Tendsto (fun n ↦ ((2⁻¹ : ℝ≥0∞) ^ n).toReal)
      Filter.atTop (nhds 0) := by
    simpa [ENNReal.toReal_pow, ENNReal.toReal_inv] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (2 : ℝ)⁻¹) (by positivity) (by norm_num))
  exact squeeze_zero (fun n ↦ dist_nonneg) hdist hpow

/-- A measure algebra is complete for its measure metric. -/
theorem completeSpace :
    letI := μ.toMetricSpace
    CompleteSpace B := by
  letI := μ.toMetricSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hbound_pos : ∀ n, 0 < ((2⁻¹ : ℝ≥0∞) ^ (n + 1)).toReal := by
    intro n
    apply ENNReal.toReal_pos (ENNReal.pow_ne_zero (by norm_num) _)
    finiteness
  obtain ⟨f, hf_mono, hf_bound⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n ↦ ((2⁻¹ : ℝ≥0∞) ^ (n + 1)).toReal) hbound_pos
  let g : ℕ → B := fun n ↦ u (f n)
  have hg_bound : ∀ n, μ (g n ∆ g (n + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
    intro n
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal (μ.measure_ne_top _) (by finiteness)).mp
    simpa [g, dist_eq_measure_symmDiff, symmDiff_comm] using
      hf_bound n (f (n + 1)) (hf_mono.monotone (Nat.le_add_right n 1))
  refine ⟨symmDiffLimit g, tendsto_nhds_of_cauchySeq_of_subseq hu
    hf_mono.tendsto_atTop ?_⟩
  exact tendsto_symmDiffLimit μ g hg_bound

end MeasureAlgebra
