/-
Authors: Pedro Tradacete
-/

import BanLat.Pi
import BanLat.Preliminaries.PiLpDuality
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Norm estimates for finite families of dual functionals

The scalar ℓᑫ norm of a finite family of functional norms is determined by its
pairings with vector families in the scalar ℓᵖ unit ball, for conjugate exponents.
-/

open scoped ENNReal

noncomputable section

namespace PiLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real functional has values arbitrarily close to its norm on the unit ball.
Changing the sign of an approximate norming vector makes its evaluation positive. -/
private lemma exists_unit_apply_gt (φ : StrongDual ℝ E) {r : ℝ} (hr : r < ‖φ‖) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ r < φ x := by
  obtain ⟨x, hx, hφx⟩ := φ.exists_lt_apply_of_lt_opNorm hr
  by_cases h : 0 ≤ φ x
  · exact ⟨x, hx.le, by simpa only [Real.norm_of_nonneg h] using hφx⟩
  · exact ⟨-x, by simpa only [norm_neg] using hx.le,
      by simpa only [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h)] using hφx⟩

variable {ι : Type*} [Fintype ι] {p q : ℝ≥0∞} [p.HolderConjugate q]

/-- Scalar norming coefficients and approximate unit norming vectors give a family in
the ℓᵖ unit ball whose pairing approaches the scalar ℓᑫ norm of the functional norms. -/
private lemma exists_unit_family_pairing (φ : ι → StrongDual ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ι → E, ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ ≤ 1 ∧
      ‖WithLp.toLp q (fun i ↦ ‖φ i‖)‖ ≤ ∑ i, φ i (x i) + ε := by
  classical
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  obtain ⟨a, ha, hanorm, hval⟩ := exists_nonneg_norming
    (p := q) (q := p) (fun i ↦ ‖φ i‖) (fun i ↦ norm_nonneg _)
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ ↦ ha i
  let δ := ε / (∑ i, a i + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  choose x hx hφx using fun i ↦ exists_unit_apply_gt (φ i) (sub_lt_self _ hδ)
  refine ⟨fun i ↦ a i • x i, ?_, ?_⟩
  · refine le_trans (b := ‖WithLp.toLp p a‖) ?_ hanorm
    apply norm_le_norm_of_abs_le_abs
    intro i
    change |‖a i • x i‖| ≤ |a i|
    rw [abs_norm, norm_smul, Real.norm_of_nonneg (ha i), abs_of_nonneg (ha i)]
    exact (mul_le_mul_of_nonneg_left (hx i) (ha i)).trans_eq (mul_one _)
  · have hsum : (∑ i, ‖φ i‖ * a i) - δ * ∑ i, a i ≤
        ∑ i, φ i (a i • x i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hi := mul_le_mul_of_nonneg_right (hφx i).le (ha i)
      simpa only [sub_mul, mul_sub, map_smul, smul_eq_mul, mul_comm] using hi
    have hδA : δ * ∑ i, a i ≤ ε := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [← hval]
    linarith

/-- A bound on all finite pairings controls the scalar ℓᑫ norm of the functional
norms by the same constant, when the vector families are measured in scalar ℓᵖ norm. -/
theorem norm_dual_family_le_of_sum_apply_le (φ : ι → StrongDual ℝ E) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x : ι → E, ∑ i, φ i (x i) ≤ C * ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖) :
    ‖WithLp.toLp q (fun i ↦ ‖φ i‖)‖ ≤ C := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨x, hx, hφx⟩ := exists_unit_family_pairing (p := p) (q := q) φ hε
  exact hφx.trans (add_le_add ((h x).trans
    ((mul_le_mul_of_nonneg_left hx hC).trans_eq (mul_one C))) le_rfl)

end PiLp
