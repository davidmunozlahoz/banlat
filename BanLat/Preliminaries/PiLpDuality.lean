/-
Authors: Pedro Tradacete
-/

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.MeanInequalities

/-!
# Dual estimates for finite scalar ℓᵖ spaces

Finite scalar Hölder estimates and norming families for conjugate exponents,
including the endpoint pair consisting of one and infinity.
-/

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p q : ℝ≥0∞} [p.HolderConjugate q]

private lemma sum_mul_le_norm_mul_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞)
    (a b : ι → ℝ) :
    ∑ i, a i * b i ≤ ‖WithLp.toLp p a‖ * ‖WithLp.toLp q b‖ := by
  simpa only [PiLp.norm_eq_sum (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).pos,
    PiLp.norm_eq_sum (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).symm.pos,
    PiLp.toLp_apply, Real.norm_eq_abs] using
    Real.inner_le_Lp_mul_Lq Finset.univ a b (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)

private lemma sum_mul_le_norm_top_mul_norm_one (a b : ι → ℝ) :
    ∑ i, a i * b i ≤ ‖WithLp.toLp ∞ a‖ * ‖WithLp.toLp 1 b‖ := by
  simpa only [PiLp.norm_eq_of_L1, PiLp.toLp_apply, Real.norm_eq_abs, Finset.mul_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      (le_abs_self (a i * b i)).trans ((abs_mul (a i) (b i)).trans_le
        (mul_le_mul_of_nonneg_right
          (PiLp.norm_apply_le (WithLp.toLp ∞ a) i) (abs_nonneg (b i)))))

/-- Hölder's inequality for a finite scalar pairing, including the exponents
one and infinity. -/
theorem sum_mul_le_norm_mul (a b : ι → ℝ) :
    ∑ i, a i * b i ≤ ‖WithLp.toLp p a‖ * ‖WithLp.toLp q b‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    exact sum_mul_le_norm_top_mul_norm_one a b
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    simpa only [mul_comm] using sum_mul_le_norm_top_mul_norm_one b a
  · exact sum_mul_le_norm_mul_of_ne_top hp hq a b

private lemma exists_nonneg_norming_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ ‖WithLp.toLp q b‖ ≤ 1 ∧
      ∑ i, a i * b i = ‖WithLp.toLp p a‖ := by
  obtain ⟨b, hb, hval⟩ := (NNReal.isGreatest_Lp Finset.univ
    (fun i ↦ NNReal.mk (a i) (ha i)) (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)).1
  refine ⟨fun i ↦ b i, fun i ↦ (b i).coe_nonneg, ?_, ?_⟩
  · simpa only [PiLp.norm_eq_sum (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).symm.pos,
      PiLp.toLp_apply, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      NNReal.coe_rpow, NNReal.coe_sum, NNReal.coe_one] using
      NNReal.coe_le_coe.mpr (NNReal.rpow_le_one hb
        (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).symm.one_div_pos.le)
  · rw [PiLp.norm_eq_sum (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).pos]
    simp only [Real.norm_of_nonneg (ha _)]
    simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_rpow] using
      congrArg NNReal.toReal hval

private lemma exists_nonneg_norming_one (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ ‖WithLp.toLp ∞ b‖ ≤ 1 ∧
      ∑ i, a i * b i = ‖WithLp.toLp 1 a‖ := by
  refine ⟨fun _ ↦ 1, fun _ ↦ zero_le_one, ?_, ?_⟩
  · simpa using (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun _ ↦ by norm_num)
  · simp [PiLp.norm_eq_of_L1, Real.norm_of_nonneg (ha _)]

private lemma exists_nonneg_norming_top (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ ‖WithLp.toLp 1 b‖ ≤ 1 ∧
      ∑ i, a i * b i = ‖WithLp.toLp ∞ a‖ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have hz : a = 0 := funext fun i ↦ isEmptyElim i
    exact ⟨0, by simp, by simp, by simp [hz]⟩
  | inr h =>
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
    refine ⟨fun i ↦ if i = j then 1 else 0,
      fun i ↦ ite_nonneg zero_le_one le_rfl, ?_, ?_⟩
    · simp [PiLp.norm_eq_of_L1, apply_ite abs]
    · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        PiLp.norm_toLp]
      apply le_antisymm
      · exact (Real.norm_of_nonneg (ha j)).symm.le.trans (norm_le_pi_norm a j)
      · exact (pi_norm_le_iff_of_nonneg (ha j)).2 fun i ↦ by
          simpa only [Real.norm_of_nonneg (ha i)] using hj i (Finset.mem_univ i)

/-- A nonnegative scalar family `a_i` admits a nonnegative family `b_i` with `(∑ |b_i|^q)^{1/q} ≤ 1`
 and `∑ a_i * b_i = (∑ |a_i|^p)^{1/p}` where `p` and `q` are conjugate exponents, including one
 and infinity. -/
theorem exists_nonneg_norming (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ ‖WithLp.toLp q b‖ ≤ 1 ∧
      ∑ i, a i * b i = ‖WithLp.toLp p a‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    exact exists_nonneg_norming_top a ha
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    exact exists_nonneg_norming_one a ha
  · exact exists_nonneg_norming_of_ne_top hp hq a ha

private lemma norm_toLp_eq_of_norm_eq {r : ℝ≥0∞} (hr : r ≠ 0)
    {a b : ι → ℝ} (h : ∀ i, ‖a i‖ = ‖b i‖) :
    ‖WithLp.toLp r a‖ = ‖WithLp.toLp r b‖ := by
  rcases eq_or_ne r ∞ with rfl | hr_top
  · simp only [PiLp.norm_eq_ciSup, h]
  · simp only [PiLp.norm_eq_sum (ENNReal.toReal_pos hr hr_top), h]

/-- Every finite scalar family `a_i` admits a family `b_i` with signs chosen to match the
original coordinates, `(∑ |b_i|^q)^{1/q} ≤ 1` and `∑ a_i * b_i = (∑ |a_i|^p)^{1/p}` where `p`
and `q` are conjugate exponents, including one and infinity. -/
theorem exists_norming (a : ι → ℝ) :
    ∃ b : ι → ℝ, ‖WithLp.toLp q b‖ ≤ 1 ∧
      ∑ i, a i * b i = ‖WithLp.toLp p a‖ := by
  classical
  obtain ⟨b, -, hb_norm, hb_value⟩ :=
    exists_nonneg_norming (p := p) (q := q) (fun i ↦ |a i|) (fun i ↦ abs_nonneg _)
  let c (i : ι) := if 0 ≤ a i then b i else -b i
  refine ⟨c, ?_, ?_⟩
  · rw [norm_toLp_eq_of_norm_eq (ENNReal.HolderConjugate.ne_zero q p)
      (b := b) (fun i ↦ by simp only [c]; split_ifs <;> simp)]
    exact hb_norm
  · have hc (i : ι) : a i * c i = |a i| * b i := by
      by_cases hi : 0 ≤ a i
      · simp [c, hi, abs_of_nonneg hi]
      · simp [c, hi, abs_of_neg (lt_of_not_ge hi)]
    rw [Finset.sum_congr rfl (fun i _ ↦ hc i), hb_value]
    exact norm_toLp_eq_of_norm_eq (ENNReal.HolderConjugate.ne_zero p q)
      (fun i ↦ by simp)

end PiLp
