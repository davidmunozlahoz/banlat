/-
Authors: Pedro Tradacete
-/

import BanLat.KBSpace.Basic
import BanLat.OrderContinuous.MeyerNieberg
import BanLat.SequenceCopies
import BanLat.Tactic.LLexpr

/-!
# The null-sequence obstruction to the KB property

A Banach lattice containing no closed vector sublattice isomorphic to `c₀` is a KB-space.

The KB-property can be checked on bounded increasing positive sequences.
-/

noncomputable section

open Set Filter
open scoped ZeroAtInfty

namespace BanachLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

omit [BanachLattice X] in
/-- The set of finite sums of disjoint positive vectors has the same upper bounds as the
individual vectors. -/
private lemma disjoint_sum_le {v : ℕ → X} (hv : ∀ n, 0 ≤ v n)
    (hd : Pairwise fun n m ↦ IsVLDisjoint (v n) (v m)) {w : X} (hw : 0 ≤ w)
    (hle : ∀ n, v n ≤ w) (s : Finset ℕ) : ∑ n ∈ s, v n ≤ w := by
  induction s using Finset.induction_on with
  | empty => simpa using hw
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, add_eq_sup_of_isVLDisjoint_of_nonneg (hv n)
        (Finset.sum_nonneg fun m _ ↦ hv m)
        (IsVLDisjoint.finset_sum_right fun m hm ↦ hd (ne_of_mem_of_not_mem hm hn).symm)]
      exact sup_le (hle n) ih

/-- If a Banach lattice does not contain a closed vector sublattice isomorphic to `c₀`, its norm
is order continuous. -/
theorem isOrderContinuousNorm_of_no_c0
    (h : ¬ ContainsLatticeCopy X C₀(ℕ, ℝ)) : IsOrderContinuousNorm X := by
  by_contra hn
  obtain ⟨v, w, ε, hε, hv, hd, hle, hnorm⟩ :=
    exists_disjoint_norm_ge_of_not_isOrderContinuousNorm hn
  refine h (containsLatticeCopy_c0_of_disjoint hv hd hε hnorm (C := ‖w‖) fun s ↦ ?_)
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (Finset.sum_nonneg fun n _ ↦ hv n),
    abs_of_nonneg ((hv 0).trans (hle 0))]
  exact disjoint_sum_le hv hd ((hv 0).trans (hle 0)) hle s

omit [BanachLattice X] in
/-- A positive vector below `e` and disjoint from the part of `e` above `t`
must already lie below `t`. -/
private lemma le_of_inf_posPart_zero (a e t : X) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (he : a ≤ e) (hz : a ⊓ (e - t)⁺ = 0) : a ≤ t := by
  have h₁ : (a - t)⁺ ≤ a := sup_le (sub_le_self _ ht) ha
  have h₂ : (a - t)⁺ ≤ (e - t)⁺ := posPart_mono (sub_le_sub_right he t)
  have h : (a - t)⁺ ≤ 0 := hz ▸ le_inf h₁ h₂
  exact sub_nonpos.mp (posPart_eq_zero.mp (le_antisymm h (posPart_nonneg _)))

/-- The overlap of the part of `q` above `K • e` with `e` is bounded by `K⁻¹ • q`. -/
private lemma cutoff_le (q e : X) (hq : 0 ≤ q) (he : 0 ≤ e) (K : ℝ) (hK : 0 < K) :
    (q - K • e)⁺ ⊓ e ≤ K⁻¹ • q := by
  have hi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK.le
  refine le_of_inf_posPart_zero _ e _ (le_inf (posPart_nonneg _) he)
    (smul_nonneg hi hq) inf_le_right ?_
  apply inf_eq_zero_of_isVLDisjoint (le_inf (posPart_nonneg _) he) (posPart_nonneg _)
  exact (isVLDisjoint_posPart_sub_smul q e hK).mono_left
    (by rw [abs_of_nonneg (le_inf (posPart_nonneg _) he),
      abs_of_nonneg (posPart_nonneg _)]; exact inf_le_left)

/-- The overlap of an increment with `e` is controlled by the corresponding
increment truncated at `K • e` and a tail of size `K⁻¹ • q`. -/
private lemma overlap_le (p q e : X) (hp : 0 ≤ p) (hpq : p ≤ q) (he : 0 ≤ e)
    (K : ℝ) (hK : 0 < K) :
    (q - p) ⊓ e ≤ (q ⊓ (K • e) - p ⊓ (K • e)) + K⁻¹ • q := by
  have hr : 0 ≤ q ⊓ (K • e) - p ⊓ (K • e) :=
    sub_nonneg.mpr (inf_le_inf_right _ hpq)
  have hdiff : q - p ≤ (q ⊓ (K • e) - p ⊓ (K • e)) + (q - K • e)⁺ := by llarith
  have h : (q - p) ⊓ e ≤ (q ⊓ (K • e) - p ⊓ (K • e)) + ((q - K • e)⁺ ⊓ e) := by
    rw [add_inf]
    exact le_inf (inf_le_left.trans hdiff) (inf_le_right.trans (le_add_of_nonneg_left hr))
  exact h.trans (add_le_add le_rfl (cutoff_le q e (hp.trans hpq) he K hK))

/-- For `0 ≤ p ≤ q`, `0 ≤ e`, and `K > 0`, the norm of `(q - p) ⊓ e` is bounded by
the norm of the difference between the truncations `q ⊓ (K • e)` and `p ⊓ (K • e)`,
plus `‖q‖ / K`, an error uniformly small for norm-bounded `q` as `K` grows. -/
private lemma norm_overlap_le (p q e : X) (hp : 0 ≤ p) (hpq : p ≤ q) (he : 0 ≤ e)
    (K : ℝ) (hK : 0 < K) :
    ‖(q - p) ⊓ e‖ ≤ ‖q ⊓ (K • e) - p ⊓ (K • e)‖ + K⁻¹ * ‖q‖ := by
  have hn : ‖(q - p) ⊓ e‖ ≤ ‖(q ⊓ (K • e) - p ⊓ (K • e)) + K⁻¹ • q‖ :=
    norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (le_inf (sub_nonneg.mpr hpq) he),
        abs_of_nonneg (add_nonneg (sub_nonneg.mpr (inf_le_inf_right _ hpq))
          (smul_nonneg (inv_nonneg.mpr hK.le) (hp.trans hpq)))]
      exact overlap_le p q e hp hpq he K hK)
  simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hK.le)] using
    hn.trans (norm_add_le _ _)

/-- In an order-continuous Banach lattice, sufficiently late increments of a
norm bounded increasing positive sequence have small overlap with any fixed vector. -/
private lemma overlap_small [IsOrderContinuousNorm X]
    (u : ℕ → X) (hu : ∀ n, 0 ≤ u n) (hm : Monotone u)
    (C : ℝ) (hC : ∀ n, ‖u n‖ ≤ C) (e : X) (he : 0 ≤ e)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ a, ‖(u b - u a) ⊓ e‖ < ε := by
  have hC0 : 0 ≤ C := (norm_nonneg (u 0)).trans (hC 0)
  let K := (2 * C + 1) / ε
  have hK : 0 < K := div_pos (by linarith) hε
  have hsmall : K⁻¹ * C < ε / 2 := by
    rw [inv_mul_eq_div, div_lt_iff₀ hK]
    dsimp only [K]
    field_simp
    nlinarith
  obtain ⟨z, _, hz⟩ := tendsto_of_monotone_bddAbove
    (u := fun n ↦ u n ⊓ K • e) (fun _ _ h ↦ inf_le_inf_right _ (hm h))
    ⟨K • e, fun _ ⟨n, hn⟩ ↦ hn ▸ inf_le_right⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hz.cauchySeq (ε / 2) (half_pos hε)
  refine ⟨N, fun a ha b hab ↦ ?_⟩
  have ht : ‖u b ⊓ K • e - u a ⊓ K • e‖ < ε / 2 :=
    (dist_eq_norm _ _ : _ = ‖u b ⊓ K • e - u a ⊓ K • e‖) ▸ hN b (ha.trans hab) a ha
  have hs : K⁻¹ * ‖u b‖ < ε / 2 :=
    (mul_le_mul_of_nonneg_left (hC b) (inv_nonneg.mpr hK.le)).trans_lt hsmall
  exact (norm_overlap_le (u a) (u b) e (hu a) (hm hab) he K hK).trans_lt
    (by linarith)

/-- `ε / 2^{n + m + 3}`. -/
private def overlapAllowance (ε : ℝ) (n m : ℕ) : ℝ :=
  ε / 8 * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ m

private lemma overlapAllowance_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    0 < overlapAllowance ε n m := by
  unfold overlapAllowance
  positivity

private lemma overlapAllowance_comm (ε : ℝ) (n m : ℕ) :
    overlapAllowance ε n m = overlapAllowance ε m n := by
  unfold overlapAllowance
  ring

private lemma overlapAllowance_antitone {ε : ℝ} (hε : 0 ≤ ε) {n m k l : ℕ}
    (hn : n ≤ k) (hm : m ≤ l) : overlapAllowance ε k l ≤ overlapAllowance ε n m := by
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn)
      (div_nonneg hε (by norm_num)))
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm)
    (by positivity) (by positivity)

/-- Any finite collection of increasing blocks can be followed by a large
increment whose overlap with each earlier block is sufficiently small. -/
private lemma exists_next_block [IsOrderContinuousNorm X]
    (u : ℕ → X) (hu : ∀ n, 0 ≤ u n) (hm : Monotone u)
    (C : ℝ) (hC : ∀ n, ‖u n‖ ≤ C) (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ N : ℕ, ∃ M ≥ N, ε ≤ ‖u M - u N‖)
    (s : Finset (ℕ × ℕ × ℕ)) (hs : ∀ z ∈ s, z.2.1 ≤ z.2.2) :
    ∃ y : ℕ × ℕ × ℕ, (y.2.1 ≤ y.2.2 ∧ ε ≤ ‖u y.2.2 - u y.2.1‖) ∧
      ∀ z ∈ s, z.1 < y.1 ∧ z.2.2 ≤ y.2.1 ∧
        ‖(u z.2.2 - u z.2.1) ⊓ (u y.2.2 - u y.2.1)‖ ≤ overlapAllowance ε z.1 y.1 := by
  let k := s.sup Prod.fst + 1
  let threshold (z : ℕ × ℕ × ℕ) := (overlap_small u hu hm C hC
    |u z.2.2 - u z.2.1| (abs_nonneg _) _ (overlapAllowance_pos hε z.1 k)).choose
  let A := max (s.sup fun z ↦ z.2.2) (s.sup threshold)
  obtain ⟨B, hAB, hnorm⟩ := hbad A
  refine ⟨(k, A, B), ⟨hAB, hnorm⟩, fun z hz ↦ ⟨?_, ?_, ?_⟩⟩
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) hz)
  · exact (Finset.le_sup (f := fun z ↦ z.2.2) hz).trans (le_max_left _ _)
  · have ht : threshold z ≤ A := (Finset.le_sup (f := threshold) hz).trans (le_max_right _ _)
    have hsmall := (overlap_small u hu hm C hC |u z.2.2 - u z.2.1| (abs_nonneg _)
      _ (overlapAllowance_pos hε z.1 k)).choose_spec A ht B hAB
    simpa only [abs_of_nonneg (sub_nonneg.mpr (hm (hs z hz))), inf_comm] using hsmall.le

/-- A non-Cauchy increasing sequence has successive large blocks with pairwise
overlaps bounded by a summable geometric family. -/
private lemma exists_blocks [IsOrderContinuousNorm X]
    (u : ℕ → X) (hu : ∀ n, 0 ≤ u n) (hm : Monotone u)
    (C : ℝ) (hC : ∀ n, ‖u n‖ ≤ C) (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ N : ℕ, ∃ M ≥ N, ε ≤ ‖u M - u N‖) :
    ∃ a b : ℕ → ℕ, (∀ n, a n ≤ b n) ∧
      (∀ n m, n < m → b n ≤ a m) ∧ (∀ n, ε ≤ ‖u (b n) - u (a n)‖) ∧
      ∀ n m, n ≠ m →
        ‖(u (b n) - u (a n)) ⊓ (u (b m) - u (a m))‖ ≤ overlapAllowance ε n m := by
  obtain ⟨f, hf, hr⟩ := exists_seq_of_forall_finset_exists
    (fun z : ℕ × ℕ × ℕ ↦ z.2.1 ≤ z.2.2 ∧ ε ≤ ‖u z.2.2 - u z.2.1‖)
    (fun z y ↦ z.1 < y.1 ∧ z.2.2 ≤ y.2.1 ∧
      ‖(u z.2.2 - u z.2.1) ⊓ (u y.2.2 - u y.2.1)‖ ≤ overlapAllowance ε z.1 y.1)
    (fun s hs ↦ exists_next_block u hu hm C hC ε hε hbad s (fun z hz ↦ (hs z hz).1))
  have hmono : StrictMono fun n ↦ (f n).1 := fun _ _ h ↦ (hr _ _ h).1
  have hbound (n m : ℕ) (h : n < m) :
      ‖(u (f n).2.2 - u (f n).2.1) ⊓ (u (f m).2.2 - u (f m).2.1)‖ ≤
        overlapAllowance ε n m :=
    (hr n m h).2.2.trans (overlapAllowance_antitone hε.le (hmono.id_le n) (hmono.id_le m))
  refine ⟨fun n ↦ (f n).2.1, fun n ↦ (f n).2.2, fun n ↦ (hf n).1,
    fun n m h ↦ (hr n m h).2.1, fun n ↦ (hf n).2, fun n m h ↦ ?_⟩
  rcases lt_or_gt_of_ne h with h | h
  · exact hbound n m h
  · simpa only [inf_comm, overlapAllowance_comm ε m n] using hbound m n h

omit [BanachLattice X] in
/-- Successive blocks of an increasing positive sequence have finite sums
bounded above by a later term of the sequence. -/
private lemma block_sums_le (u : ℕ → X) (hu : ∀ n, 0 ≤ u n) (hm : Monotone u)
    (a b : ℕ → ℕ) (hab : ∀ n, a n ≤ b n)
    (hba : ∀ n m, n < m → b n ≤ a m) (s : Finset ℕ) :
    ∑ n ∈ s, (u (b n) - u (a n)) ≤ u (a (s.sup id + 1)) := by
  have hp (n : ℕ) : 0 ≤ u (b n) - u (a n) := sub_nonneg.mpr (hm (hab n))
  have H (N : ℕ) : ∑ n ∈ Finset.range N, (u (b n) - u (a n)) ≤ u (a N) := by
    induction N with
    | zero => simpa using hu (a 0)
    | succ N ih =>
        rw [Finset.sum_range_succ]
        exact ((add_le_add ih (le_refl (u (b N) - u (a N)))).trans_eq (add_sub_cancel _ _)).trans
          (hm (hba N (N + 1) (Nat.lt_succ_self N)))
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (fun n hn ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)))
    (fun n _ _ ↦ hp n)).trans (H _)

private lemma summable_overlapAllowance (ε : ℝ) (n : ℕ) :
    Summable (overlapAllowance ε n) :=
  summable_geometric_two.mul_left (ε / 8 * (1 / 2 : ℝ) ^ n)

private lemma tsum_overlapAllowance_le {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    ∑' m, overlapAllowance ε n m ≤ ε / 4 := by
  simp only [overlapAllowance, tsum_mul_left, tsum_geometric_two]
  nlinarith [pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)]

private lemma exists_overlap_correction {d : ℕ → X} (hd : ∀ n, 0 ≤ d n)
    {ε : ℝ} (hε : 0 < ε)
    (hover : ∀ n m, n ≠ m → ‖d n ⊓ d m‖ ≤ overlapAllowance ε n m) :
    ∃ r : ℕ → X, (∀ n, 0 ≤ r n) ∧ (∀ n, ‖r n‖ ≤ ε / 4) ∧
      ∀ n m, n ≠ m → d n ⊓ d m ≤ r n := by
  let o (n m : ℕ) : X := if m = n then 0 else d n ⊓ d m
  have ho (n m : ℕ) : 0 ≤ o n m :=
    ite_nonneg le_rfl (le_inf (hd n) (hd m))
  have hob (n m : ℕ) : ‖o n m‖ ≤ overlapAllowance ε n m := by
    dsimp only [o]
    split_ifs with h
    · simpa only [norm_zero] using (overlapAllowance_pos hε n m).le
    · exact hover n m (Ne.symm h)
  have hsum (n : ℕ) : Summable (fun m ↦ ‖o n m‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hob n) (summable_overlapAllowance ε n)
  refine ⟨fun n ↦ ∑' m, o n m, fun n ↦ tsum_nonneg (ho n), ?_, ?_⟩
  · exact fun n ↦ (norm_tsum_le_tsum_norm (hsum n)).trans
      (((hsum n).tsum_le_tsum (hob n) (summable_overlapAllowance ε n)).trans
        (tsum_overlapAllowance_le hε.le n))
  · exact fun n m h ↦ by simpa only [o, ite_eq_right (Ne.symm h)] using
      (hsum n).of_norm.le_tsum m (fun k _ ↦ ho n k)

omit [BanachLattice X] in
private lemma disjoint_positive_remainders {d r : ℕ → X}
    (hover : ∀ n m, n ≠ m → d n ⊓ d m ≤ r n) :
    Pairwise fun n m ↦ IsVLDisjoint (d n - r n)⁺ (d m - r m)⁺ := by
  have hle (n m : ℕ) (h : n ≠ m) : (d n - r n)⁺ ≤ (d n - d m)⁺ := by
    simpa only [sub_inf_eq_posPart, posPart_of_nonneg (posPart_nonneg _)] using
      posPart_mono (sub_le_sub_left (hover n m h) (d n))
  intro n m h
  have hb : IsVLDisjoint (d n - d m)⁺ (d m - d n)⁺ := by
    simpa only [negPart_def, neg_sub, ← posPart_def] using
      isVLDisjoint_posPart_negPart (d n - d m)
  exact (hb.mono_left (show |(d n - r n)⁺| ≤ |(d n - d m)⁺| from
    by simpa only [abs_of_nonneg (posPart_nonneg _)] using hle n m h)).mono_right
      (by simpa only [abs_of_nonneg (posPart_nonneg _)] using hle m n h.symm)

private lemma norm_posPart_sub_ge {d r : X} (hd : 0 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hdn : ε ≤ ‖d‖) (hrn : ‖r‖ ≤ ε / 4) :
    ε / 2 ≤ ‖(d - r)⁺‖ := by
  have hn : ‖d - (d - r)⁺‖ ≤ ‖r‖ := by
    simpa only [← posPart_def, posPart_of_nonneg hd, sub_sub_cancel] using
      norm_sup_sub_sup_le_norm d (d - r) 0
  linarith [norm_le_norm_sub_add d (d - r)⁺]

/-- In an order continuous Banach lattice, a bounded increasing positive sequence that is not
Cauchy yields a disjoint positive sequence with norm bounded finite sums and norms bounded away
from zero. -/
private lemma exists_disjoint_of_not_cauchy [IsOrderContinuousNorm X]
    (u : ℕ → X) (hu : ∀ n, 0 ≤ u n) (hm : Monotone u)
    (C : ℝ) (hC : ∀ n, ‖u n‖ ≤ C) (hnc : ¬ CauchySeq u) :
    ∃ (v : ℕ → X) (ε : ℝ), 0 < ε ∧ (∀ n, 0 ≤ v n) ∧
      Pairwise (fun n m ↦ IsVLDisjoint (v n) (v m)) ∧
      (∀ n, ε ≤ ‖v n‖) ∧ ∀ s : Finset ℕ, ‖∑ n ∈ s, v n‖ ≤ C := by
  rw [Metric.cauchySeq_iff'] at hnc
  push Not at hnc
  obtain ⟨ε, hε, hbad⟩ := hnc
  obtain ⟨a, b, hab, hba, hnorm, hover⟩ := exists_blocks u hu hm C hC ε hε
    (by simpa only [dist_eq_norm] using hbad)
  let d (n : ℕ) := u (b n) - u (a n)
  have hd (n : ℕ) : 0 ≤ d n := sub_nonneg.mpr (hm (hab n))
  obtain ⟨r, hr, hrnorm, hrle⟩ := exists_overlap_correction hd hε hover
  let v (n : ℕ) := (d n - r n)⁺
  have hv (n : ℕ) : 0 ≤ v n := posPart_nonneg _
  have hvle (n : ℕ) : v n ≤ d n := sup_le (sub_le_self _ (hr n)) (hd n)
  refine ⟨v, ε / 2, half_pos hε, hv, disjoint_positive_remainders hrle,
    fun n ↦ norm_posPart_sub_ge (hd n) hε (hnorm n) (hrnorm n), fun s ↦ ?_⟩
  have hs : (∑ n ∈ s, v n) ≤ u (a (s.sup id + 1)) :=
    (Finset.sum_le_sum fun n _ ↦ hvle n).trans (block_sums_le u hu hm a b hab hba s)
  refine (norm_le_norm_of_abs_le_abs ?_).trans (hC (a (s.sup id + 1)))
  simpa only [abs_of_nonneg (Finset.sum_nonneg fun n _ ↦ hv n), abs_of_nonneg (hu _)] using hs

omit [IsOrderedAddMonoid X] [BanachLattice X] in
/-- If every bounded increasing positive sequence is Cauchy, an increasing
bounded net cannot have uniformly large increments beyond every index. -/
private lemma eventually_small_increments_of_sequences
    (h : ∀ u : ℕ → X, Monotone u → (∀ n, 0 ≤ u n) →
      Bornology.IsBounded (range u) → CauchySeq u)
    {ι : Type*} [Preorder ι] [Nonempty ι] {f : ι → X}
    (hm : Monotone f) (hp : ∀ i, 0 ≤ f i) (hb : Bornology.IsBounded (range f))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i : ι, ∀ j ≥ i, dist (f j) (f i) < ε := by
  by_contra hn
  push Not at hn
  choose next hle hdist using hn
  let ψ : ℕ → ι := fun n ↦ Nat.rec (Classical.choice (inferInstance : Nonempty ι))
    (fun _ i ↦ next i) n
  have hψ : Monotone ψ := monotone_nat_of_le_succ fun n ↦ hle (ψ n)
  have hg : CauchySeq (fun n ↦ f (ψ n)) :=
    h _ (hm.comp hψ) (fun n ↦ hp (ψ n)) (hb.subset (range_comp_subset_range _ _))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hg ε hε
  exact (not_lt_of_ge (hdist (ψ N))) (hN (N + 1) (Nat.le_succ N))

/-- Cauchy convergence for bounded increasing positive sequences implies the
KB property formulated with arbitrary directed nets. -/
theorem isKbSpace_of_monotone_sequences
    (h : ∀ u : ℕ → X, Monotone u → (∀ n, 0 ≤ u n) →
      Bornology.IsBounded (range u) → CauchySeq u) : IsKbSpace X := by
  refine ⟨fun {ι} _ _ _ {f} hm hp hb ↦ CompleteSpace.complete ?_⟩
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε ↦ ?_⟩
  obtain ⟨i, hi⟩ := eventually_small_increments_of_sequences h hm hp hb (ε / 2) (half_pos hε)
  refine ⟨f '' Ici i, ?_, ?_⟩
  · change f ⁻¹' (f '' Ici i) ∈ (atTop : Filter ι)
    exact mem_of_superset (eventually_ge_atTop i) fun j hj ↦ ⟨j, hj, rfl⟩
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
    exact (dist_triangle (f j) (f i) (f k)).trans_lt
      (by rw [dist_comm (f i) (f k)]; linarith [hi j hj, hi k hk])

/-- A Banach lattice containing no closed vector sublattice isomorphic to
`c₀` is a KB-space. -/
theorem isKbSpace_of_not_containsLatticeCopy_c0
    (h : ¬ ContainsLatticeCopy X C₀(ℕ, ℝ)) : IsKbSpace X := by
  let := isOrderContinuousNorm_of_no_c0 h
  refine isKbSpace_of_monotone_sequences fun u hm hu hb ↦ ?_
  by_contra hnc
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  obtain ⟨v, ε, hε, hv, hd, hnorm, hs⟩ :=
    exists_disjoint_of_not_cauchy u hu hm C (fun n ↦ hC _ (mem_range_self n)) hnc
  exact h (containsLatticeCopy_c0_of_disjoint hv hd hε hnorm hs)

end BanachLattice
