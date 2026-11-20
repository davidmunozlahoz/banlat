/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Examples.Ellp.Sum
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Weak convergence in real `ℓ¹`

Every weakly convergent sequence in real `ℓ¹` converges in norm.
-/

open Filter Finset
open scoped Topology ENNReal NNReal lp

noncomputable section

namespace lp

/-- Given a real sequence `(c i)` with `|c i| ≤ 1` for every `i`, define the
continuous linear functional on `ℓ¹(ℕ, ℝ)` that sends `x` to
`∑' i, c i * x i`. -/
private def boundedPairing (c : ℕ → ℝ) (hc : ∀ i, ‖c i‖ ≤ 1) :
    StrongDual ℝ ℓ¹(ℕ, ℝ) :=
  lp.dualPairing ∞ 1 (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ)
    (K := 1) (fun _ ↦ ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
    ⟨c, memℓp_infty_iff.mpr ⟨1, fun _ ⟨i, hi⟩ ↦ hi ▸ hc i⟩⟩

/-- If `|c i| ≤ 1` for every `i`, then the functional on `ℓ¹(ℕ, ℝ)` given by
`x ↦ ∑' i, c i * x i` has operator norm at most one. -/
private lemma norm_boundedPairing_le (c : ℕ → ℝ) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖boundedPairing c hc‖ ≤ 1 := by
  unfold boundedPairing
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (lp.norm_dualPairing (p := ∞) (q := 1) (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ)
        (K := 1) (fun _ ↦ ContinuousLinearMap.opNorm_mul_le ℝ ℝ))
      (lp.norm_le_of_forall_le zero_le_one hc) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Applied to the sequence with value `a` at index `i` and zero elsewhere,
`boundedPairing c hc` returns `c i * a`. -/
private lemma boundedPairing_single (c : ℕ → ℝ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (i : ℕ) (a : ℝ) : boundedPairing c hc (lp.single 1 i a) = c i * a := by
  change (∑' j : ℕ, c j * (lp.single 1 i a : ℓ¹(ℕ, ℝ)) j) = c i * a
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_eq_of_ne hj]

/-- Let `(u n)` be a weakly null sequence in `ℓ¹(ℕ, ℝ)` and fix `N`.
Project each `u n` onto the first `N` coordinates. The resulting sequence
`(headProjection N (u n))` converges to zero in `ℓ¹` norm as `n → ∞`. -/
private lemma tendsto_headProjection_zero {u : ℕ → ℓ¹(ℕ, ℝ)}
    (hu : ∀ φ : StrongDual ℝ ℓ¹(ℕ, ℝ), Tendsto (fun n ↦ φ (u n)) atTop (𝓝 0))
    (N : ℕ) : Tendsto (fun n ↦ headProjection N (u n)) atTop (𝓝 0) := by
  have hcoord (i : ℕ) : Tendsto (fun n ↦ u n i) atTop (𝓝 0) :=
    hu (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 1 i)
  have hsingle (i : ℕ) : Tendsto
      (fun n ↦ (lp.single 1 i (u n i) : ℓ¹(ℕ, ℝ))) atTop (𝓝 0) := by
    simpa only [map_zero, Function.comp_def, lp.singleContinuousLinearMap_apply] using
      ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ ℝ) 1 i).continuous.tendsto 0).comp
        (hcoord i)
  simpa only [headProjection, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range N) (fun i _ ↦ hsingle i)

/-- Let `(u n)` be weakly null in `ℓ¹(ℕ, ℝ)`. Suppose there is a fixed
`ε > 0` such that for every `k` some `n ≥ k` satisfies `‖u n‖ ≥ ε`.
Given `k` and `N`, one can choose `n > k` with `‖u n‖ ≥ ε` and an index
`M > N` so that the projections of `u n` onto the coordinates `i < N`
and `i ≥ M` each have norm at most `ε / 8`. -/
private lemma exists_block_step {u : ℕ → ℓ¹(ℕ, ℝ)}
    (hu : ∀ φ : StrongDual ℝ ℓ¹(ℕ, ℝ), Tendsto (fun n ↦ φ (u n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hlarge : ∀ k, ∃ n, k ≤ n ∧ ε ≤ ‖u n‖) (k N : ℕ) :
    ∃ n M, k < n ∧ N < M ∧ ε ≤ ‖u n‖ ∧
      ‖headProjection N (u n)‖ ≤ ε / 8 ∧ ‖u n - headProjection M (u n)‖ ≤ ε / 8 := by
  have hδ : 0 < ε / 8 := div_pos hε (by norm_num)
  have hh : Tendsto (fun n ↦ ‖headProjection N (u n)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (tendsto_headProjection_zero hu N).norm
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hh.eventually (gt_mem_nhds hδ))
  obtain ⟨n, hn, hnorm⟩ := hlarge (max (k + 1) K)
  have ht : Tendsto (fun M ↦ ‖u n - headProjection M (u n)‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ u n) atTop (𝓝 (u n))).sub
        (tendsto_headProjection (u n))).norm
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨n, max (N + 1) M, ?_, ?_, hnorm, (hK n ?_).le, (hM _ (le_max_right _ _)).le⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self k) ((le_max_left _ _).trans hn)
  · exact lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_left _ _)
  · exact (le_max_right _ _).trans hn

/-- Let `(u n)` be weakly null in `ℓ¹(ℕ, ℝ)`. Suppose there is a fixed
`ε > 0` such that for every `j` some `n ≥ j` satisfies `‖u n‖ ≥ ε`.
Then there are strictly increasing sequences `subseq` and `blockEnd` such that each
`u (subseq n)` has norm at least `ε`, and its projections onto the coordinates
`i < blockEnd n` and `i ≥ blockEnd (n + 1)` each have norm at most `ε / 8`. -/
private lemma exists_blocks {u : ℕ → ℓ¹(ℕ, ℝ)}
    (hu : ∀ φ : StrongDual ℝ ℓ¹(ℕ, ℝ), Tendsto (fun n ↦ φ (u n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hlarge : ∀ k, ∃ n, k ≤ n ∧ ε ≤ ‖u n‖) :
    ∃ subseq blockEnd : ℕ → ℕ, StrictMono subseq ∧ StrictMono blockEnd ∧ ∀ n,
      ε ≤ ‖u (subseq n)‖ ∧ ‖headProjection (blockEnd n) (u (subseq n))‖ ≤ ε / 8 ∧
      ‖u (subseq n) - headProjection (blockEnd (n + 1)) (u (subseq n))‖ ≤ ε / 8 := by
  choose nextIndex nextBound hnext using exists_block_step hu hε hlarge
  let q : ℕ → ℕ × ℕ := Nat.rec (0, 0)
    (fun _ s ↦ (nextIndex s.1 s.2, nextBound s.1 s.2))
  refine ⟨fun n ↦ (q (n + 1)).1, fun n ↦ (q n).2, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    exact (hnext (q (n + 1)).1 (q (n + 1)).2).1
  · apply strictMono_nat_of_lt_succ
    intro n
    exact (hnext (q n).1 (q n).2).2.1
  · intro n
    exact (hnext (q n).1 (q n).2).2.2

/-- Let `(v n)` be a sequence in `ℓ¹(ℕ, ℝ)` and let `N` be strictly
increasing. There is a continuous linear functional `φ` of norm at
most one that sends the projection of `v n` onto the coordinates
`N n ≤ i < N (n + 1)` to its `ℓ¹` norm, for every `n`. -/
private lemma exists_block_functional (v : ℕ → ℓ¹(ℕ, ℝ)) {N : ℕ → ℕ}
    (hN : StrictMono N) : ∃ φ : StrongDual ℝ ℓ¹(ℕ, ℝ), ‖φ‖ ≤ 1 ∧ ∀ n,
      φ (headProjection (N (n + 1)) (v n) - headProjection (N n) (v n)) =
        ‖headProjection (N (n + 1)) (v n) - headProjection (N n) (v n)‖ := by
  have hex (i : ℕ) : ∃ n, i < N (n + 1) :=
    ⟨i, (Nat.lt_succ_self i).trans_le (hN.id_le (i + 1))⟩
  let b (i : ℕ) := Nat.find (hex i)
  have hb {n i : ℕ} (hi : i ∈ Finset.Ico (N n) (N (n + 1))) : b i = n := by
    apply (Nat.find_eq_iff (hex i)).mpr
    refine ⟨(Finset.mem_Ico.mp hi).2, fun m hm ↦ ?_⟩
    exact not_lt.mpr ((hN.monotone (Nat.succ_le_of_lt hm)).trans (Finset.mem_Ico.mp hi).1)
  let c (i : ℕ) : ℝ := if 0 ≤ v (b i) i then 1 else -1
  have hc (i : ℕ) : ‖c i‖ ≤ 1 := by dsimp [c]; split_ifs <;> norm_num
  have hsign {n i : ℕ} (hi : i ∈ Finset.Ico (N n) (N (n + 1))) :
      c i * v n i = ‖v n i‖ := by
    dsimp [c]
    rw [hb hi]
    by_cases hx : 0 ≤ v n i
    · simp [hx, abs_of_nonneg hx]
    · simp [hx, abs_of_neg (lt_of_not_ge hx)]
  refine ⟨boundedPairing c hc, norm_boundedPairing_le c hc, fun n ↦ ?_⟩
  have hblock : headProjection (N (n + 1)) (v n) - headProjection (N n) (v n) =
      ∑ i ∈ Finset.Ico (N n) (N (n + 1)), (lp.single 1 i (v n i) : ℓ¹(ℕ, ℝ)) :=
    (Finset.sum_Ico_eq_sub _ (hN.monotone (Nat.le_succ n))).symm
  rw [hblock, map_sum]
  simp_rw [boundedPairing_single]
  have hnorm := lp.norm_sum_single (p := 1) (by simp : 0 < (1 : ENNReal).toReal)
    (v n : ℕ → ℝ) (Finset.Ico (N n) (N (n + 1)))
  simp only [ENNReal.toReal_one, Real.rpow_one] at hnorm
  rw [hnorm]
  exact Finset.sum_congr rfl fun i hi ↦ hsign hi

/-- It is impossible for a weakly null sequence `(u n)` in `ℓ¹(ℕ, ℝ)` to
have infinitely many terms of norm at least a fixed `ε > 0`. -/
private lemma not_cofinal_norm_lower_bound {u : ℕ → ℓ¹(ℕ, ℝ)}
    (hu : ∀ φ : StrongDual ℝ ℓ¹(ℕ, ℝ), Tendsto (fun n ↦ φ (u n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hlarge : ∀ k, ∃ n, k ≤ n ∧ ε ≤ ‖u n‖) : False := by
  obtain ⟨subseq, blockEnd, hsubseq, hblockEnd, hblock⟩ := exists_blocks hu hε hlarge
  obtain ⟨φ, hφ, hφblock⟩ := exists_block_functional (u ∘ subseq) hblockEnd
  let b (n : ℕ) := headProjection (blockEnd (n + 1)) (u (subseq n)) -
    headProjection (blockEnd n) (u (subseq n))
  have herr (n : ℕ) : ‖u (subseq n) - b n‖ ≤ ε / 4 := by
    have heq : u (subseq n) - b n =
        (u (subseq n) - headProjection (blockEnd (n + 1)) (u (subseq n))) +
        headProjection (blockEnd n) (u (subseq n)) := by dsimp [b]; abel_nf
    rw [heq]
    calc
      _ ≤ ‖u (subseq n) - headProjection (blockEnd (n + 1)) (u (subseq n))‖ +
          ‖headProjection (blockEnd n) (u (subseq n))‖ := norm_add_le _ _
      _ ≤ ε / 8 + ε / 8 := add_le_add (hblock n).2.2 (hblock n).2.1
      _ = ε / 4 := by ring
  have hlower (n : ℕ) : ε / 2 ≤ φ (u (subseq n)) := by
    have hnorm : ‖u (subseq n)‖ ≤ ‖u (subseq n) - b n‖ + ‖b n‖ := by
      simpa only [sub_add_cancel] using norm_add_le (u (subseq n) - b n) (b n)
    have hdiff : |φ (u (subseq n)) - φ (b n)| ≤ ‖u (subseq n) - b n‖ := by
      rw [← map_sub]
      simpa only [one_mul, Real.norm_eq_abs] using φ.le_of_opNorm_le hφ (u (subseq n) - b n)
    have hvalue : φ (b n) = ‖b n‖ := hφblock n
    have hleft := (abs_le.mp hdiff).1
    linarith [herr n, (hblock n).1]
  have hlim : Tendsto (fun n ↦ φ (u (subseq n))) atTop (𝓝 0) :=
    (hu φ).comp hsubseq.tendsto_atTop
  have hzero : ε / 2 ≤ 0 := le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ε / 2) atTop (𝓝 (ε / 2))) hlim hlower
  exact (not_le_of_gt (half_pos hε)) hzero

/-- **Schur's theorem**: a weakly null sequence in real `ℓ¹` converges to zero in norm. -/
theorem tendsto_zero_of_weak_tendsto {u : ℕ → ℓ¹(ℕ, ℝ)}
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ ℓ¹(ℕ, ℝ) (u n))
      atTop (𝓝 (toWeakSpace ℝ ℓ¹(ℕ, ℝ) 0))) :
    Tendsto u atTop (𝓝 0) := by
  have hdual (φ : StrongDual ℝ ℓ¹(ℕ, ℝ)) :
      Tendsto (fun n ↦ φ (u n)) atTop (𝓝 0) := by
    have hφ := (WeakBilin.eval_continuous
      (topDualPairing ℝ ℓ¹(ℕ, ℝ)).flip φ).tendsto _ |>.comp hu
    change Tendsto (fun n ↦ φ (u n)) atTop (𝓝 (φ 0)) at hφ
    simpa only [map_zero] using hφ
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra! h
  apply not_cofinal_norm_lower_bound hdual hε
  intro k
  obtain ⟨n, hn, hnorm⟩ := h k
  exact ⟨n, hn, by simpa only [dist_zero_right] using hnorm⟩

/-- If a sequence `(u n)` in `ℓ¹(ℕ, ℝ)` converges weakly to `a`, then
it converges to `a` in norm. -/
lemma tendsto_l1_of_weak_tendsto {u : ℕ → ℓ¹(ℕ, ℝ)} {a : ℓ¹(ℕ, ℝ)}
    (hu : Filter.Tendsto (fun n ↦ toWeakSpace ℝ ℓ¹(ℕ, ℝ) (u n))
      Filter.atTop (𝓝 (toWeakSpace ℝ ℓ¹(ℕ, ℝ) a))) :
    Filter.Tendsto u Filter.atTop (𝓝 a) := by
  have hzero : Filter.Tendsto (fun n ↦ u n - a) Filter.atTop (𝓝 0) := by
    apply lp.tendsto_zero_of_weak_tendsto
    simpa only [map_sub, sub_self, map_zero] using
      hu.sub_const (toWeakSpace ℝ ℓ¹(ℕ, ℝ) a)
  have h := hzero.add_const a
  simpa only [sub_add_cancel, zero_add] using h

end lp
