import BanLat.Probability.ConvergenceInMeasure
import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.IndependentFinSums
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Infinite sums of independent symmetric stable random variables

This file studies infinite linear combinations of independent symmetric `q`-stable random
variables. If the coefficients `{aₖ}ₖ` satisfy that `∑ₖ |aₖ|^q < ∞` then the finite partial
sums `∑ 0 ≤ k ≤ N, aₖXₖ` converge in probability to a symmetric `q`-stable random variable
with scale parameter `c * ∑' n, ‖a n‖₊ ^ q`. -/

open MeasureTheory

open scoped BigOperators NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {q : ℝ} {c : ℝ≥0}

namespace iIndepFun

/-- Let `{Xₖ}ₖ` be a sequence of independent and identically distributed symmetric
`q`-stable random variables with scale `c`. Let `{aₖ}ₖ` be such  that `∑ₖ ∣aₖ∣ ^ q < ∞`
and `Y` be a random variable such that `∑ₖ aₖXₖ` converges in probability to `Y`.
Then `Y` is a symmetric `q`-stable random variable with scale parameter `c · ∑ₖ ∣aₖ∣^q`. -/
lemma hasSymmetricStableLaw_of_tendstoInMeasure_sum_range_mul
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (h_indep : iIndepFun X P)
    (hX : ∀ n, HasSymmetricStableLaw (X n) q c P)
    (a : ℕ → ℝ)
    (ha : Summable (fun n ↦ ‖a n‖₊ ^ q))
    (hlim : TendstoInMeasure P
      (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y) :
    HasSymmetricStableLaw Y q (c * ∑' n, ‖a n‖₊ ^ q) P := by
  letI := (hX 0).isProbabilityMeasure
  let S : ℕ → Ω → ℝ := fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω
  have hS (N : ℕ) :
      HasSymmetricStableLaw (S N) q (c * ∑ n ∈ Finset.range N, ‖a n‖₊ ^ q) P := by
    simpa [S, Finset.mul_sum] using h_indep.hasSymmetricStableLaw_finset_sum_mul hX
      (hX 0).isSymmetricStable_map.index_pos (hX 0).isSymmetricStable_map.index_le_two
      (Finset.range N) a
  have hlimS : TendstoInMeasure P S Filter.atTop Y := by
    simpa [S] using hlim
  have hdist := hlimS.tendstoInDistribution (fun N ↦ (hS N).aemeasurable)
  refine ⟨⟨(hX 0).isSymmetricStable_map.index_pos,
    (hX 0).isSymmetricStable_map.index_le_two,
    Measure.isProbabilityMeasure_map hdist.aemeasurable_limit, ?_⟩⟩
  intro t
  have ht := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hdist.tendsto) t
  have hsum := ha.hasSum.tendsto_sum_nat
  have hcont : Continuous (fun d : ℝ≥0 ↦
      Complex.exp ((-((c * d : ℝ≥0) : ℝ) * |t| ^ q : ℝ) : ℂ)) := by
    fun_prop
  have htarget := hcont.continuousAt.tendsto.comp hsum
  change Filter.Tendsto (fun N ↦ charFun (P.map (S N)) t) Filter.atTop
    (nhds (charFun (P.map Y) t)) at ht
  simp_rw [(hS _).isSymmetricStable_map.charFun_eq] at ht
  exact (tendsto_nhds_unique htarget ht).symm

/-- Let `{Xₖ}ₖ` be a sequence of independent and identically distributed symmetric
`q`-stable random variables with scale `c`. Let `{aₖ}ₖ` be such that `∑ₖ ∣aₖ∣ ^ q < ∞`.
Then `∑ₖ aₖXₖ` converges in probability to a symmetric `q`-stable random variable
with scale parameter `c · ∑ₖ ∣aₖ∣^q`. -/
lemma exists_tendstoInMeasure_sum_range_mul_of_hasSymmetricStableLaw
    {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X P)
    (hX : ∀ n, HasSymmetricStableLaw (X n) q c P)
    (a : ℕ → ℝ)
    (ha : Summable (fun n ↦ ‖a n‖₊ ^ q)) :
    ∃ Y : Ω → ℝ,
      TendstoInMeasure P
        (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y ∧
      HasSymmetricStableLaw Y q (c * ∑' n, ‖a n‖₊ ^ q) P := by
  classical
  letI := (hX 0).isProbabilityMeasure
  let S : ℕ → Ω → ℝ := fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω
  have hS : ∀ N, AEStronglyMeasurable (S N) P := by
    intro N
    exact (Finset.aemeasurable_fun_sum _ fun i _ ↦
      (hX i).aemeasurable.const_mul (a i)).aestronglyMeasurable
  let u : ℕ → ℝ≥0 := fun i ↦ ‖a i‖₊ ^ q
  have hu : Summable u := by simpa only [u] using ha
  let R : ℕ → ℝ≥0 := fun N ↦ (∑' i, u i) - ∑ i ∈ Finset.range N, u i
  have hsum : Filter.Tendsto (fun N ↦ ∑ i ∈ Finset.range N, u i) Filter.atTop
      (nhds (∑' i, u i)) := by
    simpa only [u] using ha.hasSum.tendsto_sum_nat
  have hcontR : Continuous (fun x : ℝ≥0 ↦ (∑' i, u i) - x) := by fun_prop
  have hR : Filter.Tendsto R Filter.atTop (nhds 0) := by
    simpa only [R, tsub_self] using hcontR.continuousAt.tendsto.comp hsum
  let b : ℕ → ℝ := fun N ↦ (R N : ℝ) ^ q⁻¹
  have hq_inv_pos : 0 < q⁻¹ := inv_pos.mpr (hX 0).isSymmetricStable_map.index_pos
  have hb : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hR
    have hrpow :=
      (Real.continuous_rpow_const hq_inv_pos.le).continuousAt.tendsto.comp hcoe
    simpa only [Function.comp_apply, b, NNReal.coe_zero, Real.zero_rpow hq_inv_pos.ne'] using hrpow
  have hscaled : TendstoInMeasure P (fun N ω ↦ b N * X 0 ω) Filter.atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun N ↦ ((hX 0).aemeasurable.const_mul (b N)).aestronglyMeasurable
    · filter_upwards [] with ω
      simpa using hb.mul_const (X 0 ω)
  let A : ℕ → ℕ → ℝ≥0 := fun n m ↦ ∑ i ∈ Finset.Ico (min n m) (max n m), u i
  have hdist_block (n m : ℕ) (ω : Ω) :
      dist (S n ω) (S m ω) =
        |∑ i ∈ Finset.Ico (min n m) (max n m), a i * X i ω| := by
    rcases le_total n m with hnm | hmn
    · simp only [min_eq_left hnm, max_eq_right hnm, S,
        Finset.sum_Ico_eq_sub _ hnm, Real.dist_eq, abs_sub_comm]
    · simp only [min_eq_right hmn, max_eq_left hmn, S,
        Finset.sum_Ico_eq_sub _ hmn, Real.dist_eq]
  have hA_le_R {N n m : ℕ} (hn : N ≤ n) (hm : N ≤ m) : A n m ≤ R N := by
    change (∑ i ∈ Finset.Ico (min n m) (max n m), u i) ≤
      (∑' i, u i) - ∑ i ∈ Finset.range N, u i
    apply le_tsub_of_add_le_left
    calc
      (∑ i ∈ Finset.range N, u i) +
          ∑ i ∈ Finset.Ico (min n m) (max n m), u i ≤
          (∑ i ∈ Finset.range (min n m), u i) +
            ∑ i ∈ Finset.Ico (min n m) (max n m), u i := by
        gcongr
        exact le_min hn hm
      _ = ∑ i ∈ Finset.range (max n m), u i := by
        rw [Finset.sum_range_add_sum_Ico u (min_le_max)]
      _ ≤ ∑' i, u i := hu.sum_le_tsum _ (fun _ _ ↦ by positivity)
  have hcau_dist : ∀ ε : ℝ, 0 < ε → Filter.Tendsto
      (fun nm : ℕ × ℕ ↦ P {ω | ε ≤ dist (S nm.1 ω) (S nm.2 ω)})
      Filter.atTop (nhds 0) := by
    intro ε hε
    have hscaled_dist := (tendstoInMeasure_iff_dist.mp hscaled) ε hε
    rw [ENNReal.tendsto_atTop_zero] at hscaled_dist ⊢
    intro δ hδ
    obtain ⟨N, hN⟩ := hscaled_dist δ hδ
    refine ⟨(N, N), fun nm hnm ↦ ?_⟩
    have hn : N ≤ nm.1 := hnm.1
    have hm : N ≤ nm.2 := hnm.2
    let d : ℝ := (A nm.1 nm.2 : ℝ) ^ q⁻¹
    have hd_nonneg : 0 ≤ d := Real.rpow_nonneg (A nm.1 nm.2).2 _
    have hb_nonneg : 0 ≤ b N := Real.rpow_nonneg (R N).2 _
    have hd_le : d ≤ b N := by
      apply Real.rpow_le_rpow (A nm.1 nm.2).2
      · exact_mod_cast hA_le_R hn hm
      · exact hq_inv_pos.le
    have hmeasure :
        P {ω | ε ≤ dist (S nm.1 ω) (S nm.2 ω)} =
          P {ω | ε ≤ |d * X 0 ω|} := by
      have hid := (h_indep.identDistrib_finset_sum_mul_of_hasSymmetricStableLaw
        hX (hX 0) (Finset.Ico (min nm.1 nm.2) (max nm.1 nm.2)) a).norm
      have hmem := hid.measure_mem_eq (s := Set.Ici ε) measurableSet_Ici
      have hleft : {ω | ε ≤ dist (S nm.1 ω) (S nm.2 ω)} =
          (fun ω ↦ ‖∑ i ∈ Finset.Ico (min nm.1 nm.2) (max nm.1 nm.2),
            a i * X i ω‖) ⁻¹' Set.Ici ε := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, Real.norm_eq_abs]
        rw [hdist_block]
      have hright : {ω | ε ≤ |d * X 0 ω|} =
          (fun ω ↦ ‖((↑(∑ i ∈ Finset.Ico (min nm.1 nm.2) (max nm.1 nm.2),
            ‖a i‖₊ ^ q) : ℝ) ^ q⁻¹) * X 0 ω‖) ⁻¹' Set.Ici ε := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, Real.norm_eq_abs,
          d, A, u]
      rw [hleft, hright, hmem]
    rw [hmeasure]
    refine (measure_mono fun ω hω ↦ ?_).trans (hN N le_rfl)
    have habs_le : |d * X 0 ω| ≤ |b N * X 0 ω| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hd_nonneg, abs_of_nonneg hb_nonneg]
      exact mul_le_mul_of_nonneg_right hd_le (abs_nonneg _)
    change ε ≤ dist (b N * X 0 ω) 0
    simpa only [Real.dist_eq, sub_zero] using hω.trans habs_le
  obtain ⟨Y, hY⟩ := exists_tendstoInMeasure_of_cauchySeq hS hcau_dist
  refine ⟨Y, by simpa [S] using hY, ?_⟩
  exact h_indep.hasSymmetricStableLaw_of_tendstoInMeasure_sum_range_mul hX a ha
    (by simpa [S] using hY)

end iIndepFun

end ProbabilityTheory
