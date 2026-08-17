import BanLat.Probability.Distributions.Stable.GaussianCompatibility
import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.IndependentInfiniteSums
import BanLat.Probability.Distributions.Stable.Moments
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Absolute moments of symmetric `q`-stable random variables

Let `X` be a symmetric `q`-stable random variable with scale parameter `c`. This file characterizes
the exponents `p` for which its absolute `p`-moment, `E∣X∣ᵖ`, is finite:
  • If `c = 0`, the random variable vanishes almost surely, thus `E∣X∣^p = 0, ∀ 0 < p < ∞`.
  • If `c > 0`, then:
    - If `q = 2`, `E∣X∣^p < ∞, ∀ 0 < p < ∞`.
    - If `q < 2`, `E∣X∣^p < ∞ ↔ 0 < p < q`.
The file also expresses the absolute moments and `Lᵖ` norms of finite and infinite linear
combinations of independent symmetric `q`-stable random variables with a common scale parameter.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → ℝ} {p : ℝ≥0} {q : ℝ} {c : ℝ≥0}

namespace HasSymmetricStableLaw

/-- A symmetric `q`-stable random variable with scale parameter zero vanishes almost surely
and therefore belongs to `Lᵖ` for every nonnegative real exponent `p`. -/
lemma memLp_of_scale_eq_zero (hX : HasSymmetricStableLaw X q c P)
    (hc : c = 0) (p : ℝ≥0) :
    MemLp X p P := by
  letI := hX.isProbabilityMeasure
  have hzero := (hX.scale_eq_zero_iff_ae_eq_zero).mp hc
  exact (memLp_const (0 : ℝ)).congr_norm hX.aemeasurable.aestronglyMeasurable
    (hzero.mono fun ω hω ↦ by simp [hω])

/-- Let `c > 0` and `q < 2` and `X` be a symmetric `q`-stable random variable with scale
parameter `c` . Then `E∣X∣ᵖ < ∞ ↔ p < q`. -/
private lemma memLp_iff_of_scale_pos_of_index_lt_two_nnreal
    (hX : HasSymmetricStableLaw X q c P) (hc : 0 < c) (hq : q < 2)
    (hp_pos : 0 < p) :
    MemLp X p P ↔ (p : ℝ) < q := by
  rw [← Function.id_comp X, ← memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable]
  rw [← integrable_norm_rpow_iff aestronglyMeasurable_id (by exact_mod_cast hp_pos.ne')
    ENNReal.coe_ne_top]
  simpa [Real.norm_eq_abs] using
    hX.isSymmetricStable_map.integrable_abs_rpow_iff_of_scale_pos_of_index_lt_two
      hc hq (by exact_mod_cast hp_pos)

/-- A symmetric `q`-stable random variable is integrable iff it is degenerate or its
index satisfies `1 < q`. -/
lemma integrable_iff (hX : HasSymmetricStableLaw X q c P) :
    Integrable X P ↔ c = 0 ∨ 1 < q := by
  rw [← memLp_one_iff_integrable]
  by_cases hc : c = 0
  · have hX_one : MemLp X 1 P := by
      simpa only [ENNReal.ofReal_one] using hX.memLp_of_scale_eq_zero hc 1
    simp [hc, hX_one]
  have hc_pos : 0 < c := pos_iff_ne_zero.mpr hc
  by_cases hq : q = 2
  · subst q
    have hX_one : MemLp X 1 P :=
      (hasSymmetricStableLaw_two_iff_hasLaw_gaussianReal.mp hX).hasGaussianLaw.memLp (by norm_num)
    simp [hc, hX_one]
  · have hq_lt_two : q < 2 := lt_of_le_of_ne hX.isSymmetricStable_map.index_le_two hq
    simpa [hc] using
      (memLp_iff_of_scale_pos_of_index_lt_two_nnreal
        hX hc_pos hq_lt_two (p := 1) (by norm_num))

/-- Let `X` be a nondegenerate symmetric `q`-stable random variable with `q < 2`. For `p > 0`,
`X` belongs to `Lᵖ` exactly when `p < q`. -/
lemma memLp_iff_of_scale_pos_of_index_lt_two
    (hX : HasSymmetricStableLaw X q c P) (hc : 0 < c) (hq : q < 2)
    (hp_pos : 0 < p) :
    MemLp X p P ↔ (p : ℝ) < q :=
  memLp_iff_of_scale_pos_of_index_lt_two_nnreal hX hc hq hp_pos

/-- A symmetric `2`-stable random variable with scale parameter `c` is centered Gaussian with
variance `2 * c`, and hence belongs to `Lᵖ` for every `p ≥ 0`. -/
lemma memLp_of_index_eq_two (hX : HasSymmetricStableLaw X q c P)
    (hq : q = 2) :
    MemLp X p P := by
  subst q
  exact (hasSymmetricStableLaw_two_iff_hasLaw_gaussianReal.mp hX).hasGaussianLaw.memLp
    ENNReal.coe_ne_top

/-- For `p > 0`, a symmetric `q`-stable random variable belongs to `Lᵖ` exactly when it is
degenerate, or when either `q = 2` or `p < q`. -/
lemma memLp_iff (hX : HasSymmetricStableLaw X q c P) (hp_pos : 0 < p) :
    MemLp X p P ↔ c = 0 ∨ q = 2 ∨ (p : ℝ) < q := by
  by_cases hc : c = 0
  · simp [hc, hX.memLp_of_scale_eq_zero hc p]
  have hc_pos : 0 < c := pos_iff_ne_zero.mpr hc
  by_cases hq : q = 2
  · simp [hc, hq, hX.memLp_of_index_eq_two hq]
  · have hq_lt_two : q < 2 := lt_of_le_of_ne hX.isSymmetricStable_map.index_le_two hq
    simpa [hc, hq] using
      hX.memLp_iff_of_scale_pos_of_index_lt_two hc_pos hq_lt_two hp_pos

end HasSymmetricStableLaw

namespace iIndepFun

private lemma identDistrib_rpow_smul_of_hasSymmetricStableLaw
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω → ℝ} {Z : Ω' → ℝ} {A : ℝ≥0}
    (hY : HasSymmetricStableLaw Y q (c * A) P)
    (hZ : HasSymmetricStableLaw Z q c Q) :
    IdentDistrib Y (fun ω ↦ (A : ℝ) ^ q⁻¹ * Z ω) P Q := by
  have hq : q ≠ 0 := hZ.isSymmetricStable_map.index_pos.ne'
  have hroot : ‖(A : ℝ) ^ q⁻¹‖₊ ^ q = A := by
    apply NNReal.eq
    have hnonneg : 0 ≤ (A : ℝ) ^ q⁻¹ := Real.rpow_nonneg A.2 _
    rw [NNReal.coe_rpow, coe_nnnorm, Real.norm_of_nonneg hnonneg]
    exact Real.rpow_inv_rpow A.2 hq
  have hscaled : HasSymmetricStableLaw (fun ω ↦ (A : ℝ) ^ q⁻¹ * Z ω) q (c * A) Q := by
    simpa [hroot] using hZ.const_mul ((A : ℝ) ^ q⁻¹)
  exact ⟨hY.aemeasurable, hscaled.aemeasurable,
    hY.isSymmetricStable_map.eq hscaled.isSymmetricStable_map⟩

private lemma lpNorm_eq_rpow_mul_of_hasSymmetricStableLaw
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω → ℝ} {Z : Ω' → ℝ} {A : ℝ≥0}
    (hY : HasSymmetricStableLaw Y q (c * A) P)
    (hZ : HasSymmetricStableLaw Z q c Q) :
    lpNorm Y p P = (A : ℝ) ^ q⁻¹ * lpNorm Z p Q := by
  have hident := identDistrib_rpow_smul_of_hasSymmetricStableLaw hY hZ
  have hlpNorm : lpNorm Y p P =
      lpNorm (fun ω ↦ (A : ℝ) ^ q⁻¹ * Z ω) p Q := by
    rw [← toReal_eLpNorm hident.aestronglyMeasurable_fst,
      ← toReal_eLpNorm hident.aemeasurable_snd.aestronglyMeasurable,
      hident.eLpNorm_eq p]
  rw [hlpNorm]
  change lpNorm ((A : ℝ) ^ q⁻¹ • Z) p Q = _
  rw [lpNorm_const_smul]
  congr 1
  rw [coe_nnnorm, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.rpow_nonneg A.2 q⁻¹)

private lemma TendstoInMeasure.sub_const_real
    {ι : Type*} {l : Filter ι} {f : ι → Ω → ℝ} {Y : Ω → ℝ}
    (h : TendstoInMeasure P f l Y) (Z : Ω → ℝ) :
    TendstoInMeasure P (fun i ω ↦ f i ω - Z ω) l (fun ω ↦ Y ω - Z ω) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  simpa only [dist_sub_right] using h

private lemma hasSymmetricStableLaw_sub_sum_range_mul
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q c P)
    (h_indep : iIndepFun X P) (a : ℕ → ℝ)
    (ha : Summable (fun n ↦ ‖a n‖₊ ^ q))
    (hY : TendstoInMeasure P
      (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y)
    (N : ℕ) :
    HasSymmetricStableLaw
      (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω) q
      (c * ∑' n, ‖a (N + n)‖₊ ^ q) P := by
  let XN : ℕ → Ω → ℝ := fun n ↦ X (N + n)
  let aN : ℕ → ℝ := fun n ↦ a (N + n)
  have h_indepN : iIndepFun XN P := by
    exact h_indep.precomp (g := fun n ↦ N + n) fun _ _ h ↦ Nat.add_left_cancel h
  have hXN : ∀ n, HasSymmetricStableLaw (XN n) q c P := fun n ↦ hX (N + n)
  have haN : Summable (fun n ↦ ‖aN n‖₊ ^ q) := by
    simpa only [aN, add_comm] using NNReal.summable_nat_add _ ha N
  apply h_indepN.hasSymmetricStableLaw_of_tendstoInMeasure_sum_range_mul hXN aN haN
  have hshift := hY.comp (Filter.tendsto_add_atTop_nat N)
  have hsub := TendstoInMeasure.sub_const_real hshift
    (fun ω ↦ ∑ n ∈ Finset.range N, a n * X n ω)
  apply hsub.congr_left
  intro M
  filter_upwards [] with ω
  simp only [Function.comp_apply, XN, aN]
  rw [add_comm M N, Finset.sum_range_add]
  simp

/-- Let `(X i)` be independent symmetric `q`-stable random variables with common scale `c`,
and let `Z` be another symmetric `q`-stable random variable with scale `c`. Then:
`‖∑ i ∈ s, a i X i‖ₚ = (∑ i ∈ s, |a i| ^ q) ^ (1 / q) ‖Z‖ₚ`. -/
lemma lpNorm_finset_sum_mul_of_hasSymmetricStableLaw
    {Ω' ι : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {X : ι → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, HasSymmetricStableLaw (X i) q c P)
    (hZ : HasSymmetricStableLaw Z q c Q)
    (h_indep : iIndepFun X P) (s : Finset ι) (a : ι → ℝ)
    (_hpq : q = 2 ∨ (p : ℝ) < q) :
    lpNorm (fun ω ↦ ∑ i ∈ s, a i * X i ω) p P =
      ((↑(∑ i ∈ s, ‖a i‖₊ ^ q) : ℝ) ^ q⁻¹) *
        lpNorm Z p Q := by
  have hident := h_indep.identDistrib_finset_sum_mul_of_hasSymmetricStableLaw hX hZ s a
  have hlpNorm :
      lpNorm (fun ω ↦ ∑ i ∈ s, a i * X i ω) p P =
        lpNorm (fun ω ↦ ((↑(∑ i ∈ s, ‖a i‖₊ ^ q) : ℝ) ^ q⁻¹) * Z ω)
          p Q := by
    rw [← toReal_eLpNorm hident.aestronglyMeasurable_fst]
    rw [← toReal_eLpNorm hident.aemeasurable_snd.aestronglyMeasurable]
    rw [hident.eLpNorm_eq p]
  rw [hlpNorm]
  convert lpNorm_const_smul ((↑(∑ i ∈ s, ‖a i‖₊ ^ q) : ℝ) ^ q⁻¹) Z Q using 1
  rw [coe_nnnorm, Real.norm_of_nonneg]
  positivity

/-- For `p > 0` with `q = 2` or `p < q`, let `(X i)` be independent symmetric `q`-stable
random variables with common scale `c`, and let `Z` have the same law. Then:
`∫ |∑ i ∈ s, a i X i|ᵖ dP = (∑ i ∈ s, |a i|^q) ^ (p / q) ∫ |Z|ᵖ dQ`. -/
lemma integral_abs_rpow_finset_sum_mul_of_hasSymmetricStableLaw
    {Ω' ι : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {X : ι → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, HasSymmetricStableLaw (X i) q c P)
    (hZ : HasSymmetricStableLaw Z q c Q)
    (h_indep : iIndepFun X P) (s : Finset ι) (a : ι → ℝ)
    (_hp_pos : 0 < p) (_hpq : q = 2 ∨ (p : ℝ) < q) :
    ∫ ω, |∑ i ∈ s, a i * X i ω| ^ (p : ℝ) ∂P =
      ((↑(∑ i ∈ s, ‖a i‖₊ ^ q) : ℝ) ^ ((p : ℝ) / q)) *
        ∫ ω, |Z ω| ^ (p : ℝ) ∂Q := by
  have hident := h_indep.identDistrib_finset_sum_mul_of_hasSymmetricStableLaw hX hZ s a
  have hmoment :=
    (hident.comp (by fun_prop : Measurable (fun x : ℝ ↦ |x| ^ (p : ℝ)))).integral_eq
  have hmoment' :
      ∫ ω, |∑ i ∈ s, a i * X i ω| ^ (p : ℝ) ∂P =
        ∫ ω, |((↑(∑ i ∈ s, ‖a i‖₊ ^ q) : ℝ) ^ q⁻¹) * Z ω| ^ (p : ℝ) ∂Q := by
    simpa [Function.comp_apply] using hmoment
  let B : ℝ := ↑(∑ i ∈ s, ‖a i‖₊ ^ q)
  have hB : 0 ≤ B := by positivity
  have hq_ne : q ≠ 0 := hZ.isSymmetricStable_map.index_pos.ne'
  have hpoint (z : ℝ) :
      |B ^ q⁻¹ * z| ^ (p : ℝ) = B ^ ((p : ℝ) / q) * |z| ^ (p : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hB _),
      Real.mul_rpow (Real.rpow_nonneg hB _) (abs_nonneg z)]
    rw [← Real.rpow_mul hB]
    congr 1
    field_simp
  rw [hmoment']
  change (∫ ω, |B ^ q⁻¹ * Z ω| ^ (p : ℝ) ∂Q) =
    B ^ ((p : ℝ) / q) * ∫ ω, |Z ω| ^ (p : ℝ) ∂Q
  simp_rw [hpoint]
  rw [integral_const_mul]

/-- Let `(X i)` be independent standard centered Gaussian random variables and `Z` be
standard centered Gaussian. Then
`‖∑ i ∈ s, a i X i‖ₚ = (∑ i ∈ s, a i ^ 2) ^ (1 / 2) ‖Z‖ₚ`. -/
lemma lpNorm_finset_sum_mul_standardGaussian
    {Ω' ι : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {X : ι → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hZ : HasLaw Z (gaussianReal 0 1) Q)
    (h_indep : iIndepFun X P) (s : Finset ι) (a : ι → ℝ) :
    lpNorm (fun ω ↦ ∑ i ∈ s, a i * X i ω) p P =
      Real.sqrt (∑ i ∈ s, (a i) ^ 2) * lpNorm Z p Q := by
  have hstable := lpNorm_finset_sum_mul_of_hasSymmetricStableLaw
    (fun i ↦ (hX i).hasSymmetricStableLaw_two) hZ.hasSymmetricStableLaw_two
    h_indep s a (p := p) (Or.inl rfl)
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] using hstable

/-- For `p > 0`, let `(X i)` be independent standard centered Gaussian random variables and
let `Z` be standard centered Gaussian. Then
`∫ |∑ i ∈ s, a i X i|ᵖ dP = (∑ i ∈ s, a i ^ 2) ^ (p / 2) ∫ |Z|ᵖ dQ`. -/
lemma integral_abs_rpow_finset_sum_mul_standardGaussian
    {Ω' ι : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {X : ι → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hZ : HasLaw Z (gaussianReal 0 1) Q)
    (h_indep : iIndepFun X P) (s : Finset ι) (a : ι → ℝ)
    (hp_pos : 0 < p) :
    ∫ ω, |∑ i ∈ s, a i * X i ω| ^ (p : ℝ) ∂P =
      (∑ i ∈ s, (a i) ^ 2) ^ ((p : ℝ) / 2) *
        ∫ ω, |Z ω| ^ (p : ℝ) ∂Q := by
  have hstable := integral_abs_rpow_finset_sum_mul_of_hasSymmetricStableLaw
    (fun i ↦ (hX i).hasSymmetricStableLaw_two) hZ.hasSymmetricStableLaw_two
    h_indep s a hp_pos (Or.inl rfl)
  simpa [Real.norm_eq_abs, sq_abs] using hstable

private lemma exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q c P)
    (h_indep : iIndepFun X P) (a : ℕ → ℝ)
    (ha : Summable (fun n ↦ ‖a n‖₊ ^ q))
    (hp_pos : 0 < p) (hpq : q = 2 ∨ (p : ℝ) < q) :
    ∃ Y : Ω → ℝ,
      TendstoInMeasure P
        (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y ∧
      HasSymmetricStableLaw Y q (c * ∑' n, ‖a n‖₊ ^ q) P ∧
      MemLp Y p P ∧
      Filter.Tendsto
        (fun N ↦
          lpNorm (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω)
            p P)
        Filter.atTop (nhds 0) ∧
      lpNorm Y p P =
        ((↑(∑' n, ‖a n‖₊ ^ q) : ℝ) ^ q⁻¹) *
          lpNorm (X 0) p P := by
  obtain ⟨Y, hY, hYstable⟩ :=
    h_indep.exists_tendstoInMeasure_sum_range_mul_of_hasSymmetricStableLaw hX a ha
  refine ⟨Y, hY, hYstable, ?_, ?_, ?_⟩
  · exact (hYstable.memLp_iff hp_pos).2 (Or.inr hpq)
  · have htail (N : ℕ) :
        lpNorm (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω)
            p P =
          ((↑(∑' n, ‖a (N + n)‖₊ ^ q) : ℝ) ^ q⁻¹) *
            lpNorm (X 0) p P := by
      exact lpNorm_eq_rpow_mul_of_hasSymmetricStableLaw
        (hasSymmetricStableLaw_sub_sum_range_mul hX h_indep a ha hY N) (hX 0)
    let u : ℕ → ℝ≥0 := fun n ↦ ‖a n‖₊ ^ q
    have htailNN : Filter.Tendsto (fun N ↦ ∑' n, u (n + N)) Filter.atTop (nhds 0) :=
      NNReal.tendsto_sum_nat_add u
    have htailReal : Filter.Tendsto (fun N ↦ (↑(∑' n, u (n + N)) : ℝ))
        Filter.atTop (nhds 0) := NNReal.tendsto_coe.mpr htailNN
    have hq_inv_pos : 0 < q⁻¹ := inv_pos.mpr (hX 0).isSymmetricStable_map.index_pos
    have hfactor := htailReal.rpow_const (Or.inr hq_inv_pos.le)
    have hproduct := hfactor.mul_const (lpNorm (X 0) p P)
    simpa only [u, add_comm, htail, Real.zero_rpow hq_inv_pos.ne', zero_mul] using hproduct
  · exact lpNorm_eq_rpow_mul_of_hasSymmetricStableLaw hYstable (hX 0)

/-- Let `(X n)` be independent symmetric `q`-stable random variables with common scale `c`,
where `q < 2`, and suppose that `∑ n, |aₙ|^q < ∞`. If `0 < p < q`, then the partial sums
of `∑ n, aₙXₙ` converge in probability and in `Lᵖ` to a symmetric `q`-stable random
variable `Y`, and `‖Y‖ₚ = (∑ n, |aₙ|^q) ^ (1 / q) ‖X 0‖ₚ`. -/
lemma exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul_of_hasSymmetricStableLaw_of_index_lt_two
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q c P)
    (h_indep : iIndepFun X P) (a : ℕ → ℝ)
    (ha : Summable (fun n ↦ ‖a n‖₊ ^ q))
    (hq : q < 2) (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    ∃ Y : Ω → ℝ,
      TendstoInMeasure P
        (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y ∧
      HasSymmetricStableLaw Y q (c * ∑' n, ‖a n‖₊ ^ q) P ∧
      MemLp Y p P ∧
      Filter.Tendsto
        (fun N ↦
          lpNorm (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω)
            p P)
        Filter.atTop (nhds 0) ∧
      lpNorm Y p P =
        ((↑(∑' n, ‖a n‖₊ ^ q) : ℝ) ^ q⁻¹) *
          lpNorm (X 0) p P := by
  have _hq := hq
  exact exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul
    hX h_indep a ha hp_pos (Or.inr hpq)

/-- Let `(X n)` be independent standard centered Gaussian random variables and suppose that
`∑ n, |aₙ|² < ∞`. For every positive finite `p`, the partial sums of `∑ n, aₙ Xₙ`
converge in probability and in `Lᵖ` to a centered Gaussian random variable `Y` with variance
`∑ n, |aₙ|²`, and
`‖Y‖ₚ = (∑ n, |aₙ|²) ^ (1 / 2) ‖X₀‖ₚ`. -/
lemma exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul_standardGaussian
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) (a : ℕ → ℝ)
    (ha : Summable (fun n ↦ ‖a n‖₊ ^ 2))
    (hp_pos : 0 < p) :
    ∃ Y : Ω → ℝ,
      TendstoInMeasure P
        (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y ∧
      HasLaw Y (gaussianReal 0 (∑' n, ‖a n‖₊ ^ 2)) P ∧
      MemLp Y p P ∧
      Filter.Tendsto
        (fun N ↦
          lpNorm (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω)
            p P)
        Filter.atTop (nhds 0) ∧
      lpNorm Y p P =
        Real.sqrt (↑(∑' n, ‖a n‖₊ ^ 2) : ℝ) *
          lpNorm (X 0) p P := by
  have haStable : Summable (fun n ↦ ‖a n‖₊ ^ (2 : ℝ)) := by
    simpa only [NNReal.rpow_two] using ha
  obtain ⟨Y, hY, hYstable, hYp, hYconv, hYnorm⟩ :=
    exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul
      (fun n ↦ (hX n).hasSymmetricStableLaw_two) h_indep a haStable
      hp_pos (Or.inl rfl)
  refine ⟨Y, hY, ?_, hYp, hYconv, ?_⟩
  · have hlaw := hasSymmetricStableLaw_two_iff_hasLaw_gaussianReal.mp hYstable
    convert hlaw using 1
    congr 2
    simp only [NNReal.rpow_two, ← mul_assoc]
    norm_num
  · simpa only [NNReal.rpow_two, Real.sqrt_eq_rpow, invOf_eq_inv, one_div] using hYnorm

end iIndepFun

end ProbabilityTheory
