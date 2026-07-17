import BanLat.Probability.ConvergenceInMeasure
import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.Moments
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Gaussian sequences in `Lᵖ(P)` spaces

## Main theorems

• Let `(Ω, Σ, P)` be a probability space and `(Xₖ)ₖ` a sequence of independent, identically
distributed, standard centered real Gaussian random variables. For `1 ≤ p < ∞`, the closure
of their linear span in `Lᵖ(P)` is linearly isometric to `ℓ²(ℕ, ℝ)`.

• For `0 < p < 1`, the normalized Gaussian map defines an injective linear map `ℓ²(ℕ, ℝ) ↦ Lᵖ(P)`
which preserves the quasi-norm. -/

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal lp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℝ≥0}

/-- The almost-everywhere equivalence class in `Lᵖ`
represented by a standard Gaussian random variable. -/
noncomputable def standardGaussianToLp (p : ℝ≥0) {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) : Lp ℝ p P :=
  (hX.hasGaussianLaw.memLp ENNReal.coe_ne_top).toLp X

/-- A standard Gaussian has positive `Lᵖ` norm, so
its almost-everywhere class is non-zero. -/
private lemma norm_standardGaussianToLp_pos {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) (hp_pos : 0 < p) :
    0 < ‖standardGaussianToLp p hX‖ := by
  rw [lt_iff_le_and_ne]
  refine ⟨NNReal.coe_nonneg _, fun hzero ↦ ?_⟩
  have hmem : MemLp X p P :=
    hX.hasGaussianLaw.memLp ENNReal.coe_ne_top
  have hzero_ae : X =ᵐ[P] 0 :=
    (MemLp.coeFn_toLp hmem).symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp <|
        (Lp.norm_eq_zero_iff (by exact_mod_cast hp_pos)).mp hzero.symm)
  have hstable := hX.hasSymmetricStableLaw_two
  have hscale_zero := hstable.scale_eq_zero_iff_ae_eq_zero.mpr hzero_ae
  norm_num at hscale_zero

/-- The squared absolute values of the coordinates of an element of `ℓ²` are summable. -/
private lemma summable_nnnorm_sq (a : ℓ²(ℕ, ℝ)) :
    Summable (fun n ↦ ‖a n‖₊ ^ 2) := by
  rw [← NNReal.summable_coe]
  simpa [Real.norm_eq_abs, sq_abs] using
    (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The square root of the sum of the squared coordinates is the `ℓ²` norm. -/
private lemma sqrt_tsum_nnnorm_sq (a : ℓ²(ℕ, ℝ)) :
    Real.sqrt (↑(∑' n, ‖a n‖₊ ^ 2) : ℝ) = ‖a‖ := by
  have hnorm := lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num) a
  norm_num [Real.norm_eq_abs, sq_abs] at hnorm
  have htsum : (↑(∑' n, ‖a n‖₊ ^ 2) : ℝ) = ∑' n, (a n) ^ 2 := by
    rw [NNReal.coe_tsum]
    congr 1
    funext n
    simp [Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow, htsum, ← hnorm]

/-- Scalar multiplication in `Lᵖ` is represented almost everywhere
by pointwise multiplication of the underlying standard Gaussian. -/
private lemma coeFn_smul_standardGaussianToLp {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) (a : ℝ) :
    ⇑(a • standardGaussianToLp p hX) =ᵐ[P] fun ω ↦ a * X ω := by
  have hmem : MemLp X p P :=
    hX.hasGaussianLaw.memLp ENNReal.coe_ne_top
  rw [standardGaussianToLp, ← hmem.toLp_const_smul]
  simpa [Pi.smul_apply, smul_eq_mul] using MemLp.coeFn_toLp (hmem.const_smul a)

/-- A finite sum of Gaussian `Lᵖ` classes is represented almost
everywhere by the corresponding pointwise finite Gaussian sum. -/
private lemma coeFn_sum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (s : Finset ℕ) (a : ℕ → ℝ) :
    ⇑(∑ i ∈ s, a i • standardGaussianToLp p (hX i)) =ᵐ[P]
      fun ω ↦ ∑ i ∈ s, a i * X i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℝ p P)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (a i • standardGaussianToLp p (hX i))
        (∑ j ∈ s, a j • standardGaussianToLp p (hX j)),
        coeFn_smul_standardGaussianToLp (hX i) (a i), ih]
        with ω hadd hsmul hsum
      rw [hadd, Pi.add_apply, hsmul, hsum]

/-- Scalar multiplication in `Lᵖ` is homogeneous even when `0 < p < 1`. -/
private lemma norm_smul_Lp (r : ℝ) (f : Lp ℝ p P) :
    ‖r • f‖ = |r| * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_smul r f),
    eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
    Lp.norm_def]

/-- The `Lᵖ` norm of a finite Gaussian sum is the standard Gaussian
`Lᵖ` norm multiplied by the Euclidean norm of its coefficient vector. -/
private lemma norm_sum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ (p : ℝ≥0∞))]
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ i ∈ s, a i • standardGaussianToLp p (hX i)‖ =
      ‖standardGaussianToLp p (hX 0)‖ * Real.sqrt (∑ i ∈ s, (a i) ^ 2) := by
  have hp_pos : 0 < p := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ (p : ℝ≥0∞)))
  have hnorm :=
    ProbabilityTheory.iIndepFun.lpNorm_finset_sum_mul_standardGaussian
      (p := p) hX (hX 0) h_indep s a hp_pos
  have hcoe := coeFn_sum_standardGaussianToLp (p := p) hX s a
  have hsum_meas : AEStronglyMeasurable (fun ω ↦ ∑ i ∈ s, a i * X i ω) P := by
    exact (Lp.aestronglyMeasurable _).congr hcoe
  have hstd_norm : lpNorm (X 0) p P = ‖standardGaussianToLp p (hX 0)‖ := by
    rw [standardGaussianToLp, Lp.norm_toLp,
      toReal_eLpNorm (hX 0).aemeasurable.aestronglyMeasurable]
  calc
    ‖∑ i ∈ s, a i • standardGaussianToLp p (hX i)‖ =
        lpNorm (fun ω ↦ ∑ i ∈ s, a i * X i ω) p P := by
      rw [Lp.norm_def, eLpNorm_congr_ae hcoe, toReal_eLpNorm hsum_meas]
    _ = ‖standardGaussianToLp p (hX 0)‖ * Real.sqrt (∑ i ∈ s, (a i) ^ 2) := by
      rw [hnorm, hstd_norm, mul_comm]

private lemma norm_finset_sum_single_two (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ i ∈ s, lp.single 2 i (a i)‖ = Real.sqrt (∑ i ∈ s, (a i) ^ 2) := by
  have hsq := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) a s
  norm_num [Real.norm_eq_abs, sq_abs] at hsq
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Square-summability of the coefficients makes the
associated Gaussian series summable in the `Lᵖ` sense. -/
private lemma summable_smul_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ (p : ℝ≥0∞))] (a : ℓ²(ℕ, ℝ)) :
    Summable (fun n ↦ a n • standardGaussianToLp p (hX n)) := by
  let c := ‖standardGaussianToLp p (hX 0)‖
  have hp_pos : 0 < p := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ (p : ℝ≥0∞)))
  have hc : 0 < c := norm_standardGaussianToLp_pos (hX 0) hp_pos
  have hbasis : Summable (fun n ↦ lp.single 2 n (a n)) :=
    (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) a).summable
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s, hs⟩ :=
    summable_iff_vanishing_norm.1 hbasis (ε / c) (div_pos hε hc)
  refine ⟨s, ?_⟩
  intro t ht
  have hgauss :
      ‖∑ i ∈ t, a i • standardGaussianToLp p (hX i)‖ =
        c * Real.sqrt (∑ i ∈ t, (a i) ^ 2) := by
    simpa [c] using norm_sum_standardGaussianToLp hX h_indep t a
  have hbasisnorm := norm_finset_sum_single_two t a
  calc
    ‖∑ i ∈ t, a i • standardGaussianToLp p (hX i)‖ =
        c * ‖∑ i ∈ t, lp.single 2 i (a i)‖ := by rw [hgauss, hbasisnorm]
    _ < c * (ε / c) := mul_lt_mul_of_pos_left (hs t ht) hc
    _ = ε := by field_simp

/-- The `Lᵖ` norm of an infinite Gaussian series `∑ₖ aₖXₖ` is the standard
Gaussian `Lᵖ` norm `∣∣X₀∣∣ₚ` multiplied by the `ℓ²` norm of its coefficients. -/
private lemma norm_tsum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ (p : ℝ≥0∞))] (a : ℓ²(ℕ, ℝ)) :
  ‖∑' n, a n • standardGaussianToLp p (hX n)‖ =
      ‖standardGaussianToLp p (hX 0)‖ * ‖a‖ := by
  have hp_pos : 0 < p := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ (p : ℝ≥0∞)))
  obtain ⟨Y, hprob, _, hYmem, _, hYnorm⟩ :=
    h_indep.exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul_standardGaussian
      (p := p) hX a (summable_nnnorm_sq a) hp_pos
  have hsum := summable_smul_standardGaussianToLp (p := p) hX h_indep a
  have hpartial : TendstoInMeasure P
      (fun N ω ↦ (∑ n ∈ Finset.range N,
        a n • standardGaussianToLp p (hX n)) ω) Filter.atTop Y := by
    refine hprob.congr_left fun N ↦ ?_
    exact (coeFn_sum_standardGaussianToLp (p := p) hX (Finset.range N) a).symm
  have htsum_prob : TendstoInMeasure P
      (fun N ω ↦ (∑ n ∈ Finset.range N,
        a n • standardGaussianToLp p (hX n)) ω) Filter.atTop
      (fun ω ↦ (∑' n, a n • standardGaussianToLp p (hX n)) ω) := by
    exact tendstoInMeasure_of_tendsto_Lp hsum.hasSum.tendsto_sum_nat
  have hYeq : Y =ᵐ[P] fun ω ↦
      (∑' n, a n • standardGaussianToLp p (hX n)) ω :=
    tendstoInMeasure_ae_unique hpartial htsum_prob
  have hstd_norm : lpNorm (X 0) p P = ‖standardGaussianToLp p (hX 0)‖ := by
    rw [standardGaussianToLp, Lp.norm_toLp,
      toReal_eLpNorm (hX 0).aemeasurable.aestronglyMeasurable]
  calc
    ‖∑' n, a n • standardGaussianToLp p (hX n)‖ =
        lpNorm Y p P := by
      rw [Lp.norm_def, eLpNorm_congr_ae hYeq.symm]
      exact toReal_eLpNorm hYmem.1
    _ = Real.sqrt (↑(∑' n, ‖a n‖₊ ^ 2) : ℝ) *
        lpNorm (X 0) p P := hYnorm
    _ = ‖standardGaussianToLp p (hX 0)‖ * ‖a‖ := by
      rw [sqrt_tsum_nnnorm_sq, hstd_norm, mul_comm]

/-- For `0 < p < ∞`, the assignment `eₙ ↦ Xₙ` extends linearly to a map
`G : ℓ²(ℕ, ℝ) → Lᵖ(P)` satisfying `‖G a‖ = ‖N(0, 1)‖ₚ ‖a‖`. -/
private lemma exists_linearMap_standardGaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) (hp_pos : 0 < p) :
    ∃ G : ℓ²(ℕ, ℝ) →ₗ[ℝ] Lp ℝ p P,
      (∀ a, ‖G a‖ = ‖standardGaussianToLp p (hX 0)‖ * ‖a‖) ∧
      ∀ n, G (lp.single 2 n 1) = standardGaussianToLp p (hX n) := by
  letI := h_indep.isProbabilityMeasure
  let hex (a : ℓ²(ℕ, ℝ)) :
      ∃ Y : Ω → ℝ,
        TendstoInMeasure P
          (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y ∧
        HasLaw Y (gaussianReal 0 (∑' n, ‖a n‖₊ ^ 2)) P ∧
        MemLp Y p P ∧
        Filter.Tendsto
          (fun N ↦ lpNorm (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω)
            p P)
          Filter.atTop (nhds 0) ∧
        lpNorm Y p P =
          Real.sqrt (↑(∑' n, ‖a n‖₊ ^ 2) : ℝ) *
            lpNorm (X 0) p P :=
    h_indep.exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul_standardGaussian
      hX a (summable_nnnorm_sq a) hp_pos
  let Y : ℓ²(ℕ, ℝ) → Ω → ℝ := fun a ↦ (hex a).choose
  have hYspec (a : ℓ²(ℕ, ℝ)) := (hex a).choose_spec
  let hYmem (a : ℓ²(ℕ, ℝ)) : MemLp (Y a) p P := (hYspec a).2.2.1
  have hpartial_meas (a : ℓ²(ℕ, ℝ)) (N : ℕ) :
      AEStronglyMeasurable (fun ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) P := by
    exact (Finset.aemeasurable_fun_sum _ fun n _ ↦
      (hX n).aemeasurable.const_mul (a n)).aestronglyMeasurable
  let G : ℓ²(ℕ, ℝ) →ₗ[ℝ] Lp ℝ p P :=
    { toFun := fun a ↦ (hYmem a).toLp (Y a)
      map_add' := by
        intro a b
        have hab := tendstoInMeasure_add_real
          (fun N ↦ hpartial_meas a N) (fun N ↦ hpartial_meas b N)
          (hYspec a).1 (hYspec b).1
        have hab' : TendstoInMeasure P
            (fun N ω ↦ ∑ n ∈ Finset.range N, (a + b) n * X n ω)
            Filter.atTop (fun ω ↦ Y a ω + Y b ω) := by
          refine hab.congr_left fun N ↦ Filter.Eventually.of_forall fun ω ↦ ?_
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [lp.coeFn_add, Pi.add_apply]
          ring
        have huniq : Y (a + b) =ᵐ[P] fun ω ↦ Y a ω + Y b ω :=
          tendstoInMeasure_ae_unique (hYspec (a + b)).1 hab'
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hYmem (a + b)), huniq,
          Lp.coeFn_add ((hYmem a).toLp (Y a)) ((hYmem b).toLp (Y b)),
          MemLp.coeFn_toLp (hYmem a), MemLp.coeFn_toLp (hYmem b)]
          with ω hleft huniqω hadd ha hb
        rw [hleft, huniqω, hadd, Pi.add_apply, ha, hb]
      map_smul' := by
        intro r a
        have hra := tendstoInMeasure_const_mul_real
          (fun N ↦ hpartial_meas a N) (hYspec a).1 r
        have hra' : TendstoInMeasure P
            (fun N ω ↦ ∑ n ∈ Finset.range N, (r • a) n * X n ω)
            Filter.atTop (fun ω ↦ r * Y a ω) := by
          refine hra.congr_left fun N ↦ Filter.Eventually.of_forall fun ω ↦ ?_
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [lp.coeFn_smul, Pi.smul_apply]
          simp only [smul_eq_mul]
          ring
        have huniq : Y (r • a) =ᵐ[P] fun ω ↦ r * Y a ω :=
          tendstoInMeasure_ae_unique (hYspec (r • a)).1 hra'
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hYmem (r • a)), huniq,
          Lp.coeFn_smul r ((hYmem a).toLp (Y a)), MemLp.coeFn_toLp (hYmem a)]
          with ω hleft huniqω hsmul ha
        rw [hleft, huniqω]
        change r * Y a ω = ⇑(r • (hYmem a).toLp (Y a)) ω
        rw [hsmul, Pi.smul_apply, ha]
        simp only [smul_eq_mul] }
  let c := ‖standardGaussianToLp p (hX 0)‖
  have hstd_norm : lpNorm (X 0) p P = c := by
    change lpNorm (X 0) p P = ‖standardGaussianToLp p (hX 0)‖
    rw [standardGaussianToLp, Lp.norm_toLp,
      toReal_eLpNorm (hX 0).aemeasurable.aestronglyMeasurable]
  have hGnorm (a : ℓ²(ℕ, ℝ)) : ‖G a‖ = c * ‖a‖ := by
    change ‖(hYmem a).toLp (Y a)‖ = c * ‖a‖
    rw [Lp.norm_toLp, toReal_eLpNorm (hYmem a).1,
      (hYspec a).2.2.2.2, sqrt_tsum_nnnorm_sq, hstd_norm]
    exact mul_comm _ _
  have hGsingle (n : ℕ) : G (lp.single 2 n 1) = standardGaussianToLp p (hX n) := by
    let e : ℓ²(ℕ, ℝ) := lp.single 2 n 1
    have hconst : TendstoInMeasure P (fun _ ↦ X n) Filter.atTop (X n) :=
      tendstoInMeasure_of_tendsto_ae
        (fun _ ↦ (hX n).aemeasurable.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun _ ↦ tendsto_const_nhds)
    have hevent : ∀ᶠ N in Filter.atTop,
        (X n : Ω → ℝ) =ᵐ[P] fun ω ↦ ∑ i ∈ Finset.range N, e i * X i ω := by
      filter_upwards [Filter.eventually_ge_atTop (n + 1)] with N hN
      exact Filter.Eventually.of_forall fun ω ↦ by
        have hnN : n < N := (Nat.lt_succ_self n).trans_le hN
        change X n ω = ∑ i ∈ Finset.range N, e i * X i ω
        rw [Finset.sum_eq_single n]
        · simp [e, lp.single_apply]
        · intro i hi hin
          simp [e, lp.single_apply, hin]
        · intro hNn
          exact (hNn (Finset.mem_range.mpr hnN)).elim
    have heprob : TendstoInMeasure P
        (fun N ω ↦ ∑ i ∈ Finset.range N, e i * X i ω)
        Filter.atTop (X n) := hconst.congr' hevent Filter.EventuallyEq.rfl
    have huniq : Y e =ᵐ[P] X n := tendstoInMeasure_ae_unique (hYspec e).1 heprob
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hYmem e), huniq,
      MemLp.coeFn_toLp ((hX n).hasGaussianLaw.memLp ENNReal.coe_ne_top)]
      with ω hleft huniqω hright
    simpa [G, e, standardGaussianToLp] using hleft.trans (huniqω.trans hright.symm)
  exact ⟨G, fun a ↦ by simpa [c] using hGnorm a, hGsingle⟩

/-- Normalizing the Gaussian map by `‖N(0, 1)‖ₚ⁻¹` gives a norm-preserving linear map
sending `eₙ` to `‖N(0, 1)‖ₚ⁻¹Xₙ`. -/
private lemma exists_linearMap_standardGaussian_norm_eq {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) (hp_pos : 0 < p) :
    ∃ T : ℓ²(ℕ, ℝ) →ₗ[ℝ] Lp ℝ p P,
      (∀ a, ‖T a‖ = ‖a‖) ∧
      ∀ n, T (lp.single 2 n 1) =
        ‖standardGaussianToLp p (hX 0)‖⁻¹ • standardGaussianToLp p (hX n) := by
  obtain ⟨G, hGnorm, hG⟩ := exists_linearMap_standardGaussian hX h_indep hp_pos
  let c := ‖standardGaussianToLp p (hX 0)‖
  have hc : 0 < c := norm_standardGaussianToLp_pos (hX 0) hp_pos
  let T : ℓ²(ℕ, ℝ) →ₗ[ℝ] Lp ℝ p P := c⁻¹ • G
  have hTnorm (a : ℓ²(ℕ, ℝ)) : ‖T a‖ = ‖a‖ := by
    change ‖c⁻¹ • G a‖ = ‖a‖
    rw [norm_smul_Lp, hGnorm]
    simp [c, abs_of_pos hc, hc.ne']
  refine ⟨T, hTnorm, ?_⟩
  intro n
  simpa [T, c] using congrArg (fun z ↦ c⁻¹ • z) (hG n)

/-- For `1 ≤ p < ∞`, the previous map `T : ℓ²(ℕ, ℝ) → Lᵖ(P)` is a linear isometric
embedding of `ℓ²(ℕ, ℝ)` into `Lᵖ(P)`. -/
private lemma exists_linearIsometry_standardGaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ (p : ℝ≥0∞))] :
    ∃ T : ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] Lp ℝ p P,
      ∀ n, T (lp.single 2 n 1) =
        ‖standardGaussianToLp p (hX 0)‖⁻¹ • standardGaussianToLp p (hX n) := by
  have hp_pos : 0 < p := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ (p : ℝ≥0∞)))
  obtain ⟨T, hTnorm, hT⟩ :=
    exists_linearMap_standardGaussian_norm_eq hX h_indep hp_pos
  refine ⟨{ toLinearMap := T, norm_map' := hTnorm }, ?_⟩
  exact hT

/-- For `1 ≤ p < ∞`, the range of the linear isometric embedding `T : ℓ²(ℕ, ℝ) → Lᵖ(P)`
`eₙ ↦ ‖N(0, 1)‖ₚ⁻¹Xₙ` is the closed linear span of the standard Gaussian sequence. -/
private lemma range_linearIsometry_standardGaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (T : ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] Lp ℝ p P)
    (hT : ∀ n, T (lp.single 2 n 1) =
      ‖standardGaussianToLp p (hX 0)‖⁻¹ • standardGaussianToLp p (hX n)) :
    LinearMap.range T.toLinearMap =
      (Submodule.span ℝ (Set.range fun n ↦ standardGaussianToLp p (hX n))
        |>.topologicalClosure) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x
    have hTx : HasSum (fun n ↦ T (lp.single 2 n (x n))) (T x) := by
      simpa only [Function.comp_apply] using hx.map T T.continuous
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hTx ?_
    filter_upwards with s
    apply Submodule.sum_mem
    intro n _
    have hsingle : lp.single (E := fun _ : ℕ ↦ ℝ) 2 n (x n) =
        (x n) • lp.single (E := fun _ : ℕ ↦ ℝ) 2 n (1 : ℝ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hsingle, map_smul, hT n]
    exact Submodule.smul_mem _ (x n) <| Submodule.smul_mem _
      ‖standardGaussianToLp p (hX 0)‖⁻¹ <|
        Submodule.le_topologicalClosure _ <| Submodule.subset_span ⟨n, rfl⟩
  · have hclosed : IsClosed (T.range : Set (Lp ℝ p P)) := by
      exact T.isometry.antilipschitz.isClosed_range T.isometry.uniformContinuous
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hclosed
    rintro _ ⟨n, rfl⟩
    have hp_pos : 0 < p := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ (p : ℝ≥0∞)))
    have hc := norm_standardGaussianToLp_pos (hX 0) hp_pos
    refine ⟨‖standardGaussianToLp p (hX 0)‖ • lp.single 2 n 1, ?_⟩
    simp [map_smul, hT n, smul_smul, hc.ne']

/-- For `p ≥ 1`, the closed linear span in `Lᵖ` of an independent sequence of standard
real Gaussian random variables is linearly isometric to `ℓ²(ℕ, ℝ)`. -/
theorem nonempty_linearIsometryEquiv_standardGaussian_closedSpan
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ (p : ℝ≥0∞))] :
    Nonempty
      (ℓ²(ℕ, ℝ) ≃ₗᵢ[ℝ]
        (Submodule.span ℝ (Set.range fun n ↦ standardGaussianToLp p (hX n))
          |>.topologicalClosure)) := by
  obtain ⟨T, hT⟩ := exists_linearIsometry_standardGaussian (p := p) hX h_indep
  have hRange := range_linearIsometry_standardGaussian hX T hT
  exact ⟨T.equivRange.trans (LinearIsometryEquiv.ofEq _ _ hRange)⟩

/-- For `0 < p < 1`, the normalized Gaussian map embeds `ℓ²(ℕ, ℝ)` linearly into
`Lᵖ`, preserves the quasi-norm, and sends `eₙ` to `‖N(0, 1)‖ₚ⁻¹ · Xₙ`. -/
theorem exists_linearMap_standardGaussian_preserving_quasiNorm
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P)
    (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∃ T : ℓ²(ℕ, ℝ) →ₗ[ℝ] Lp ℝ p P,
      Function.Injective T ∧
      (∀ a, ‖T a‖ = ‖a‖) ∧
      ∀ n, T (lp.single 2 n 1) =
        ‖standardGaussianToLp p (hX 0)‖⁻¹ • standardGaussianToLp p (hX n) := by
  have _hp_lt_one := hp_lt_one
  obtain ⟨T, hTnorm, hT⟩ :=
    exists_linearMap_standardGaussian_norm_eq hX h_indep hp_pos
  have hTinj : Function.Injective T := by
    intro a b hab
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← hTnorm (a - b), map_sub, hab, sub_self, Lp.norm_zero]
  exact ⟨T, hTinj, hTnorm, hT⟩
