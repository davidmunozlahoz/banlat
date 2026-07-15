import BanLat.Preliminaries.AtomlessIid
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian sequences in `Lᵖ(μ)` spaces

## Main theorems

• Let `(Ω, Σ, μ)` be a probability space and `(Xₖ)ₖ` a sequence of independent, identically
distributed, centered, nondegenerate real Gaussian random variables. For `1 ≤ p < ∞`, the
closure of their linear span in `Lᵖ(μ)` is linearly isometric to `ℓ²(ℕ)`.

• Let `(Ω, Σ, μ)` be an atomless finite measure space and `1 ≤ p < ∞`. Then `Lᵖ(μ)` contains
an isometrically isomorphic copy of `ℓ²(ℕ)`.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal lp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℝ≥0∞}

-- The almost-everywhere equivalence class in `Lᵖ`
-- represented by a standard Gaussian random variable.
noncomputable def standardGaussianToLp {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) (hp : p ≠ ∞) : Lp ℝ p P :=
  (hX.hasGaussianLaw.memLp hp).toLp X

-- A standard Gaussian has positive `Lᵖ` norm, so
-- its almost-everywhere class is non-zero.
private lemma norm_standardGaussianToLp_pos {X : Ω → ℝ} [Fact (1 ≤ p)]
    (hX : HasLaw X (gaussianReal 0 1) P) (hp : p ≠ ∞) :
    0 < ‖standardGaussianToLp hX hp‖ := by
  rw [norm_pos_iff]
  intro hzero
  have hmem := hX.hasGaussianLaw.memLp hp
  have hzeroLp :
      hmem.toLp X = (MemLp.zero : MemLp (0 : Ω → ℝ) p P).toLp 0 := by
    simpa [standardGaussianToLp] using hzero
  have hzero_ae : X =ᵐ[P] 0 :=
    (MemLp.toLp_eq_toLp_iff hmem MemLp.zero).1 hzeroLp
  have hvar : Var[X; P] = 1 := by
    simpa using hX.variance_eq
  have hzvar : Var[X; P] = 0 := (variance_congr hzero_ae).trans (variance_zero P)
  linarith

-- If `X` is a standard Gaussian and `a ∈ ℝ`,
-- then `aX` is a Gaussian with variance `a²`.
private lemma hasLaw_const_mul_standardGaussian {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) (a : ℝ) :
    HasLaw (fun ω ↦ a * X ω) (gaussianReal 0 (‖a‖₊ ^ 2)) P := by
  convert gaussianReal_const_mul hX a using 1
  congr 2
  · simp
  · ext; simp [sq_abs]

-- A finite linear combination of independent standard Gaussians, `∑ₖ aₖXₖ`
-- is a centered Gaussian. Moreover, its variance is precisely `∑ₖ ∣aₖ∣²`.
private lemma hasLaw_sum_standardGaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) (s : Finset ℕ) (a : ℕ → ℝ) :
    HasLaw (fun ω ↦ ∑ i ∈ s, a i * X i ω)
      (gaussianReal 0 (∑ i ∈ s, ‖a i‖₊ ^ 2)) P := by
  letI := h_indep.isProbabilityMeasure
  let Y : ℕ → Ω → ℝ := fun i ω ↦ a i * X i ω
  have hY_law (i : ℕ) : HasLaw (Y i) (gaussianReal 0 (‖a i‖₊ ^ 2)) P :=
    hasLaw_const_mul_standardGaussian (hX i) (a i)
  have hY_indep : iIndepFun Y P := by
    simpa [Y, Function.comp_def] using
      h_indep.comp (fun i x ↦ a i * x) (by fun_prop)
  change HasLaw (fun ω ↦ ∑ i ∈ s, Y i ω)
    (gaussianReal 0 (∑ i ∈ s, ‖a i‖₊ ^ 2)) P
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨by fun_prop, ?_⟩
      simp [gaussianReal_zero_var]
  | @insert i s hi ih =>
      have ih' : HasLaw (∑ j ∈ s, Y j)
          (gaussianReal 0 (∑ j ∈ s, ‖a j‖₊ ^ 2)) P := by
        apply ih.congr
        filter_upwards
        simp
      have hsum_indep :=
        hY_indep.indepFun_finsetSum_of_notMem₀ (fun j ↦ (hY_law j).aemeasurable) hi
      have hadd := hsum_indep.hasLaw_add ih' (hY_law i)
      rw [gaussianReal_conv_gaussianReal] at hadd
      convert hadd using 1
      · ext ω
        simp [Finset.sum_insert hi, add_comm]
      · simp [Finset.sum_insert hi, add_comm]

-- Scalar multiplication in `Lᵖ` is represented almost everywhere
-- by pointwise multiplication of the underlying standard Gaussian.
private lemma coeFn_smul_standardGaussianToLp {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) P) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : ℝ) :
    ⇑(a • standardGaussianToLp hX hp) =ᵐ[P] fun ω ↦ a * X ω := by
  have hstd : ⇑(standardGaussianToLp hX hp) =ᵐ[P] X :=
    MemLp.coeFn_toLp (hX.hasGaussianLaw.memLp hp)
  filter_upwards [Lp.coeFn_smul a (standardGaussianToLp hX hp),
    hstd] with ω hsmul hXω
  rw [hsmul, Pi.smul_apply, hXω]
  simp only [smul_eq_mul]

-- A finite sum of Gaussian `Lᵖ` classes is represented almost
-- everywhere by the corresponding pointwise finite Gaussian sum.
private lemma coeFn_sum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ⇑(∑ i ∈ s, a i • standardGaussianToLp (hX i) hp) =ᵐ[P]
      fun ω ↦ ∑ i ∈ s, a i * X i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℝ p P)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (a i • standardGaussianToLp (hX i) hp)
        (∑ j ∈ s, a j • standardGaussianToLp (hX j) hp),
        coeFn_smul_standardGaussianToLp (hX i) hp (a i), ih]
        with ω hadd hsmul hsum
      rw [hadd, Pi.add_apply, hsmul, hsum]

-- The `Lᵖ` norm of a finite Gaussian sum is the standard Gaussian
-- `Lᵖ` norm multiplied by the Euclidean norm of its coefficient vector.
private lemma norm_sum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ i ∈ s, a i • standardGaussianToLp (hX i) hp‖ =
      ‖standardGaussianToLp (hX 0) hp‖ * Real.sqrt (∑ i ∈ s, (a i) ^ 2) := by
  let na : ℝ := ∑ i ∈ s, (a i) ^ 2
  have hna : 0 ≤ na := by positivity
  have hscaled :
      HasLaw (fun ω ↦ Real.sqrt na * X 0 ω)
        (gaussianReal 0 (∑ i ∈ s, ‖a i‖₊ ^ 2)) P := by
    convert hasLaw_const_mul_standardGaussian (hX 0) (Real.sqrt na) using 1
    congr 2
    ext
    simp [na, Real.sq_sqrt hna, sq_abs]
  have hsum := hasLaw_sum_standardGaussian hX h_indep s a
  have heLp := (hsum.identDistrib hscaled).eLpNorm_eq p
  have hcoe := coeFn_sum_standardGaussianToLp hX hp s a
  have hscaled_coe := coeFn_smul_standardGaussianToLp (hX 0) hp (Real.sqrt na)
  calc
    ‖∑ i ∈ s, a i • standardGaussianToLp (hX i) hp‖ =
        ENNReal.toReal (eLpNorm (fun ω ↦ ∑ i ∈ s, a i * X i ω) p P) := by
      rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
    _ = ENNReal.toReal (eLpNorm (fun ω ↦ Real.sqrt na * X 0 ω) p P) := by
      exact congrArg ENNReal.toReal heLp
    _ = ‖Real.sqrt na • standardGaussianToLp (hX 0) hp‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae hscaled_coe]
    _ = ‖standardGaussianToLp (hX 0) hp‖ * Real.sqrt (∑ i ∈ s, (a i) ^ 2) := by
      rw [norm_smul_of_nonneg (Real.sqrt_nonneg na)]
      simp only [na, mul_comm]

-- Square-summability of the coefficients makes the
-- associated Gaussian series summable in the `Lᵖ` sense.
private lemma summable_smul_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : ℓ²(ℕ, ℝ)) :
    Summable (fun n ↦ a n • standardGaussianToLp (hX n) hp) := by
  let c := ‖standardGaussianToLp (hX 0) hp‖
  have hc : 0 < c := norm_standardGaussianToLp_pos (hX 0) hp
  have hbasis : Summable (fun n ↦ lp.single 2 n (a n)) :=
    (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) a).summable
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s, hs⟩ :=
    summable_iff_vanishing_norm.1 hbasis (ε / c) (div_pos hε hc)
  refine ⟨s, ?_⟩
  intro t ht
  have hgauss :
      ‖∑ i ∈ t, a i • standardGaussianToLp (hX i) hp‖ =
        c * Real.sqrt (∑ i ∈ t, (a i) ^ 2) := by
    simpa [c] using norm_sum_standardGaussianToLp hX h_indep hp t a
  have hbasisnorm :
      ‖∑ i ∈ t, lp.single 2 i (a i)‖ =
        Real.sqrt (∑ i ∈ t, (a i) ^ 2) := by
    have hsq := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun i : ℕ ↦ a i) t
    norm_num [Real.norm_eq_abs, sq_abs] at hsq
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  calc
    ‖∑ i ∈ t, a i • standardGaussianToLp (hX i) hp‖ =
        c * ‖∑ i ∈ t, lp.single 2 i (a i)‖ := by rw [hgauss, hbasisnorm]
    _ < c * (ε / c) := mul_lt_mul_of_pos_left (hs t ht) hc
    _ = ε := by field_simp

-- The `Lᵖ` sum of a square-summable Gaussian series is centered Gaussian
-- with variance equal to the squared `ℓ²` norm of its coefficient sequence.
private lemma hasLaw_tsum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : ℓ²(ℕ, ℝ)) :
    HasLaw (fun ω ↦ (∑' n, a n • standardGaussianToLp (hX n) hp) ω)
      (gaussianReal 0 (‖a‖₊ ^ 2)) P := by
  have hsum := summable_smul_standardGaussianToLp hX h_indep hp a
  letI := h_indep.isProbabilityMeasure
  let b : ℕ → ℓ²(ℕ, ℝ) := fun n ↦
    ∑ i ∈ Finset.range n, lp.single 2 i (a i)
  let S : ℕ → Lp ℝ p P := fun n ↦
    ∑ i ∈ Finset.range n, a i • standardGaussianToLp (hX i) hp
  let Y : Lp ℝ p P := ∑' n, a n • standardGaussianToLp (hX n) hp
  let R : ℕ → Ω → ℝ := fun n ω ↦ ‖b n‖ * X 0 ω
  let Z : Ω → ℝ := fun ω ↦ ‖a‖ * X 0 ω
  have hZlaw : HasLaw Z (gaussianReal 0 (‖a‖₊ ^ 2)) P := by
    simpa [Z] using hasLaw_const_mul_standardGaussian (hX 0) ‖a‖
  have hS_tendsto : Filter.Tendsto S Filter.atTop (nhds Y) := by
    simpa [S, Y] using hsum.hasSum.tendsto_sum_nat
  have hb_tendsto : Filter.Tendsto b Filter.atTop (nhds a) := by
    simpa [b] using
      (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) a).tendsto_sum_nat
  have hSYdist :=
    (tendstoInMeasure_of_tendsto_Lp hS_tendsto).tendstoInDistribution
      (fun n ↦ (Lp.aestronglyMeasurable (S n)).aemeasurable)
  have hb_norm : Filter.Tendsto (fun n ↦ ‖b n‖) Filter.atTop (nhds ‖a‖) :=
    hb_tendsto.norm
  have hRZ_ae : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun n ↦ R n ω) Filter.atTop (nhds (Z ω)) := by
    filter_upwards with ω
    simpa [R, Z] using hb_norm.mul_const (X 0 ω)
  have hR_meas (n : ℕ) : AEStronglyMeasurable (R n) P :=
    ((hX 0).aemeasurable.const_mul ‖b n‖).aestronglyMeasurable
  have hRZdist :=
    (tendstoInMeasure_of_tendsto_ae hR_meas hRZ_ae).tendstoInDistribution
      (fun n ↦ (hR_meas n).aemeasurable)
  have hSlaw (n : ℕ) :
      HasLaw (fun ω ↦ S n ω)
        (gaussianReal 0 (∑ i ∈ Finset.range n, ‖a i‖₊ ^ 2)) P := by
    apply (hasLaw_sum_standardGaussian hX h_indep (Finset.range n) a).congr
    simpa [S] using coeFn_sum_standardGaussianToLp hX hp (Finset.range n) a
  have hb_nnnorm_sq (n : ℕ) :
      ‖(‖b n‖ : ℝ)‖₊ ^ 2 = ∑ i ∈ Finset.range n, ‖a i‖₊ ^ 2 := by
    ext
    simpa [b, Real.norm_eq_abs, sq_abs] using
      lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num)
        (fun i : ℕ ↦ a i) (Finset.range n)
  have hRlaw (n : ℕ) :
      HasLaw (R n) (gaussianReal 0 (∑ i ∈ Finset.range n, ‖a i‖₊ ^ 2)) P := by
    rw [← hb_nnnorm_sq n]
    simpa [R] using hasLaw_const_mul_standardGaussian (hX 0) ‖b n‖
  have hSRident (n : ℕ) : IdentDistrib (fun ω ↦ S n ω) (R n) P P :=
    (hSlaw n).identDistrib (hRlaw n)
  have hSZdist : TendstoInDistribution (fun n ↦ fun ω ↦ S n ω)
      Filter.atTop Z (fun _ ↦ P) P :=
    { forall_aemeasurable := fun n ↦ (hSlaw n).aemeasurable
      aemeasurable_limit := hZlaw.aemeasurable
      tendsto := by
        apply hRZdist.tendsto.congr'
        filter_upwards with n
        apply Subtype.ext
        exact (hSRident n).map_eq.symm }
  have hmap := tendstoInDistribution_unique (fun n ω ↦ S n ω) hSYdist hSZdist
  have hZY : IdentDistrib Z (fun ω ↦ Y ω) P P :=
    ⟨hZlaw.aemeasurable, (Lp.aestronglyMeasurable Y).aemeasurable, hmap.symm⟩
  simpa [Y] using hZY.hasLaw hZlaw

-- The `Lᵖ` norm of an infinite Gaussian series is the standard
-- Gaussian `Lᵖ` norm multiplied by the `ℓ²` norm of its coefficients.
private lemma norm_tsum_standardGaussianToLp {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : ℓ²(ℕ, ℝ)) :
  ‖∑' n, a n • standardGaussianToLp (hX n) hp‖ =
      ‖standardGaussianToLp (hX 0) hp‖ * ‖a‖ := by
  let Y : Lp ℝ p P := ∑' n, a n • standardGaussianToLp (hX n) hp
  have hYlaw := hasLaw_tsum_standardGaussianToLp hX h_indep hp a
  have hZlaw :
      HasLaw (fun ω ↦ ‖a‖ * X 0 ω) (gaussianReal 0 (‖a‖₊ ^ 2)) P := by
    simpa using hasLaw_const_mul_standardGaussian (hX 0) ‖a‖
  have heLp := (hYlaw.identDistrib hZlaw).eLpNorm_eq p
  calc
    ‖∑' n, a n • standardGaussianToLp (hX n) hp‖ =
        ENNReal.toReal (eLpNorm (fun ω ↦ Y ω) p P) := by rw [Lp.norm_def]
    _ = ENNReal.toReal (eLpNorm (fun ω ↦ ‖a‖ * X 0 ω) p P) :=
      congrArg ENNReal.toReal heLp
    _ = ‖‖a‖ • standardGaussianToLp (hX 0) hp‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae
      (coeFn_smul_standardGaussianToLp (hX 0) hp ‖a‖)]
    _ = ‖standardGaussianToLp (hX 0) hp‖ * ‖a‖ := by
      rw [norm_smul_of_nonneg (norm_nonneg a)]
      simp only [mul_comm]

-- The map induced by the assigment `eₙ ↦ 1/∣∣N(0, 1)∣∣ₚ Xₙ` defines an
-- linear isometric embedding of `ℓ²(ℕ, ℝ)` into `Lᵖ(μ)`.
private lemma exists_linearIsometry_standardGaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ T : ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] Lp ℝ p P,
      ∀ n, T (lp.single 2 n 1) =
        ‖standardGaussianToLp (hX 0) hp‖⁻¹ • standardGaussianToLp (hX n) hp := by
  let c := ‖standardGaussianToLp (hX 0) hp‖
  have hc : 0 < c := norm_standardGaussianToLp_pos (hX 0) hp
  let g : ℕ → Lp ℝ p P := fun n ↦ standardGaussianToLp (hX n) hp
  have hsum (a : ℓ²(ℕ, ℝ)) : Summable (fun n ↦ a n • g n) := by
    simpa [g] using summable_smul_standardGaussianToLp hX h_indep hp a
  let G : ℓ²(ℕ, ℝ) →ₗ[ℝ] Lp ℝ p P :=
    { toFun := fun a ↦ ∑' n, a n • g n
      map_add' := by
        intro a b
        apply HasSum.unique (hsum (a + b)).hasSum
        simpa only [lp.coeFn_add, Pi.add_apply, add_smul] using
          (hsum a).hasSum.add (hsum b).hasSum
      map_smul' := by
        intro r a
        apply HasSum.unique (hsum (r • a)).hasSum
        have hterm :
            (fun n ↦ (r • a) n • g n) = (fun n ↦ r • (a n • g n)) := by
          funext n
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
        rw [hterm]
        exact HasSum.const_smul r (hsum a).hasSum }
  have hG_norm (a : ℓ²(ℕ, ℝ)) : ‖G a‖ = c * ‖a‖ := by
    simpa [G, g, c] using norm_tsum_standardGaussianToLp hX h_indep hp a
  let T : ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] Lp ℝ p P :=
    { toLinearMap := c⁻¹ • G
      norm_map' := by
        intro a
        rw [LinearMap.smul_apply, norm_smul, hG_norm]
        simp [Real.norm_eq_abs, abs_of_pos hc, hc.ne'] }
  have hG_single (n : ℕ) : G (lp.single 2 n 1) = g n := by
    change (∑' i, (lp.single 2 n 1) i • g i) = g n
    rw [tsum_eq_single n]
    · simp
    · intro j hj
      rw [lp.single_apply, Pi.single_eq_of_ne hj, zero_smul]
  refine ⟨T, ?_⟩
  intro n
  simpa [T, c, g] using congrArg (fun z ↦ c⁻¹ • z) (hG_single n)

-- The range of the linear isometric embedding `eₙ ↦ 1/∣∣N(0, 1)∣∣ₚ Xₙ` is exactly the
-- closed linear span of the sequence of independent standard Gaussians in `Lᴾ(μ)`.
private lemma range_linearIsometry_standardGaussian {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (T : ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] Lp ℝ p P)
    (hT : ∀ n, T (lp.single 2 n 1) =
      ‖standardGaussianToLp (hX 0) hp‖⁻¹ • standardGaussianToLp (hX n) hp) :
    LinearMap.range T.toLinearMap =
      (Submodule.span ℝ (Set.range fun n ↦ standardGaussianToLp (hX n) hp)
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
      ‖standardGaussianToLp (hX 0) hp‖⁻¹ <|
        Submodule.le_topologicalClosure _ <| Submodule.subset_span ⟨n, rfl⟩
  · have hclosed : IsClosed (T.range : Set (Lp ℝ p P)) := by
      exact T.isometry.antilipschitz.isClosed_range T.isometry.uniformContinuous
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hclosed
    rintro _ ⟨n, rfl⟩
    have hc := norm_standardGaussianToLp_pos (hX 0) hp
    refine ⟨‖standardGaussianToLp (hX 0) hp‖ • lp.single 2 n 1, ?_⟩
    simp [map_smul, hT n, smul_smul, hc.ne']

-- The closed linear span in `Lᵖ` of an independent sequence of standard
-- real Gaussian random variables is linearly isometric to `ℓ²(ℕ, ℝ)`.
theorem nonempty_linearIsometryEquiv_standardGaussian_closedSpan
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P)
    (h_indep : iIndepFun X P) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Nonempty
      (ℓ²(ℕ, ℝ) ≃ₗᵢ[ℝ]
        (Submodule.span ℝ (Set.range fun n ↦ standardGaussianToLp (hX n) hp)
          |>.topologicalClosure)) := by
  obtain ⟨T, hT⟩ := exists_linearIsometry_standardGaussian hX h_indep hp
  have hRange := range_linearIsometry_standardGaussian hX hp T hT
  exact ⟨T.equivRange.trans (LinearIsometryEquiv.ofEq _ _ hRange)⟩

/-
/-- If `μ` is atomless, then `Lᵖ(μ)` contains a linear isometric copy of `ℓ²(ℕ, ℝ)`. -/
theorem nonempty_linearIsometry_l2_Lp
    [IsProbabilityMeasure P] (hP : P.HasNoAtoms)
    [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Nonempty (ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] Lp ℝ p P) := by
  obtain ⟨X, hX, h_indep⟩ := hP.exists_iid (gaussianReal 0 1)
  obtain ⟨T, _⟩ := exists_linearIsometry_standardGaussian hX h_indep hp
  exact ⟨T⟩ -/
