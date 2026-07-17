import BanLat.Probability.ConvergenceInMeasure
import BanLat.Probability.Distributions.Stable.HasSymmetricStableLaw.Moments
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Symmetric stable sequences in `Lᵖ(P)` spaces

## Main theorems

• Let `(Ω, Σ, P)` be a probability space and `(Xₖ)ₖ` a sequence of independent, identically
distributed, standard symmetric `q`-stable real random variables. For `1 ≤ p < q < 2`, the
closure of their linear span in `Lᵖ(P)` is linearly isometric to `ℓ^q(ℕ, ℝ)`.

• For `0 < p < 1` and `p < q < 2`, the normalized stable map defines an injective linear map
`ℓ^q(ℕ, ℝ) ↦ Lᵖ(P)` which preserves the quasi-norm.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.iIndepFun

open scoped ENNReal NNReal lp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {p : ℝ≥0} {q : ℝ}

/-- The almost-everywhere equivalence class in `Lᵖ`
represented by a standard symmetric `q`-stable random variable. -/
noncomputable def standardQStableToLp {X : Ω → ℝ}
    (hX : HasSymmetricStableLaw X q 1 P)
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    Lp ℝ p P := by
  exact ((hX.memLp_iff hp_pos).2 (Or.inr (Or.inr hpq))).toLp X

/-- A standard symmetric `q`-stable random variable has positive `Lᵖ` norm, so
its almost-everywhere class is non-zero. -/
private lemma norm_standardQStableToLp_pos {X : Ω → ℝ}
    (hX : HasSymmetricStableLaw X q 1 P)
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    0 < ‖standardQStableToLp hX hp_pos hpq‖ := by
  rw [lt_iff_le_and_ne]
  refine ⟨NNReal.coe_nonneg _, fun hzero ↦ ?_⟩
  have hmem : MemLp X p P := (hX.memLp_iff hp_pos).2 (Or.inr (Or.inr hpq))
  have hzero_ae : X =ᵐ[P] 0 :=
    (MemLp.coeFn_toLp hmem).symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp <|
        (Lp.norm_eq_zero_iff (by exact_mod_cast hp_pos)).mp hzero.symm)
  have hscale_zero := hX.scale_eq_zero_iff_ae_eq_zero.mpr hzero_ae
  norm_num at hscale_zero

/-- The `q`-th powers of the absolute coordinates of an element of `ℓ^q` are summable. -/
private lemma summable_nnnorm_rpow (hq_pos : 0 < q)
    (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) :
    Summable (fun n ↦ ‖a n‖₊ ^ q) := by
  rw [← NNReal.summable_coe]
  simpa [NNReal.coe_rpow, ENNReal.toReal_ofReal hq_pos.le] using
    (lp.memℓp a).summable (by simpa [ENNReal.toReal_ofReal hq_pos.le] using hq_pos)

/-- The `q`-th root of the sum of the `q`-th powers of the coordinates is the `ℓ^q` norm. -/
private lemma rpow_tsum_nnnorm_rpow (hq_pos : 0 < q)
    (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) :
    (↑(∑' n, ‖a n‖₊ ^ q) : ℝ) ^ q⁻¹ = ‖a‖ := by
  have hnorm := lp.norm_eq_tsum_rpow (p := ENNReal.ofReal q)
    (by simpa [ENNReal.toReal_ofReal hq_pos.le] using hq_pos) a
  rw [NNReal.coe_tsum]
  simpa [NNReal.coe_rpow, ENNReal.toReal_ofReal hq_pos.le, one_div] using hnorm.symm

/-- Scalar multiplication in `Lᵖ` is homogeneous even when `0 < p < 1`. -/
private lemma norm_smul_Lp (r : ℝ) (f : Lp ℝ p P) :
    ‖r • f‖ = |r| * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_smul r f),
    eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
    Lp.norm_def]

/-- For `0 < p < q < 2`, the assignment `eₙ ↦ Xₙ` extends linearly to a map
`G : ℓ^q(ℕ, ℝ) → Lᵖ(P)` satisfying `‖G a‖ = ‖X₀‖ₚ ‖a‖`. -/
private lemma exists_linearMap_standardQStable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q 1 P)
    (h_indep : iIndepFun X P) (hq_lt_two : q < 2)
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    ∃ G : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗ[ℝ] Lp ℝ p P,
      (∀ a, ‖G a‖ = ‖standardQStableToLp (hX 0) hp_pos hpq‖ * ‖a‖) ∧
      ∀ n, G (lp.single (ENNReal.ofReal q) n 1) =
        standardQStableToLp (hX n) hp_pos hpq := by
  letI := h_indep.isProbabilityMeasure
  have hq_pos : 0 < q := (hX 0).isSymmetricStable_map.index_pos
  let hex (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) :
      ∃ Y : Ω → ℝ,
        TendstoInMeasure P
          (fun N ω ↦ ∑ n ∈ Finset.range N, a n * X n ω) Filter.atTop Y ∧
        HasSymmetricStableLaw Y q (1 * ∑' n, ‖a n‖₊ ^ q) P ∧
        MemLp Y p P ∧
        Filter.Tendsto
          (fun N ↦ lpNorm (fun ω ↦ Y ω - ∑ n ∈ Finset.range N, a n * X n ω) p P)
          Filter.atTop (nhds 0) ∧
        lpNorm Y p P =
          (↑(∑' n, ‖a n‖₊ ^ q) : ℝ) ^ q⁻¹ * lpNorm (X 0) p P :=
    exists_tendstoInMeasure_tendsto_lpNorm_sum_range_mul_of_hasSymmetricStableLaw_of_index_lt_two
      hX h_indep a (summable_nnnorm_rpow hq_pos a) hq_lt_two hp_pos hpq
  let Y : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) → Ω → ℝ := fun a ↦ (hex a).choose
  have hYspec (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) := (hex a).choose_spec
  let hYmem (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) : MemLp (Y a) p P :=
    (hYspec a).2.2.1
  let G : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗ[ℝ] Lp ℝ p P :=
    { toFun := fun a ↦ (hYmem a).toLp (Y a)
      map_add' := by
        intro a b
        have hab := tendstoInMeasure_add_real (hYspec a).1 (hYspec b).1
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
        have hra := tendstoInMeasure_const_mul_real (hYspec a).1 r
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
  let c := ‖standardQStableToLp (hX 0) hp_pos hpq‖
  have hstd_norm : lpNorm (X 0) p P = c := by
    change lpNorm (X 0) p P = ‖standardQStableToLp (hX 0) hp_pos hpq‖
    rw [standardQStableToLp, Lp.norm_toLp,
      toReal_eLpNorm (hX 0).aemeasurable.aestronglyMeasurable]
  have hGnorm (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) : ‖G a‖ = c * ‖a‖ := by
    change ‖(hYmem a).toLp (Y a)‖ = c * ‖a‖
    rw [Lp.norm_toLp, toReal_eLpNorm (hYmem a).1,
      (hYspec a).2.2.2.2, rpow_tsum_nnnorm_rpow hq_pos, hstd_norm]
    exact mul_comm _ _
  have hGsingle (n : ℕ) :
      G (lp.single (ENNReal.ofReal q) n 1) = standardQStableToLp (hX n) hp_pos hpq := by
    let e : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) :=
      lp.single (ENNReal.ofReal q) n 1
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
      MemLp.coeFn_toLp ((hX n).memLp_iff hp_pos |>.2 (Or.inr (Or.inr hpq)))]
      with ω hleft huniqω hright
    simpa [G, e, standardQStableToLp] using hleft.trans (huniqω.trans hright.symm)
  exact ⟨G, fun a ↦ by simpa [c] using hGnorm a, hGsingle⟩

/-- Normalizing the stable map by `‖X₀‖ₚ⁻¹` gives a norm-preserving linear map
sending `eₙ` to `‖X₀‖ₚ⁻¹Xₙ`. -/
private lemma exists_linearMap_standardQStable_norm_eq {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q 1 P)
    (h_indep : iIndepFun X P) (hq_lt_two : q < 2)
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    ∃ T : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗ[ℝ] Lp ℝ p P,
      (∀ a, ‖T a‖ = ‖a‖) ∧
      ∀ n, T (lp.single (ENNReal.ofReal q) n 1) =
        ‖standardQStableToLp (hX 0) hp_pos hpq‖⁻¹ •
          standardQStableToLp (hX n) hp_pos hpq := by
  obtain ⟨G, hGnorm, hG⟩ :=
    exists_linearMap_standardQStable hX h_indep hq_lt_two hp_pos hpq
  let c := ‖standardQStableToLp (hX 0) hp_pos hpq‖
  have hc : 0 < c := norm_standardQStableToLp_pos (hX 0) hp_pos hpq
  let T : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗ[ℝ] Lp ℝ p P := c⁻¹ • G
  have hTnorm (a : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q)) : ‖T a‖ = ‖a‖ := by
    change ‖c⁻¹ • G a‖ = ‖a‖
    rw [norm_smul_Lp, hGnorm]
    simp [c, abs_of_pos hc, hc.ne']
  refine ⟨T, hTnorm, ?_⟩
  intro n
  simpa [T, c] using congrArg (fun z ↦ c⁻¹ • z) (hG n)

/-- For `1 ≤ p < q < 2`, the previous map `T : ℓ^q(ℕ, ℝ) → Lᵖ(P)` is a linear isometric
embedding of `ℓ^q(ℕ, ℝ)` into `Lᵖ(P)`. -/
private lemma exists_linearIsometry_standardQStable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q 1 P)
    (h_indep : iIndepFun X P) (hq_lt_two : q < 2)
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ ENNReal.ofReal q)]
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    ∃ T : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗᵢ[ℝ] Lp ℝ p P,
      ∀ n, T (lp.single (ENNReal.ofReal q) n 1) =
        ‖standardQStableToLp (hX 0) hp_pos hpq‖⁻¹ •
          standardQStableToLp (hX n) hp_pos hpq := by
  obtain ⟨T, hTnorm, hT⟩ :=
    exists_linearMap_standardQStable_norm_eq hX h_indep hq_lt_two hp_pos hpq
  refine ⟨{ toLinearMap := T, norm_map' := hTnorm }, ?_⟩
  exact hT

/-- For `1 ≤ p < q < 2`, the range of the linear isometric embedding
`T : ℓ^q(ℕ, ℝ) → Lᵖ(P)`, `eₙ ↦ ‖X₀‖ₚ⁻¹Xₙ`, is the closed linear span of
the standard symmetric `q`-stable sequence. -/
private lemma range_linearIsometry_standardQStable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasSymmetricStableLaw (X n) q 1 P)
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ ENNReal.ofReal q)]
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q)
    (T : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗᵢ[ℝ] Lp ℝ p P)
    (hT : ∀ n, T (lp.single (ENNReal.ofReal q) n 1) =
      ‖standardQStableToLp (hX 0) hp_pos hpq‖⁻¹ •
        standardQStableToLp (hX n) hp_pos hpq) :
    LinearMap.range T.toLinearMap =
      (Submodule.span ℝ
        (Set.range fun n ↦ standardQStableToLp (hX n) hp_pos hpq)
        |>.topologicalClosure) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := lp.hasSum_single (p := ENNReal.ofReal q) ENNReal.ofReal_ne_top x
    have hTx : HasSum
        (fun n ↦ T (lp.single (ENNReal.ofReal q) n (x n))) (T x) := by
      simpa only [Function.comp_apply] using hx.map T T.continuous
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hTx ?_
    filter_upwards with s
    apply Submodule.sum_mem
    intro n _
    have hsingle : lp.single (E := fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) n (x n) =
        (x n) • lp.single (E := fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) n (1 : ℝ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hsingle, map_smul, hT n]
    exact Submodule.smul_mem _ (x n) <| Submodule.smul_mem _
      ‖standardQStableToLp (hX 0) hp_pos hpq‖⁻¹ <|
        Submodule.le_topologicalClosure _ <| Submodule.subset_span ⟨n, rfl⟩
  · have hclosed : IsClosed (T.range : Set (Lp ℝ p P)) := by
      exact T.isometry.antilipschitz.isClosed_range T.isometry.uniformContinuous
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hclosed
    rintro _ ⟨n, rfl⟩
    have hc := norm_standardQStableToLp_pos (hX 0) hp_pos hpq
    refine ⟨‖standardQStableToLp (hX 0) hp_pos hpq‖ •
      lp.single (ENNReal.ofReal q) n 1, ?_⟩
    simp [map_smul, hT n, smul_smul, hc.ne']

/-- For `1 ≤ p < q < 2`, the closed linear span in `Lᵖ` of an independent sequence of
standard symmetric `q`-stable random variables is linearly isometric to `ℓ^q(ℕ, ℝ)`. -/
theorem nonempty_linearIsometryEquiv_standardQStable_closedSpan
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hX : ∀ n, HasSymmetricStableLaw (X n) q 1 P)
    (h_indep : iIndepFun X P) (hq_lt_two : q < 2)
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ ENNReal.ofReal q)]
    (hp_pos : 0 < p) (hpq : (p : ℝ) < q) :
    Nonempty
      (lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) ≃ₗᵢ[ℝ]
        (Submodule.span ℝ
          (Set.range fun n ↦ standardQStableToLp (hX n) hp_pos hpq)
          |>.topologicalClosure)) := by
  obtain ⟨T, hT⟩ :=
    exists_linearIsometry_standardQStable hX h_indep hq_lt_two hp_pos hpq
  have hRange := range_linearIsometry_standardQStable hX hp_pos hpq T hT
  exact ⟨T.equivRange.trans (LinearIsometryEquiv.ofEq _ _ hRange)⟩

/-- For `0 < p < 1` and `p < q < 2`, the normalized stable map embeds `ℓ^q(ℕ, ℝ)` linearly
into `Lᵖ`, preserves the quasi-norm, and sends `eₙ ↦ ‖X₀‖ₚ⁻¹ · Xₙ`. -/
theorem exists_linearMap_standardQStable_preserving_quasiNorm
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hX : ∀ n, HasSymmetricStableLaw (X n) q 1 P)
    (h_indep : iIndepFun X P) (hq_lt_two : q < 2)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hpq : (p : ℝ) < q) :
    ∃ T : lp (fun _ : ℕ ↦ ℝ) (ENNReal.ofReal q) →ₗ[ℝ] Lp ℝ p P,
      Function.Injective T ∧
      (∀ a, ‖T a‖ = ‖a‖) ∧
      ∀ n, T (lp.single (ENNReal.ofReal q) n 1) =
        ‖standardQStableToLp (hX 0) hp_pos hpq‖⁻¹ •
          standardQStableToLp (hX n) hp_pos hpq := by
  have _hp_lt_one := hp_lt_one
  obtain ⟨T, hTnorm, hT⟩ :=
    exists_linearMap_standardQStable_norm_eq hX h_indep hq_lt_two hp_pos hpq
  have hTinj : Function.Injective T := by
    intro a b hab
    apply sub_eq_zero.mp
    apply lp.norm_eq_zero_iff.mp
    rw [← hTnorm (a - b), map_sub, hab, sub_self, Lp.norm_zero]
  exact ⟨T, hTinj, hTnorm, hT⟩
