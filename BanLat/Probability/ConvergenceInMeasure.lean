import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Completeness of convergence in measure

On a finite measure space, every sequence of a.e.-strongly measurable real-valued functions
which is Cauchy in measure converges in measure to an a.e.-strongly measurable function. In
particular, every sequence which is Cauchy in probability converges in probability.
-/

open Filter MeasureTheory

open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A sequence of functions is Cauchy in measure if the measure of the set on which two
terms are separated by at least `ε` tends to zero as both indices tend to infinity. -/
def CauchyInMeasure {E : Type*} [PseudoMetricSpace E]
    (μ : Measure Ω) (f : ℕ → Ω → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun nm : ℕ × ℕ ↦ μ {ω | ε ≤ dist (f nm.1 ω) (f nm.2 ω)}) atTop (nhds 0)

/-- If two sequences of real-valued functions converge in measure, then their pointwise sums
converge in measure to the sum of their limits. -/
theorem tendstoInMeasure_add_real [IsFiniteMeasure μ]
    {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg_meas : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : TendstoInMeasure μ f atTop F)
    (hg : TendstoInMeasure μ g atTop G) :
    TendstoInMeasure μ (fun n ω ↦ f n ω + g n ω) atTop (fun ω ↦ F ω + G ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff fun n ↦ (hf_meas n).add (hg_meas n)).2
  intro ns hns
  obtain ⟨ms, hms, hfm⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hgm⟩ :=
    ((hg.comp hns.tendsto_atTop).comp hms.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks, hms.comp hks, ?_⟩
  filter_upwards [hfm, hgm] with ω hfω hgω
  exact (hfω.comp hks.tendsto_atTop).add hgω

/-- If a sequence of real-valued functions converges in measure, then multiplication by a fixed
real scalar preserves its convergence in measure. -/
theorem tendstoInMeasure_const_mul_real [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hf : TendstoInMeasure μ f atTop F) (r : ℝ) :
    TendstoInMeasure μ (fun n ω ↦ r * f n ω) atTop (fun ω ↦ r * F ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff fun n ↦ (hf_meas n).const_mul r).2
  intro ns hns
  obtain ⟨ms, hms, hfm⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hfm] with ω hfω
  exact hfω.const_mul r

private lemma ofReal_one_div_two_pow (k : ℕ) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ k) = (2 : ENNReal)⁻¹ ^ k := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private lemma exists_tendstoInMeasure_of_dyadic_cauchy
    {f : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hcau : ∀ k, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      μ {ω | (2 : ENNReal)⁻¹ ^ k ≤ edist (f n ω) (f m ω)} ≤ (2 : ENNReal)⁻¹ ^ k) :
    ∃ g, TendstoInMeasure μ f atTop g := by
  classical
  let N : ℕ → ℕ := fun k ↦ (hcau k).choose
  have hN (k n m : ℕ) (hn : N k ≤ n) (hm : N k ≤ m) :
      μ {ω | (2 : ENNReal)⁻¹ ^ k ≤ edist (f n ω) (f m ω)} ≤ (2 : ENNReal)⁻¹ ^ k := by
    exact (hcau k).choose_spec n m hn hm
  let ns : ℕ → ℕ := fun k ↦
    Nat.rec (N 0) (fun j previous ↦ max (N (j + 1)) (previous + 1)) k
  have hNns (k : ℕ) : N k ≤ ns k := by
    cases k <;> simp [ns]
  have hns_strict : StrictMono ns := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    simp only [ns]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let A : ℕ → Set Ω := fun k ↦
    {ω | (2 : ENNReal)⁻¹ ^ k ≤ edist (f (ns (k + 1)) ω) (f (ns k) ω)}
  have hμA (k : ℕ) : μ (A k) ≤ (2 : ENNReal)⁻¹ ^ k := by
    exact hN k _ _ ((hNns k).trans (hns_strict (Nat.lt_succ_self k)).le) (hNns k)
  have hsumA : ∑' k, μ (A k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμA)
    simp [ENNReal.tsum_geometric]
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ A k := ae_eventually_notMem hsumA
  have hsub : ∀ᵐ ω ∂μ, ∃ y : ℝ, Tendsto (fun k ↦ f (ns k) ω) atTop (nhds y) := by
    filter_upwards [hae] with ω hω
    have hdiff : ∀ᶠ k in atTop,
        ‖f (ns (k + 1)) ω - f (ns k) ω‖ ≤ ((1 / 2 : ℝ) ^ k) := by
      filter_upwards [hω] with k hk
      change ¬(2 : ENNReal)⁻¹ ^ k ≤ edist (f (ns (k + 1)) ω) (f (ns k) ω) at hk
      rw [not_le, edist_dist] at hk
      rw [← ofReal_one_div_two_pow k, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hk
      simpa [Real.dist_eq, Real.norm_eq_abs] using hk.le
    have hdiff_sum : Summable (fun k ↦ f (ns (k + 1)) ω - f (ns k) ω) :=
      Summable.of_norm_bounded_eventually_nat
        (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)) hdiff
    have ht := hdiff_sum.hasSum.tendsto_sum_nat
    rw [funext fun k ↦ Finset.sum_range_sub (fun j ↦ f (ns j) ω) k] at ht
    exact ⟨∑' k, (f (ns (k + 1)) ω - f (ns k) ω) + f (ns 0) ω,
      by simpa using ht.add_const (f (ns 0) ω)⟩
  let g : Ω → ℝ := fun ω ↦
    if h : ∃ y : ℝ, Tendsto (fun k ↦ f (ns k) ω) atTop (nhds y) then h.choose else 0
  have hsubg : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ f (ns k) ω) atTop (nhds (g ω)) := by
    filter_upwards [hsub] with ω hω
    simpa only [g, dif_pos hω] using hω.choose_spec
  have hsubMeasure : TendstoInMeasure μ (fun k ↦ f (ns k)) atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ hf (ns k)) hsubg
  refine ⟨g, tendstoInMeasure_of_ne_top ?_⟩
  intro ε hε hε_top
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hhalf : 0 < min (ε / 2) (δ / 2) := by
    rw [lt_min_iff]
    exact ⟨ENNReal.div_pos hε.ne' (by norm_num), ENNReal.div_pos hδ.ne' (by norm_num)⟩
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hhalf.ne'
  let r : ENNReal := (2 : ENNReal)⁻¹ ^ k
  have hr : 0 < r := by
    exact ENNReal.pow_pos (by simp) k
  change r < min (ε / 2) (δ / 2) at hk
  have hrrε : r + r < ε :=
    (ENNReal.add_lt_add (hk.trans_le (min_le_left _ _))
      (hk.trans_le (min_le_left _ _))).trans_eq
      (ENNReal.add_halves ε)
  have hrrδ : r + r < δ :=
    (ENNReal.add_lt_add (hk.trans_le (min_le_right _ _))
      (hk.trans_le (min_le_right _ _))).trans_eq
      (ENNReal.add_halves δ)
  have hsubr := hsubMeasure r hr
  rw [ENNReal.tendsto_atTop_zero] at hsubr
  obtain ⟨J, hJ⟩ := hsubr r hr
  let j := max J (N k)
  have hgj : μ {ω | r ≤ edist (f (ns j) ω) (g ω)} ≤ r :=
    hJ j (le_max_left _ _)
  have hNj : N k ≤ ns j := by
    exact (show N k ≤ j by simp [j]).trans (hns_strict.id_le j)
  refine ⟨N k, fun n hn ↦ ?_⟩
  have hnj : μ {ω | r ≤ edist (f n ω) (f (ns j) ω)} ≤ r := by
    simpa only [r] using hN k n (ns j) hn hNj
  have hsubset : {ω | ε ≤ edist (f n ω) (g ω)} ⊆
      {ω | r ≤ edist (f n ω) (f (ns j) ω)} ∪
        {ω | r ≤ edist (f (ns j) ω) (g ω)} := by
    intro ω hω
    by_contra hmem
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hmem
    exact (not_lt_of_ge hω) <|
      (edist_triangle (f n ω) (f (ns j) ω) (g ω)).trans_lt
        ((ENNReal.add_lt_add hmem.1 hmem.2).trans hrrε)
  calc
    μ {ω | ε ≤ edist (f n ω) (g ω)} ≤
        μ ({ω | r ≤ edist (f n ω) (f (ns j) ω)} ∪
          {ω | r ≤ edist (f (ns j) ω) (g ω)}) := measure_mono hsubset
    _ ≤ μ {ω | r ≤ edist (f n ω) (f (ns j) ω)} +
        μ {ω | r ≤ edist (f (ns j) ω) (g ω)} := measure_union_le _ _
    _ ≤ r + r := add_le_add hnj hgj
    _ ≤ δ := hrrδ.le

/-- A sequence of a.e.-strongly measurable real-valued functions which is Cauchy in measure
converges in measure to an a.e.-strongly measurable function. -/
theorem exists_tendstoInMeasure_of_cauchySeq
    {f : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hcau : CauchyInMeasure μ f) :
    ∃ g, TendstoInMeasure μ f atTop g := by
  apply exists_tendstoInMeasure_of_dyadic_cauchy hf
  intro k
  have hk_pos : 0 < (2 : ENNReal)⁻¹ ^ k := ENNReal.pow_pos (by simp) k
  have hk_real_pos : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) k
  have h := hcau ((1 / 2 : ℝ) ^ k) hk_real_pos
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨nm, hnm⟩ := h ((2 : ENNReal)⁻¹ ^ k) hk_pos
  refine ⟨max nm.1 nm.2, fun n m hn hm ↦ ?_⟩
  have hbound := hnm (n, m) ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hm⟩
  have hpow := ofReal_one_div_two_pow k
  simp_rw [edist_dist]
  rw [← hpow]
  have hset : {ω | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≤
      ENNReal.ofReal (dist (f n ω) (f m ω))} =
      {ω | (1 / 2 : ℝ) ^ k ≤ dist (f n ω) (f m ω)} := by
    ext ω
    exact ENNReal.ofReal_le_ofReal_iff dist_nonneg
  rw [hset, hpow]
  exact hbound

/-- The space `L⁰(μ)` of a.e.-strongly measurable real-valued functions modulo a.e. equality is
complete with respect to convergence in measure. -/
theorem exists_tendstoInMeasure_lp_zero_of_cauchyInMeasure
    [IsFiniteMeasure μ] (f : ℕ → Lp ℝ 0 μ)
    (hf : CauchyInMeasure μ fun n ↦ f n) :
    ∃ g : Lp ℝ 0 μ, TendstoInMeasure μ (fun n ↦ f n) atTop g := by
  obtain ⟨g, hg⟩ :=
    exists_tendstoInMeasure_of_cauchySeq (fun n ↦ Lp.aestronglyMeasurable (f n)) hf
  have hg_memLp : MemLp g 0 μ := memLp_zero_iff_aestronglyMeasurable.2 <|
    TendstoInMeasure.aestronglyMeasurable (fun n ↦ Lp.aestronglyMeasurable (f n)) hg
  refine ⟨hg_memLp.toLp g, ?_⟩
  exact hg.congr_right hg_memLp.coeFn_toLp.symm

end MeasureTheory
