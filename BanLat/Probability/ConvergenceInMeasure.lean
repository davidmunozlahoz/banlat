import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence in measure

We add the following facts about convergence in measure:
  • It is closed under addition and scalar multiplication.
  • Every sequence of real-valued functions which is Cauchy in measure
    converges in measure.
  • Every a.e.-measurable sequence of real-valued functions which is
    Cauchy in measure converges in measure to an a.e.-measurable function.
  • `L⁰(μ)` is complete with respect to convergence in measure.
Following Mathlib's API, convergence in measure is treated independently of
measurability. Measurability of limits is recovered in separate corollaries
when the functions in the sequence are a.e.-measurable.

## Main definitions

* `MeasureTheory.CauchyInMeasure`: a sequence of functions is Cauchy in measure.
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
theorem tendstoInMeasure_add_real
    {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop F)
    (hg : TendstoInMeasure μ g atTop G) :
    TendstoInMeasure μ (fun n ω ↦ f n ω + g n ω) atTop (fun ω ↦ F ω + G ω) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  have hsum : Tendsto
      (fun n ↦ μ {ω | ε / 2 ≤ dist (f n ω) (F ω)} +
        μ {ω | ε / 2 ≤ dist (g n ω) (G ω)}) atTop (nhds 0) := by
    simpa only [zero_add] using (hf (ε / 2) hε2).add (hg (ε / 2) hε2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun n ↦ ?_
  have hsubset : {ω | ε ≤ dist (f n ω + g n ω) (F ω + G ω)} ⊆
      {ω | ε / 2 ≤ dist (f n ω) (F ω)} ∪
        {ω | ε / 2 ≤ dist (g n ω) (G ω)} := by
    intro ω hω
    by_contra hmem
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hmem
    exact (not_lt_of_ge hω) <|
      (dist_add_add_le (f n ω) (g n ω) (F ω) (G ω)).trans_lt <|
        (add_lt_add hmem.1 hmem.2).trans_eq (add_halves ε)
  exact (measure_mono hsubset).trans (measure_union_le _ _)

/-- If a sequence of real-valued functions converges in measure, then multiplication by a fixed
real scalar preserves its convergence in measure. -/
theorem tendstoInMeasure_const_mul_real
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop F) (r : ℝ) :
    TendstoInMeasure μ (fun n ω ↦ r * f n ω) atTop (fun ω ↦ r * F ω) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  by_cases hr : r = 0
  · simp [hr, not_le.mpr hε]
  have hr_pos : 0 < |r| := abs_pos.mpr hr
  have hfun : (fun n ↦ μ {ω | ε ≤ dist (r * f n ω) (r * F ω)}) =
      fun n ↦ μ {ω | ε / |r| ≤ dist (f n ω) (F ω)} := by
    funext n
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, mul_comm |r|]
    exact (div_le_iff₀ hr_pos).symm
  rw [hfun]
  exact hf (ε / |r|) (div_pos hε hr_pos)

private lemma ofReal_one_div_two_pow (k : ℕ) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ k) = (2 : ENNReal)⁻¹ ^ k := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private lemma exists_tendstoInMeasure_of_dyadic_cauchy
    {f : ℕ → Ω → ℝ}
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
  have hconv (ω : Ω) (hω : ∀ᶠ k in atTop, ω ∉ A k) :
      ∃ y : ℝ, Tendsto (fun k ↦ f (ns k) ω) atTop (nhds y) := by
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
  have hμtail (k : ℕ) : μ (⋃ i, A (k + i)) ≤ 2 * (2 : ENNReal)⁻¹ ^ k := by
    calc
      μ (⋃ i, A (k + i)) ≤ ∑' i, μ (A (k + i)) := measure_iUnion_le _
      _ ≤ ∑' i, (2 : ENNReal)⁻¹ ^ (k + i) :=
        ENNReal.tsum_le_tsum fun i ↦ hμA (k + i)
      _ = 2 * (2 : ENNReal)⁻¹ ^ k := by
        rw [show (fun i : ℕ ↦ (2 : ENNReal)⁻¹ ^ (k + i)) =
          fun i ↦ (2 : ENNReal)⁻¹ ^ k * (2 : ENNReal)⁻¹ ^ i by
            funext i
            rw [pow_add]]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        norm_num
        rw [mul_comm]
  have hdist (k : ℕ) (ω : Ω) (hω : ω ∉ ⋃ i, A (k + i)) :
      edist (f (ns k) ω) (g ω) ≤ 2 * (2 : ENNReal)⁻¹ ^ k := by
    have hnotA (i : ℕ) : ω ∉ A (k + i) := by
      exact fun hi ↦ hω (Set.mem_iUnion.2 ⟨i, hi⟩)
    have hdiff (i : ℕ) :
        dist (f (ns (k + i)) ω) (f (ns (k + (i + 1))) ω) ≤ (1 / 2 : ℝ) ^ (k + i) := by
      have hi := hnotA i
      change ¬(2 : ENNReal)⁻¹ ^ (k + i) ≤
        edist (f (ns (k + i + 1)) ω) (f (ns (k + i)) ω) at hi
      rw [not_le, edist_dist] at hi
      rw [← ofReal_one_div_two_pow (k + i),
        ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hi
      simpa only [Nat.add_assoc, dist_comm] using hi.le
    have hsummable : Summable (fun i : ℕ ↦ (1 / 2 : ℝ) ^ (k + i)) :=
      (summable_geometric_of_lt_one (by norm_num)
        (by norm_num : (1 / 2 : ℝ) < 1)).comp_injective (add_right_injective k)
    have hωevent : ∀ᶠ i in atTop, ω ∉ A i := by
      refine Filter.eventually_atTop.2 ⟨k, fun i hi ↦ ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact hnotA j
    have hωconv := hconv ω hωevent
    have hωg : Tendsto (fun i ↦ f (ns i) ω) atTop (nhds (g ω)) := by
      simpa only [g, dif_pos hωconv] using hωconv.choose_spec
    have hshift : Tendsto (fun i ↦ f (ns (k + i)) ω) atTop (nhds (g ω)) := by
      simpa only [Nat.add_comm] using (Filter.tendsto_add_atTop_iff_nat k).2 hωg
    have hdist_real :
        dist (f (ns k) ω) (g ω) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (k + i) := by
      simpa only [Nat.add_zero] using
        dist_le_tsum_of_dist_le_of_tendsto₀ _ hdiff hsummable hshift
    have hsum : ∑' i : ℕ, (1 / 2 : ℝ) ^ (k + i) = 2 * (1 / 2 : ℝ) ^ k := by
      rw [show (fun i : ℕ ↦ (1 / 2 : ℝ) ^ (k + i)) =
        fun i ↦ (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ i by
          funext i
          rw [pow_add]]
      rw [tsum_mul_left]
      norm_num [tsum_geometric_of_norm_lt_one]
      rw [mul_comm]
    rw [edist_dist, ← ofReal_one_div_two_pow]
    calc
      ENNReal.ofReal (dist (f (ns k) ω) (g ω)) ≤
          ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) :=
        ENNReal.ofReal_le_ofReal (hdist_real.trans_eq hsum)
      _ = 2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  refine ⟨g, tendstoInMeasure_of_ne_top ?_⟩
  intro ε hε hε_top
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hthird : 0 < min (ε / 3) (δ / 3) := by
    rw [lt_min_iff]
    exact ⟨ENNReal.div_pos hε.ne' (by norm_num), ENNReal.div_pos hδ.ne' (by norm_num)⟩
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hthird.ne'
  let r : ENNReal := (2 : ENNReal)⁻¹ ^ k
  have hr : 0 < r := by
    exact ENNReal.pow_pos (by simp) k
  change r < min (ε / 3) (δ / 3) at hk
  have hrrε : r + 2 * r < ε := by
    calc
      r + 2 * r = r + (r + r) := by rw [two_mul]
      _ < ε / 3 + (ε / 3 + ε / 3) :=
        ENNReal.add_lt_add (hk.trans_le (min_le_left _ _)) <|
          ENNReal.add_lt_add (hk.trans_le (min_le_left _ _))
            (hk.trans_le (min_le_left _ _))
      _ = ε := by rw [← add_assoc, ENNReal.add_thirds]
  have hrrδ : r + 2 * r < δ := by
    calc
      r + 2 * r = r + (r + r) := by rw [two_mul]
      _ < δ / 3 + (δ / 3 + δ / 3) :=
        ENNReal.add_lt_add (hk.trans_le (min_le_right _ _)) <|
          ENNReal.add_lt_add (hk.trans_le (min_le_right _ _))
            (hk.trans_le (min_le_right _ _))
      _ = δ := by rw [← add_assoc, ENNReal.add_thirds]
  refine ⟨N k, fun n hn ↦ ?_⟩
  have hnk : μ {ω | r ≤ edist (f n ω) (f (ns k) ω)} ≤ r := by
    simpa only [r] using hN k n (ns k) hn (hNns k)
  have hsubset : {ω | ε ≤ edist (f n ω) (g ω)} ⊆
      {ω | r ≤ edist (f n ω) (f (ns k) ω)} ∪ ⋃ i, A (k + i) := by
    intro ω hω
    by_contra hmem
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hmem
    have hsecond := hdist k ω hmem.2
    have hsecond_top : edist (f (ns k) ω) (g ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (by finiteness) hsecond
    exact (not_lt_of_ge hω) <|
      (edist_triangle (f n ω) (f (ns k) ω) (g ω)).trans_lt <|
        (ENNReal.add_lt_add_right hsecond_top hmem.1).trans_le <|
          (add_le_add le_rfl hsecond).trans hrrε.le
  calc
    μ {ω | ε ≤ edist (f n ω) (g ω)} ≤
        μ ({ω | r ≤ edist (f n ω) (f (ns k) ω)} ∪ ⋃ i, A (k + i)) :=
      measure_mono hsubset
    _ ≤ μ {ω | r ≤ edist (f n ω) (f (ns k) ω)} + μ (⋃ i, A (k + i)) :=
      measure_union_le _ _
    _ ≤ r + 2 * r := add_le_add hnk (hμtail k)
    _ ≤ δ := hrrδ.le

/-- A sequence of real-valued functions which is Cauchy in measure converges in measure. -/
theorem exists_tendstoInMeasure_of_cauchySeq
    {f : ℕ → Ω → ℝ}
    (hcau : CauchyInMeasure μ f) :
    ∃ g, TendstoInMeasure μ f atTop g := by
  apply exists_tendstoInMeasure_of_dyadic_cauchy
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

/-- An a.e.-strongly measurable real-valued sequence which is Cauchy in measure
converges in measure to an a.e.-strongly measurable function. -/
theorem exists_aestronglyMeasurable_tendstoInMeasure_of_cauchySeq
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hcau : CauchyInMeasure μ f) :
    ∃ g, AEStronglyMeasurable g μ ∧ TendstoInMeasure μ f atTop g := by
  obtain ⟨g, hg⟩ := exists_tendstoInMeasure_of_cauchySeq hcau
  exact ⟨g, hg.aestronglyMeasurable hf, hg⟩

/-- An a.e.-measurable real-valued sequence which is Cauchy in measure converges
in measure to an a.e.-measurable function. -/
theorem exists_aemeasurable_tendstoInMeasure_of_cauchySeq
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hcau : CauchyInMeasure μ f) :
    ∃ g, AEMeasurable g μ ∧ TendstoInMeasure μ f atTop g := by
  obtain ⟨g, hg⟩ := exists_tendstoInMeasure_of_cauchySeq hcau
  exact ⟨g, hg.aemeasurable hf, hg⟩

/-- The space `L⁰(μ)` of a.e.-strongly measurable real-valued functions modulo a.e. equality is
complete with respect to convergence in measure. -/
theorem exists_tendstoInMeasure_lp_zero_of_cauchyInMeasure
    (f : ℕ → Lp ℝ 0 μ)
    (hf : CauchyInMeasure μ fun n ↦ f n) :
    ∃ g : Lp ℝ 0 μ, TendstoInMeasure μ (fun n ↦ f n) atTop g := by
  obtain ⟨g, hg_meas, hg⟩ := exists_aestronglyMeasurable_tendstoInMeasure_of_cauchySeq
    (fun n ↦ Lp.aestronglyMeasurable (f n)) hf
  have hg_memLp : MemLp g 0 μ := memLp_zero_iff_aestronglyMeasurable.2 hg_meas
  refine ⟨hg_memLp.toLp g, ?_⟩
  exact hg.congr_right hg_memLp.coeFn_toLp.symm

end MeasureTheory
