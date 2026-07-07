import BanLat.Examples.Lp.Basic
import BanLat.Operators.Hom
import BanLat.Substructures.Sublattice
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Order.Sublattice

/-!
# Closed sublattices of `Lp`

For `1 ≤ p < ∞` and a finite measure `μ`, the norm-closed sublattices of
`Lp ℝ p μ` that contain the constant function `𝟙` are exactly the subspaces
`lpMeas ℝ ℝ m p μ` of functions measurable with respect to a sub-σ-algebra
`m ≤ m₀`.
-/

open MeasureTheory Filter

open scoped Topology

section ClosedSublattices

universe u

variable {Ω : Type u} {m₀ : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω} {p : ENNReal} [Fact (1 ≤ p)]

namespace exists_Lp_banachLatEquiv_aux

/-- The family of `m₀`-measurable sets `A` whose indicator function
`1_A ∈ L p μ` lies in the sublattice `L`. -/
private def indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ)) : Set (Set Ω) :=
  {A | ∃ hA : MeasurableSet A,
    indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ) ∈ L.toSubmodule}

omit [Fact (1 ≤ p)] in
/-- The empty set belongs to `indicatorFamily` since `1_∅ = 0 ∈ L`. -/
private lemma empty_mem_indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ)) :
    ∅ ∈ indicatorFamily (μ := μ) (p := p) L :=
  ⟨MeasurableSet.empty, by
    rw [indicatorConstLp_empty]; exact L.toSubmodule.zero_mem⟩

omit [Fact (1 ≤ p)] in
/-- `indicatorFamily` is closed under complements: if `1_A ∈ L`, then
`1_{Aᶜ} = 1 - 1_A ∈ L`. -/
private lemma compl_mem_indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) {A : Set Ω}
    (hA : A ∈ indicatorFamily (μ := μ) (p := p) L) :
    Aᶜ ∈ indicatorFamily (μ := μ) (p := p) L := by
  obtain ⟨hAm, hAL⟩ := hA
  refine ⟨hAm.compl, ?_⟩
  have h : indicatorConstLp p hAm.compl (measure_ne_top μ Aᶜ) (1:ℝ)
      = Lp.const p μ (1:ℝ) - indicatorConstLp p hAm (measure_ne_top μ A) 1 := by
    rw [Lp.ext_iff]
    filter_upwards [indicatorConstLp_coeFn (hs := hAm.compl)
        (hμs := measure_ne_top μ Aᶜ) (c := (1:ℝ)),
      Lp.coeFn_sub (Lp.const p μ (1:ℝ))
        (indicatorConstLp p hAm (measure_ne_top μ A) (1:ℝ)),
      Lp.coeFn_const p μ (1:ℝ),
      indicatorConstLp_coeFn (hs := hAm) (hμs := measure_ne_top μ A)
        (c := (1:ℝ))] with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4, Set.indicator_compl]
    rfl
  rw [h]
  exact L.toSubmodule.sub_mem hone hAL

omit [Fact (1 ≤ p)] in
/-- In `Lp`, the indicator of a union of two measurable sets is the supremum
of the individual indicators. -/
private lemma indicatorConstLp_union_eq_sup [IsFiniteMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    indicatorConstLp p (hA.union hB) (measure_ne_top μ _) (1 : ℝ)
      = indicatorConstLp p hA (measure_ne_top μ _) (1 : ℝ)
        ⊔ indicatorConstLp p hB (measure_ne_top μ _) (1 : ℝ) := by
  rw [Lp.ext_iff]
  filter_upwards [indicatorConstLp_coeFn (hs := hA.union hB)
      (hμs := measure_ne_top μ (A ∪ B)) (c := (1:ℝ)),
    Lp.coeFn_sup (indicatorConstLp p hA (measure_ne_top μ A) (1:ℝ))
      (indicatorConstLp p hB (measure_ne_top μ B) (1:ℝ)),
    indicatorConstLp_coeFn (hs := hA) (hμs := measure_ne_top μ A) (c := (1:ℝ)),
    indicatorConstLp_coeFn (hs := hB) (hμs := measure_ne_top μ B) (c := (1:ℝ))]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.sup_apply, h3, h4]
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxA, hxB,
      Set.mem_union, sup_of_le_left, sup_of_le_right]

/-- `indicatorFamily` is closed under countable unions. For a monotone
sequence this follows from order continuity of the `Lp` norm together with
norm-closure of `L`; the general case is reduced to the monotone case in the
usual way. -/
private lemma iUnion_mem_indicatorFamily [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    {f : ℕ → Set Ω}
    (hf : ∀ i, f i ∈ indicatorFamily (μ := μ) (p := p) L) :
    (⋃ i, f i) ∈ indicatorFamily (μ := μ) (p := p) L := by
  have hfm : ∀ i, MeasurableSet (f i) := fun i => (hf i).1
  have hfL : ∀ i, indicatorConstLp p (hfm i) (measure_ne_top μ (f i)) (1:ℝ)
                ∈ L.toSubmodule := fun i => (hf i).2
  let A : ℕ → Set Ω := Set.accumulate f
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hfm i))
  have hAmono : Monotone A := Set.monotone_accumulate
  have hAunion : ⋃ n, A n = ⋃ i, f i := Set.iUnion_accumulate
  have hAL : ∀ n, indicatorConstLp p (hAm n) (measure_ne_top μ (A n)) (1:ℝ)
                ∈ L.toSubmodule := by
    intro n
    induction n with
    | zero =>
      have hA0 : A 0 = f 0 := Set.accumulate_zero_nat f
      have : indicatorConstLp p (hAm 0) (measure_ne_top μ (A 0)) (1:ℝ)
           = indicatorConstLp p (hfm 0) (measure_ne_top μ (f 0)) (1:ℝ) := by
        congr 1
      rw [this]; exact hfL 0
    | succ n ih =>
      have hAsucc : A (n+1) = A n ∪ f (n+1) := Set.accumulate_succ f n
      have : indicatorConstLp p (hAm (n+1)) (measure_ne_top μ (A (n+1))) (1:ℝ)
           = indicatorConstLp p ((hAm n).union (hfm (n+1)))
               (measure_ne_top μ _) (1:ℝ) := by
        congr 1
      rw [this, indicatorConstLp_union_eq_sup (hAm n) (hfm (n+1))]
      exact L.sup_mem ih (hfL (n+1))
  have hUm : MeasurableSet (⋃ i, f i) :=
    MeasurableSet.iUnion hfm
  refine ⟨hUm, ?_⟩
  have htendsto : Filter.Tendsto
      (fun n => indicatorConstLp p (hAm n) (measure_ne_top μ (A n)) (1:ℝ))
      Filter.atTop (nhds (indicatorConstLp p hUm (measure_ne_top μ _) (1:ℝ))) := by
    refine tendsto_indicatorConstLp_set (ht := hAm)
      (hμt := fun n => measure_ne_top μ (A n)) hp_ne_top ?_
    have hAsub : ∀ n, A n ⊆ ⋃ i, f i := fun n =>
      Set.accumulate_subset_iUnion n
    have hsymm : ∀ n, symmDiff (A n) (⋃ i, f i) = (⋃ i, f i) \ A n := by
      intro n
      rw [symmDiff_def]
      simp [Set.diff_eq_empty.mpr (hAsub n)]
    simp_rw [hsymm]
    have hmtendsto : Filter.Tendsto (fun n => μ (A n)) Filter.atTop
        (nhds (μ (⋃ i, f i))) := by
      have := tendsto_measure_iUnion_atTop (μ := μ) hAmono
      rw [hAunion] at this
      exact this
    have hsub : ∀ n, μ ((⋃ i, f i) \ A n) = μ (⋃ i, f i) - μ (A n) := fun n =>
      measure_diff (hAsub n) (hAm n).nullMeasurableSet (measure_ne_top μ _)
    simp_rw [hsub]
    have hfin : μ (⋃ i, f i) ≠ ⊤ := measure_ne_top μ _
    have hsub_tendsto : Filter.Tendsto
        (fun n => μ (⋃ i, f i) - μ (A n)) Filter.atTop
        (nhds (μ (⋃ i, f i) - μ (⋃ i, f i))) :=
      ENNReal.tendsto_sub (Or.inr hfin) |>.comp
        (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hmtendsto)
    rw [tsub_self] at hsub_tendsto
    exact hsub_tendsto
  exact hclosed.isSeqClosed (fun n => hAL n) htendsto

/-- The sub-σ-algebra of `m₀` induced by the sublattice `L`. -/
@[reducible]
private def sigmaAlgebra [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) : MeasurableSpace Ω where
  MeasurableSet' A := A ∈ indicatorFamily (μ := μ) (p := p) L
  measurableSet_empty := empty_mem_indicatorFamily L
  measurableSet_compl _ hA := compl_mem_indicatorFamily L hone hA
  measurableSet_iUnion _ := iUnion_mem_indicatorFamily hp_ne_top L hclosed

/-- The induced σ-algebra is coarser than `m₀`. -/
private lemma sigmaAlgebra_le [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    sigmaAlgebra hp_ne_top L hclosed hone ≤ m₀ := by
  intro A hA
  exact hA.1

omit [Fact (1 ≤ p)] in
/-- For a real scalar, the indicator in `Lp` is the scalar multiple of the
indicator with value `1`. -/
private lemma indicatorConstLp_eq_smul [IsFiniteMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A) (c : ℝ) :
    indicatorConstLp p hA (measure_ne_top μ A) c
      = c • indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ) := by
  rw [Lp.ext_iff]
  filter_upwards [indicatorConstLp_coeFn (hs := hA)
      (hμs := measure_ne_top μ A) (c := c),
    Lp.coeFn_smul c (indicatorConstLp p hA (measure_ne_top μ A) (1:ℝ)),
    indicatorConstLp_coeFn (hs := hA) (hμs := measure_ne_top μ A) (c := (1:ℝ))]
    with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  by_cases hxs : x ∈ A
  · simp [Set.indicator_of_mem, hxs, smul_eq_mul]
  · simp [Set.indicator_of_notMem, hxs, smul_eq_mul]

/-- Every `m`-simple function lies in `L`: the indicator of every set in
`indicatorFamily` is in `L`, and `L` is a real subspace. -/
private lemma simpleFunc_mem_sublattice [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (f : Lp ℝ p μ)
    (hf : AEStronglyMeasurable[sigmaAlgebra hp_ne_top L hclosed hone] f μ) :
    f ∈ L.toSubmodule := by
  set hm := sigmaAlgebra_le hp_ne_top L hclosed hone
  refine Lp.induction_stronglyMeasurable hm hp_ne_top
    (fun f => f ∈ L.toSubmodule) ?_ ?_ ?_ f hf
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    obtain ⟨hsm, hsL⟩ := hs
    rw [show indicatorConstLp p (hm s ⟨hsm, hsL⟩) hμs.ne c
          = c • indicatorConstLp p hsm (measure_ne_top μ s) (1 : ℝ) from
        indicatorConstLp_eq_smul hsm c]
    exact L.toSubmodule.smul_mem c hsL
  · intros _ _ _ _ _ _ _ hPf hPg
    exact L.toSubmodule.add_mem hPf hPg
  · exact hclosed.preimage continuous_induced_dom

/-- For `f ∈ L`, every superlevel set `{f > λ}` lies in the induced
`indicatorFamily`. The approximation `((n+1) · (f - λ · 1)⁺) ⊓ 1` converges in
`Lp` to the indicator of `{f > λ}` because the difference is supported on the
shrinking sets `{λ < f < λ + 1/(n+1)}`, whose measure tends to `0`. -/
private lemma indicatorConstLp_superlevel_mem_sublattice
    [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    {f : Lp ℝ p μ} (hf : f ∈ L.toSubmodule) (lam : ℝ) :
    indicatorConstLp p
      ((Lp.stronglyMeasurable f).measurable
        (measurableSet_Ioi : MeasurableSet (Set.Ioi lam)))
      (measure_ne_top μ _) (1 : ℝ) ∈ L.toSubmodule := by
  set A : Set Ω := ⇑f ⁻¹' Set.Ioi lam with hA_def
  set hA : MeasurableSet A :=
    (Lp.stronglyMeasurable f).measurable measurableSet_Ioi
  set Igw : Lp ℝ p μ := indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ)
    with hIgw_def
  set g : Lp ℝ p μ := f - lam • Lp.const p μ (1 : ℝ) with hg_def
  have hgL : g ∈ L.toSubmodule :=
    L.toSubmodule.sub_mem hf (L.toSubmodule.smul_mem _ hone)
  have hp_one : (1 : ENNReal) ≤ p := Fact.out
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; norm_num at hp_one
  have hp_real_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  set F : ℕ → Lp ℝ p μ := fun n =>
    (((n + 1 : ℕ) : ℝ) • g⁺) ⊓ Lp.const p μ (1 : ℝ) with hF_def
  have hFL : ∀ n, F n ∈ L.toSubmodule := fun n =>
    L.inf_mem (L.toSubmodule.smul_mem _ (L.posPart_mem hgL)) hone
  set B : ℕ → Set Ω := fun n =>
    ⇑f ⁻¹' Set.Ioo lam (lam + (((n + 1 : ℕ) : ℝ))⁻¹) with hB_def
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    (Lp.stronglyMeasurable f).measurable measurableSet_Ioo
  have hBmono : Antitone B := by
    intro n m hnm ω hω
    refine ⟨hω.1, lt_of_lt_of_le hω.2 ?_⟩
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h1 : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ :=
      inv_anti₀ hpos (by exact_mod_cast Nat.succ_le_succ hnm)
    linarith
  have hBempty : ⋂ n, B n = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    by_cases h_bound : ⇑f ω - lam ≤ 0
    · exact ⟨0, fun ⟨h1, _⟩ => absurd (sub_pos.mpr h1) (not_lt.mpr h_bound)⟩
    push Not at h_bound
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h_bound
    refine ⟨n, fun ⟨_, hlt⟩ => ?_⟩
    have : ((n + 1 : ℕ) : ℝ)⁻¹ < ⇑f ω - lam := by
      have : (1 : ℝ) / ((n : ℕ) + 1) < ⇑f ω - lam := hn
      simp only [one_div] at this
      convert this using 2
      push_cast
      ring
    linarith
  have hμB_ne_top : ∀ n, μ (B n) ≠ ⊤ := fun n => measure_ne_top μ (B n)
  have hμB_tendsto : Filter.Tendsto (fun n => μ (B n)) Filter.atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (s := B) (fun n => (hBm n).nullMeasurableSet) hBmono ⟨0, hμB_ne_top 0⟩
    rw [hBempty, measure_empty] at h
    exact h
  have hμB_pow_tendsto :
      Filter.Tendsto (fun n => μ (B n) ^ (1 / p.toReal))
        Filter.atTop (𝓝 0) := by
    have hcont : Continuous (fun x : ENNReal => x ^ (1 / p.toReal)) :=
      ENNReal.continuous_rpow_const
    have hzero : (0 : ENNReal) ^ (1 / p.toReal) = 0 :=
      ENNReal.zero_rpow_of_pos (by positivity)
    have := hcont.tendsto (0 : ENNReal)
    rw [hzero] at this
    exact this.comp hμB_tendsto
  have h_diff_bound : ∀ n, ∀ᵐ ω ∂μ,
      ‖(⇑(F n) - ⇑Igw) ω‖ ≤ (B n).indicator (fun _ => (1 : ℝ)) ω := by
    intro n
    filter_upwards [Lp.coeFn_inf
        ((((n + 1 : ℕ) : ℝ)) • (g⁺ : Lp ℝ p μ)) (Lp.const p μ (1 : ℝ)),
      Lp.coeFn_smul (((n + 1 : ℕ) : ℝ)) (g⁺ : Lp ℝ p μ),
      Lp.coeFn_sup g (0 : Lp ℝ p μ),
      Lp.coeFn_zero ℝ p μ,
      Lp.coeFn_sub f (lam • Lp.const p μ (1 : ℝ)),
      Lp.coeFn_smul lam (Lp.const p μ (1 : ℝ)),
      Lp.coeFn_const p μ (1 : ℝ),
      indicatorConstLp_coeFn (hs := hA) (hμs := measure_ne_top μ A)
        (c := (1 : ℝ))]
      with ω h_inf h_smul h_sup h_zero h_sub h_smul' h_const h_ind
    have h_pos : ⇑(g⁺ : Lp ℝ p μ) ω = max (⇑g ω) 0 := by
      change ⇑(g ⊔ (0 : Lp ℝ p μ)) ω = _
      rw [h_sup, Pi.sup_apply, h_zero, Pi.zero_apply]
    have h_Fn : ⇑(F n) ω
        = min (((n + 1 : ℕ) : ℝ) * max (⇑f ω - lam) 0) 1 := by
      change ⇑((((n + 1 : ℕ) : ℝ) • (g⁺ : Lp ℝ p μ)) ⊓ Lp.const p μ (1 : ℝ))
        ω = _
      rw [h_inf, Pi.inf_apply, h_smul, Pi.smul_apply, h_pos, h_sub,
        Pi.sub_apply, h_smul', Pi.smul_apply, h_const]
      simp only [smul_eq_mul, Function.const_apply, mul_one]
    have h_Igw : ⇑Igw ω = A.indicator (fun _ => (1 : ℝ)) ω := h_ind
    rw [Pi.sub_apply, h_Fn, h_Igw]
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    by_cases hf_le : ⇑f ω ≤ lam
    · have h_max : max (⇑f ω - lam) 0 = 0 := max_eq_right (by linarith)
      have hω_notin_A : ω ∉ A := by
        intro h; have : ⇑f ω > lam := h; linarith
      rw [h_max, mul_zero, min_eq_left zero_le_one,
        Set.indicator_of_notMem hω_notin_A, sub_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    push Not at hf_le
    have hω_in_A : ω ∈ A := hf_le
    rw [Set.indicator_of_mem hω_in_A]
    have h_max : max (⇑f ω - lam) 0 = ⇑f ω - lam := max_eq_left (by linarith)
    rw [h_max]
    by_cases h_ge : ((n + 1 : ℕ) : ℝ) * (⇑f ω - lam) ≥ 1
    · rw [min_eq_right h_ge, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    push Not at h_ge
    rw [min_eq_left h_ge.le]
    have h_ω_in_B : ω ∈ B n := by
      refine ⟨hf_le, ?_⟩
      have h_div : ⇑f ω - lam < ((n + 1 : ℕ) : ℝ)⁻¹ := by
        rw [show ((n + 1 : ℕ) : ℝ)⁻¹ = 1 / ((n + 1 : ℕ) : ℝ)
          from (one_div _).symm,
          lt_div_iff₀ hpos]
        linarith [mul_comm ((n + 1 : ℕ) : ℝ) (⇑f ω - lam)]
      linarith
    rw [Set.indicator_of_mem h_ω_in_B]
    have h_diff_neg : ((n + 1 : ℕ) : ℝ) * (⇑f ω - lam) - 1
        = -(1 - ((n + 1 : ℕ) : ℝ) * (⇑f ω - lam)) := by ring
    rw [h_diff_neg, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    have h_pos_prod : 0 < ((n + 1 : ℕ) : ℝ) * (⇑f ω - lam) :=
      mul_pos hpos (by linarith)
    linarith
  have h_one : ‖(1 : ℝ)‖ₑ = 1 := by simp
  have h_eLpNorm_le : ∀ n,
      eLpNorm (⇑(F n) - ⇑Igw) p μ ≤ μ (B n) ^ (1 / p.toReal) := by
    intro n
    have h1 : eLpNorm (⇑(F n) - ⇑Igw) p μ
        ≤ eLpNorm ((B n).indicator (fun _ => (1 : ℝ))) p μ := by
      refine eLpNorm_mono_ae_real ?_
      filter_upwards [h_diff_bound n] with ω hω using hω
    have h2 := eLpNorm_indicator_const_le ((1 : ℝ)) (s := B n) (μ := μ) p
    rw [h_one, one_mul] at h2
    exact h1.trans h2
  have h_eLpNorm_tendsto :
      Filter.Tendsto (fun n => eLpNorm (⇑(F n) - ⇑Igw) p μ)
        Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hμB_pow_tendsto
      (fun _ => bot_le) h_eLpNorm_le
  have h_tendsto : Filter.Tendsto F Filter.atTop (𝓝 Igw) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    exact h_eLpNorm_tendsto
  exact hclosed.isSeqClosed (fun n => hFL n) h_tendsto

/-- For `f ∈ L`, the function `f` is `m`-strongly measurable with respect to
the induced σ-algebra. -/
private lemma aeStronglyMeasurable_of_mem_sublattice [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) {f : Lp ℝ p μ}
    (hf : f ∈ L.toSubmodule) :
    AEStronglyMeasurable[sigmaAlgebra hp_ne_top L hclosed hone] f μ := by
  refine ⟨⇑f, ?_, Filter.EventuallyEq.rfl⟩
  refine Measurable.stronglyMeasurable ?_
  refine measurable_of_Ioi (fun lam => ?_)
  exact ⟨(Lp.stronglyMeasurable f).measurable measurableSet_Ioi,
    indicatorConstLp_superlevel_mem_sublattice hp_ne_top L hclosed hone hf lam⟩

/-- The sublattice `L` coincides, as a submodule of `Lp ℝ p μ`, with
`lpMeas ℝ ℝ m p μ` for the induced sub-σ-algebra `m`. -/
private lemma toSubmodule_eq_lpMeas [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    L.toSubmodule =
      lpMeas ℝ ℝ (sigmaAlgebra hp_ne_top L hclosed hone) p μ := by
  ext f
  constructor
  · intro hf
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact aeStronglyMeasurable_of_mem_sublattice hp_ne_top L hclosed hone hf
  · intro hf
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hf
    exact simpleFunc_mem_sublattice hp_ne_top L hclosed hone f hf

/-- The restricted finite measure on the induced σ-algebra. -/
private noncomputable def trimmedMeasure [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    @MeasureTheory.Measure Ω (sigmaAlgebra hp_ne_top L hclosed hone) :=
  μ.trim (sigmaAlgebra_le hp_ne_top L hclosed hone)

private instance [IsFiniteMeasure μ] {hp_ne_top : p ≠ ⊤}
    {L : VectorSublattice (Lp ℝ p μ)}
    {hclosed : IsClosed (L : Set (Lp ℝ p μ))}
    {hone : Lp.const p μ (1 : ℝ) ∈ L} :
    IsFiniteMeasure (trimmedMeasure hp_ne_top L hclosed hone) := by
  unfold trimmedMeasure
  infer_instance

/-- A linear isometric equivalence between two subtypes induced by submodule
equality. -/
private noncomputable def submoduleEquivLie
    {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {M N : Submodule ℝ X} (h : M = N) : ↥M ≃ₗᵢ[ℝ] ↥N where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The linear isometric equivalence between `↥L.toSubmodule` and
`Lp ℝ p (μ.trim h)`, obtained from `lpMeasToLpTrimLie` by identifying the
sublattice with `lpMeas`. -/
private noncomputable def linearIsometryEquiv [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    ↥L.toSubmodule ≃ₗᵢ[ℝ]
      Lp ℝ p (trimmedMeasure hp_ne_top L hclosed hone) :=
  (submoduleEquivLie (toSubmodule_eq_lpMeas hp_ne_top L hclosed hone)).trans
    (lpMeasToLpTrimLie ℝ ℝ p μ (sigmaAlgebra_le hp_ne_top L hclosed hone))

/-- The underlying function of `linearIsometryEquiv z` is `μ`-a.e. equal to the
underlying function of `z.1`. -/
private lemma linearIsometryEquiv_coeFn_ae_eq [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (z : ↥L.toSubmodule) :
    (linearIsometryEquiv hp_ne_top L hclosed hone z : Ω → ℝ) =ᵐ[μ]
      (z.1 : Ω → ℝ) :=
  lpMeasToLpTrim_ae_eq (sigmaAlgebra_le hp_ne_top L hclosed hone) _

/-- `linearIsometryEquiv` preserves the pointwise supremum. -/
private lemma linearIsometryEquiv_map_sup [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (x y : ↥L.toSubmodule) :
    linearIsometryEquiv hp_ne_top L hclosed hone (x ⊔ y) =
      linearIsometryEquiv hp_ne_top L hclosed hone x ⊔
        linearIsometryEquiv hp_ne_top L hclosed hone y := by
  set hm := sigmaAlgebra_le hp_ne_top L hclosed hone
  refine Lp.ext ?_
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm
    (Lp.stronglyMeasurable _) ?_
  have h_ae_sup : ⇑(linearIsometryEquiv hp_ne_top L hclosed hone x ⊔
        linearIsometryEquiv hp_ne_top L hclosed hone y) =ᵐ[μ]
      ⇑(linearIsometryEquiv hp_ne_top L hclosed hone x) ⊔
        ⇑(linearIsometryEquiv hp_ne_top L hclosed hone y) :=
    ae_eq_of_ae_eq_trim (Lp.coeFn_sup _ _)
  filter_upwards [linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone (x ⊔ y),
    linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone x,
    linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone y,
    h_ae_sup, Lp.coeFn_sup x.1 y.1] with ω h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sup_apply, h2, h3]
  exact h5

/-- `linearIsometryEquiv` preserves the pointwise infimum. -/
private lemma linearIsometryEquiv_map_inf [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (x y : ↥L.toSubmodule) :
    linearIsometryEquiv hp_ne_top L hclosed hone (x ⊓ y) =
      linearIsometryEquiv hp_ne_top L hclosed hone x ⊓
        linearIsometryEquiv hp_ne_top L hclosed hone y := by
  set hm := sigmaAlgebra_le hp_ne_top L hclosed hone
  refine Lp.ext ?_
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm
    (Lp.stronglyMeasurable _) ?_
  have h_ae_inf : ⇑(linearIsometryEquiv hp_ne_top L hclosed hone x ⊓
        linearIsometryEquiv hp_ne_top L hclosed hone y) =ᵐ[μ]
      ⇑(linearIsometryEquiv hp_ne_top L hclosed hone x) ⊓
        ⇑(linearIsometryEquiv hp_ne_top L hclosed hone y) :=
    ae_eq_of_ae_eq_trim (Lp.coeFn_inf _ _)
  filter_upwards [linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone (x ⊓ y),
    linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone x,
    linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone y,
    h_ae_inf, Lp.coeFn_inf x.1 y.1] with ω h1 h2 h3 h4 h5
  rw [h1, h4, Pi.inf_apply, h2, h3]
  exact h5

/-- Assemble the Banach lattice equivalence from the linear isometric
equivalence and the two lattice-preservation lemmas. -/
private noncomputable def banachLatEquiv [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
    BanachLatEquiv ↥L.toSubmodule
      (Lp ℝ p (trimmedMeasure hp_ne_top L hclosed hone)) :=
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
  { toLinearIsometryEquiv := linearIsometryEquiv hp_ne_top L hclosed hone
    map_sup' := linearIsometryEquiv_map_sup hp_ne_top L hclosed hone
    map_inf' := linearIsometryEquiv_map_inf hp_ne_top L hclosed hone }

end exists_Lp_banachLatEquiv_aux

/-- A norm-closed vector sublattice of `Lp ℝ p μ` (with `1 ≤ p < ∞` and `μ` a
finite measure) that contains the constant function `1` is Banach-lattice
isomorphic to `Lp ℝ p ν` for a finite measure `ν` on some measurable space. -/
theorem exists_Lp_banachLatEquiv_of_closed_sublattice_containing_one
    [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : MeasureTheory.Measure Ω')
      (_ : IsFiniteMeasure ν) (φ : BanachLatEquiv ↥L.toSubmodule (Lp ℝ p ν)),
      ∀ᵐ a ∂ν, (φ ⟨Lp.const p μ (1 : ℝ), hone⟩ : Ω' → ℝ) a = 1 := by
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
  refine ⟨Ω,
    exists_Lp_banachLatEquiv_aux.sigmaAlgebra hp_ne_top L hclosed hone,
    exists_Lp_banachLatEquiv_aux.trimmedMeasure hp_ne_top L hclosed hone,
    inferInstance,
    exists_Lp_banachLatEquiv_aux.banachLatEquiv hp_ne_top L hclosed hone, ?_⟩
  have hae : (exists_Lp_banachLatEquiv_aux.banachLatEquiv hp_ne_top L hclosed hone
      ⟨Lp.const p μ (1 : ℝ), hone⟩ : Ω → ℝ) =ᵐ[μ] fun _ => 1 :=
    (exists_Lp_banachLatEquiv_aux.linearIsometryEquiv_coeFn_ae_eq hp_ne_top L hclosed hone
      ⟨Lp.const p μ (1 : ℝ), hone⟩).trans (Lp.coeFn_const p μ (1 : ℝ))
  exact (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (exists_Lp_banachLatEquiv_aux.sigmaAlgebra_le hp_ne_top L hclosed hone)
    stronglyMeasurable_const hae

private lemma lp_indicatorConstLp_one_eq_zero_iff
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {E : Set α} (hEm : MeasurableSet E) :
    indicatorConstLp 1 hEm (measure_ne_top ν E) (1 : ℝ) = 0 ↔ ν E = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (indicatorConstLp 1 hEm (measure_ne_top ν E) (1 : ℝ) : α → ℝ)
        =ᵐ[ν] 0 := by rw [h]; exact Lp.coeFn_zero ℝ 1 ν
    have h2 : E.indicator (fun _ => (1 : ℝ)) =ᵐ[ν] 0 :=
      (indicatorConstLp_coeFn (p := 1) (hs := hEm)
        (hμs := measure_ne_top ν E) (c := (1 : ℝ))).symm.trans h1
    have h3 : ν (E ∩ Function.support (fun _ : α => (1 : ℝ))) = 0 :=
      (Set.indicator_ae_eq_zero (μ := ν)).mp h2
    have hsupp : Function.support (fun _ : α => (1 : ℝ)) = Set.univ := by
      ext; simp [Function.support]
    rw [hsupp, Set.inter_univ] at h3
    exact h3
  · apply Lp.ext
    refine (indicatorConstLp_coeFn (p := 1) (hs := hEm)
      (hμs := measure_ne_top ν E) (c := (1 : ℝ))).trans ?_
    exact (indicator_meas_zero h).trans (Lp.coeFn_zero ℝ 1 ν).symm

/-- A non-negative `L¹` function with no nonzero disjoint `L¹` function is
almost everywhere strictly positive. -/
theorem lp_aePos_of_forall_isVLDisjoint_eq_zero
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {g : Lp ℝ 1 ν} (hg : 0 ≤ g)
    (hwou : ∀ v : Lp ℝ 1 ν, IsVLDisjoint v g → v = 0) :
    ∀ᵐ a ∂ν, 0 < (g : α → ℝ) a := by
  have hg_ae : 0 ≤ᵐ[ν] (g : α → ℝ) := (Lp.coeFn_nonneg g).mpr hg
  have hg_meas : Measurable (g : α → ℝ) := (Lp.stronglyMeasurable g).measurable
  set E : Set α := {a | (g : α → ℝ) a ≤ 0}
  have hEm : MeasurableSet E := hg_meas measurableSet_Iic
  set χE : Lp ℝ 1 ν := indicatorConstLp 1 hEm (measure_ne_top ν E) (1 : ℝ)
    with hχE_def
  have hχE_coe : (χE : α → ℝ) =ᵐ[ν] E.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn (p := 1) (hs := hEm)
      (hμs := measure_ne_top ν E) (c := (1 : ℝ))
  have hχE_nn : (0 : Lp ℝ 1 ν) ≤ χE := by
    rw [← Lp.coeFn_le]
    filter_upwards [Lp.coeFn_zero ℝ 1 ν, hχE_coe] with a h0 hχ
    rw [h0, hχ]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) a
  have h_inf_zero : χE ⊓ g = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_inf χE g, Lp.coeFn_zero ℝ 1 ν, hχE_coe, hg_ae]
      with a h1 h0 hχ hgnn
    rw [h1, h0]
    change min ((χE : α → ℝ) a) ((g : α → ℝ) a) = (0 : ℝ)
    rw [hχ]
    by_cases haE : a ∈ E
    · have hga_le : (g : α → ℝ) a ≤ 0 := haE
      have hga_eq : (g : α → ℝ) a = 0 := le_antisymm hga_le hgnn
      rw [hga_eq, min_comm, min_eq_left]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) a
    · rw [Set.indicator_of_notMem haE]
      exact min_eq_left hgnn
  have hχE_disj : IsVLDisjoint χE g := by
    unfold IsVLDisjoint
    rw [abs_of_nonneg hχE_nn, abs_of_nonneg hg, h_inf_zero]
  have hχE_zero : χE = 0 := hwou χE hχE_disj
  have hEν : ν E = 0 := (lp_indicatorConstLp_one_eq_zero_iff hEm).mp hχE_zero
  have hae_notE : ∀ᵐ a ∂ν, a ∉ E := ae_iff.mpr (by simpa using hEν)
  filter_upwards [hae_notE, hg_ae] with a hnotE hnn
  rcases eq_or_lt_of_le hnn with heq | hlt
  · exact absurd (le_of_eq heq.symm) hnotE
  · exact hlt

private lemma withDensitySMulLI_surjective_of_ae_pos
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f_nn : α → NNReal} (hf_nn_meas : Measurable f_nn)
    (hf_pos : ∀ᵐ ω ∂μ, (0 : ℝ) < f_nn ω) :
    Function.Surjective (withDensitySMulLI (E := ℝ) μ hf_nn_meas) := by
  intro g
  let h : α → ℝ := fun ω => (g ω) / (f_nn ω : ℝ)
  have hh_meas : Measurable h :=
    (Lp.stronglyMeasurable g).measurable.div
      (measurable_coe_nnreal_real.comp hf_nn_meas)
  have hmul_ae_μ : (fun ω => f_nn ω • h ω) =ᵐ[μ] ⇑g := by
    filter_upwards [hf_pos] with ω hω
    change (f_nn ω : ℝ) * (g ω / (f_nn ω : ℝ)) = g ω
    field_simp
  have hmul_int : Integrable (fun ω => f_nn ω • h ω) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp g)).congr hmul_ae_μ.symm
  have hh_int_ν :
      Integrable h (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal))) := by
    rw [integrable_withDensity_iff_integrable_smul hf_nn_meas]
    exact hmul_int
  have hh_memLp :
      MemLp h 1 (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal))) :=
    memLp_one_iff_integrable.mpr hh_int_ν
  refine ⟨hh_memLp.toLp h, ?_⟩
  rw [withDensitySMulLI_apply]
  apply Lp.ext
  have hh_toLp_ν :
      ⇑(hh_memLp.toLp h) =ᵐ[μ.withDensity
        (fun ω => ((f_nn ω : NNReal) : ENNReal))] h :=
    hh_memLp.coeFn_toLp
  have hh_toLp_μ : ∀ᵐ ω ∂μ,
      (f_nn ω : ENNReal) ≠ 0 → (hh_memLp.toLp h : α → ℝ) ω = h ω :=
    (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp hh_toLp_ν
  have hae : (fun x => f_nn x • (hh_memLp.toLp h : α → ℝ) x) =ᵐ[μ] ⇑g := by
    filter_upwards [hmul_ae_μ, hf_pos, hh_toLp_μ] with ω hmul hω hω_eq
    have hne : (f_nn ω : ENNReal) ≠ 0 := by exact_mod_cast hω.ne'
    rw [hω_eq hne]
    exact hmul
  calc ⇑(MemLp.toLp (fun x => f_nn x • (hh_memLp.toLp h : α → ℝ) x) _)
      =ᵐ[μ] fun x => f_nn x • (hh_memLp.toLp h : α → ℝ) x := MemLp.coeFn_toLp _
    _ =ᵐ[μ] ⇑g := hae

private lemma withDensitySMulLI_map_sup
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f_nn : α → NNReal} (hf_nn_meas : Measurable f_nn)
    (v w : Lp ℝ 1 (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal)))) :
    withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊔ w) =
      withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊔
        withDensitySMulLI (E := ℝ) μ hf_nn_meas w := by
  apply Lp.ext
  have hLHS : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊔ w)) =ᵐ[μ]
      fun x => f_nn x • ((v ⊔ w : Lp ℝ 1 _) : α → ℝ) x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hRv : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v) =ᵐ[μ]
      fun x => f_nn x • (v : α → ℝ) x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hRw : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      fun x => f_nn x • (w : α → ℝ) x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hsup_coeFn :
      ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊔
          withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      (fun x => f_nn x • (v : α → ℝ) x) ⊔ (fun x => f_nn x • (w : α → ℝ) x) := by
    filter_upwards [Lp.coeFn_sup (withDensitySMulLI (E := ℝ) μ hf_nn_meas v)
      (withDensitySMulLI (E := ℝ) μ hf_nn_meas w), hRv, hRw] with ω h h1 h2
    rw [h]
    exact congr_arg₂ _ h1 h2
  have hvw_μ : ∀ᵐ ω ∂μ, (f_nn ω : ENNReal) ≠ 0 →
      ((v ⊔ w : Lp ℝ 1 _) : α → ℝ) ω = max ((v : α → ℝ) ω) ((w : α → ℝ) ω) :=
    (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp (Lp.coeFn_sup v w)
  filter_upwards [hLHS, hsup_coeFn, hvw_μ] with ω hL hR hvw
  rw [hL, hR]
  by_cases hne : (f_nn ω : ENNReal) = 0
  · have hzero : f_nn ω = 0 := by exact_mod_cast hne
    simp [hzero]
  · rw [hvw hne]
    simp only [Pi.sup_apply]
    rw [NNReal.smul_def, NNReal.smul_def, NNReal.smul_def,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    exact mul_max_of_nonneg _ _ (NNReal.coe_nonneg _)

private lemma withDensitySMulLI_map_inf
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f_nn : α → NNReal} (hf_nn_meas : Measurable f_nn)
    (v w : Lp ℝ 1 (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal)))) :
    withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊓ w) =
      withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊓
        withDensitySMulLI (E := ℝ) μ hf_nn_meas w := by
  apply Lp.ext
  have hLHS : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊓ w)) =ᵐ[μ]
      fun x => f_nn x • ((v ⊓ w : Lp ℝ 1 _) : α → ℝ) x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hRv : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v) =ᵐ[μ]
      fun x => f_nn x • (v : α → ℝ) x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hRw : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      fun x => f_nn x • (w : α → ℝ) x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hinf_coeFn :
      ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊓
          withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      (fun x => f_nn x • (v : α → ℝ) x) ⊓ (fun x => f_nn x • (w : α → ℝ) x) := by
    filter_upwards [Lp.coeFn_inf (withDensitySMulLI (E := ℝ) μ hf_nn_meas v)
      (withDensitySMulLI (E := ℝ) μ hf_nn_meas w), hRv, hRw] with ω h h1 h2
    rw [h]
    exact congr_arg₂ _ h1 h2
  have hvw_μ : ∀ᵐ ω ∂μ, (f_nn ω : ENNReal) ≠ 0 →
      ((v ⊓ w : Lp ℝ 1 _) : α → ℝ) ω = min ((v : α → ℝ) ω) ((w : α → ℝ) ω) :=
    (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp (Lp.coeFn_inf v w)
  filter_upwards [hLHS, hinf_coeFn, hvw_μ] with ω hL hR hvw
  rw [hL, hR]
  by_cases hne : (f_nn ω : ENNReal) = 0
  · have hzero : f_nn ω = 0 := by exact_mod_cast hne
    simp [hzero]
  · rw [hvw hne]
    simp only [Pi.inf_apply]
    rw [NNReal.smul_def, NNReal.smul_def, NNReal.smul_def,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    exact mul_min_of_nonneg _ _ (NNReal.coe_nonneg _)

/-- A Banach lattice that embeds as a closed sublattice of an `L¹` space and
contains an almost everywhere strictly positive element is Banach-lattice
isomorphic to an `L¹` space. -/
theorem exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive.{v}
    {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X]
    {α : Type v} [MeasurableSpace α] (μ : Measure α)
    (T : X →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (hsup : ∀ x y : X, T (x ⊔ y) = T x ⊔ T y)
    (hinf : ∀ x y : X, T (x ⊓ y) = T x ⊓ T y)
    (_hclosed : IsClosed (Set.range T))
    (u : X) (_hu_nn : 0 ≤ u)
    (hu_ae : ∀ᵐ a ∂μ, 0 < (T u : α → ℝ) a) :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (ν : Measure Ω) (_ : IsFiniteMeasure ν)
      (φ : BanachLatEquiv X (Lp ℝ 1 ν)), ∀ᵐ a ∂ν, (φ u : Ω → ℝ) a = 1 := by
  set ρ : α → ℝ := ⇑(T u) with hρ_def
  have hρ_meas : Measurable ρ := (Lp.stronglyMeasurable (T u)).measurable
  have hρ_memLp : MemLp ρ 1 μ := Lp.memLp (T u)
  set f_nn : α → NNReal := fun ω => Real.toNNReal (ρ ω) with hf_nn_def
  have hf_nn_meas : Measurable f_nn := hρ_meas.real_toNNReal
  have hf_pos : ∀ᵐ ω ∂μ, (0 : ℝ) < f_nn ω := by
    filter_upwards [hu_ae] with ω hω
    change (0 : ℝ) < (Real.toNNReal (ρ ω) : ℝ)
    rw [Real.coe_toNNReal _ hω.le]
    exact hω
  have hf_nn_eq_ρ : ∀ᵐ ω ∂μ, (f_nn ω : ℝ) = ρ ω := by
    filter_upwards [hu_ae] with ω hω
    exact Real.coe_toNNReal _ hω.le
  set ν := μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal)) with hν_def
  have hν_finite : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [memLp_one_iff_integrable] at hρ_memLp
    calc ∫⁻ ω, ((f_nn ω : NNReal) : ENNReal) ∂μ
        ≤ ∫⁻ ω, ‖ρ ω‖ₑ ∂μ := by
          apply lintegral_mono
          intro ω
          change ((f_nn ω : NNReal) : ENNReal) ≤ ‖ρ ω‖ₑ
          rw [Real.enorm_eq_ofReal_abs,
            show ENNReal.ofReal |ρ ω| = (Real.toNNReal |ρ ω| : ENNReal) from rfl]
          exact_mod_cast Real.toNNReal_le_toNNReal (le_abs_self _)
      _ < ⊤ := hρ_memLp.2
  letI : IsFiniteMeasure ν := hν_finite
  let Φ : Lp ℝ 1 ν →ₗᵢ[ℝ] Lp ℝ 1 μ := withDensitySMulLI μ hf_nn_meas
  have hΦ_surj : Function.Surjective Φ :=
    withDensitySMulLI_surjective_of_ae_pos μ hf_nn_meas hf_pos
  let Φ' : Lp ℝ 1 ν ≃ₗᵢ[ℝ] Lp ℝ 1 μ := LinearIsometryEquiv.ofSurjective Φ hΦ_surj
  let Ψ : Lp ℝ 1 μ ≃ₗᵢ[ℝ] Lp ℝ 1 ν := Φ'.symm
  let T' : X →ₗᵢ[ℝ] Lp ℝ 1 ν := Ψ.toLinearIsometry.comp T
  have hΨ_sup : ∀ a b : Lp ℝ 1 μ, Ψ (a ⊔ b) = Ψ a ⊔ Ψ b := by
    intro a b
    apply Φ'.injective
    rw [Φ'.apply_symm_apply]
    have h : Φ' (Ψ a ⊔ Ψ b) = Φ' (Ψ a) ⊔ Φ' (Ψ b) :=
      withDensitySMulLI_map_sup μ hf_nn_meas _ _
    rw [h]
    change a ⊔ b = Φ' (Φ'.symm a) ⊔ Φ' (Φ'.symm b)
    rw [Φ'.apply_symm_apply, Φ'.apply_symm_apply]
  have hΨ_inf : ∀ a b : Lp ℝ 1 μ, Ψ (a ⊓ b) = Ψ a ⊓ Ψ b := by
    intro a b
    apply Φ'.injective
    rw [Φ'.apply_symm_apply]
    have h : Φ' (Ψ a ⊓ Ψ b) = Φ' (Ψ a) ⊓ Φ' (Ψ b) :=
      withDensitySMulLI_map_inf μ hf_nn_meas _ _
    rw [h]
    change a ⊓ b = Φ' (Φ'.symm a) ⊓ Φ' (Φ'.symm b)
    rw [Φ'.apply_symm_apply, Φ'.apply_symm_apply]
  have hT'_sup : ∀ x y : X, T' (x ⊔ y) = T' x ⊔ T' y := by
    intro x y
    change Ψ (T (x ⊔ y)) = Ψ (T x) ⊔ Ψ (T y)
    rw [hsup]
    exact hΨ_sup _ _
  have hT'_inf : ∀ x y : X, T' (x ⊓ y) = T' x ⊓ T' y := by
    intro x y
    change Ψ (T (x ⊓ y)) = Ψ (T x) ⊓ Ψ (T y)
    rw [hinf]
    exact hΨ_inf _ _
  have hT'u : T' u = Lp.const 1 ν (1 : ℝ) := by
    change Ψ (T u) = Lp.const 1 ν (1 : ℝ)
    apply Φ'.injective
    rw [Φ'.apply_symm_apply]
    change T u = withDensitySMulLI μ hf_nn_meas (Lp.const 1 ν (1 : ℝ))
    symm
    apply Lp.ext
    have hΦ_ae : ⇑(withDensitySMulLI μ hf_nn_meas (Lp.const 1 ν (1 : ℝ))) =ᵐ[μ]
        fun x => f_nn x • (Lp.const 1 ν (1 : ℝ) : α → ℝ) x := by
      rw [withDensitySMulLI_apply]
      exact MemLp.coeFn_toLp _
    have hc_μ : ∀ᵐ ω ∂μ, (f_nn ω : ENNReal) ≠ 0 →
        (Lp.const 1 ν (1 : ℝ) : α → ℝ) ω = 1 :=
      (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp (Lp.coeFn_const 1 ν 1)
    filter_upwards [hΦ_ae, hc_μ, hf_nn_eq_ρ, hf_pos] with ω hΦ hc heq hω
    rw [hΦ]
    have hne : (f_nn ω : ENNReal) ≠ 0 := by exact_mod_cast hω.ne'
    rw [hc hne]
    change (f_nn ω : ℝ) * 1 = ρ ω
    rw [mul_one]
    exact heq
  let L : VectorSublattice (Lp ℝ 1 ν) :=
    { toSubmodule := LinearMap.range T'.toLinearMap
      sup_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        change T' x ⊔ T' y ∈ _
        rw [← hT'_sup]
        exact LinearMap.mem_range_self _ _ }
  have hL_closed : IsClosed (L : Set (Lp ℝ 1 ν)) := by
    change IsClosed (Set.range T')
    exact T'.isometry.isClosedEmbedding.isClosed_range
  have hL_one : Lp.const 1 ν (1 : ℝ) ∈ L := by
    rw [← hT'u]
    exact LinearMap.mem_range_self _ _
  letI : Lattice ↥L.toSubmodule := L.instLatticeSubtype
  letI : IsOrderedAddMonoid ↥L.toSubmodule := L.instIsOrderedAddMonoidSubtype
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hL_closed
  obtain ⟨Ω', mΩ', ν', hν'_finite, φ, hφ_one⟩ :=
    exists_Lp_banachLatEquiv_of_closed_sublattice_containing_one (μ := ν)
      (by norm_num : (1 : ENNReal) ≠ ⊤) L hL_closed hL_one
  have hψ_sup : ∀ x y : X,
      T'.equivRange (x ⊔ y) = T'.equivRange x ⊔ T'.equivRange y := fun x y =>
    Subtype.ext (hT'_sup x y)
  have hψ_inf : ∀ x y : X,
      T'.equivRange (x ⊓ y) = T'.equivRange x ⊓ T'.equivRange y := fun x y =>
    Subtype.ext (hT'_inf x y)
  refine ⟨Ω', mΩ', ν', hν'_finite,
    { toLinearIsometryEquiv := T'.equivRange.trans φ.toLinearIsometryEquiv
      map_sup' := ?_
      map_inf' := ?_ }, ?_⟩
  · intro x y
    change φ (T'.equivRange (x ⊔ y)) = φ (T'.equivRange x) ⊔ φ (T'.equivRange y)
    rw [hψ_sup]
    exact φ.map_sup' _ _
  · intro x y
    change φ (T'.equivRange (x ⊓ y)) = φ (T'.equivRange x) ⊓ φ (T'.equivRange y)
    rw [hψ_inf]
    exact φ.map_inf' _ _
  · have hrange_u : T'.equivRange u = ⟨Lp.const 1 ν (1 : ℝ), hL_one⟩ := Subtype.ext hT'u
    change ∀ᵐ a ∂ν', (φ (T'.equivRange u) : Ω' → ℝ) a = 1
    rw [hrange_u]
    exact hφ_one

end ClosedSublattices
