import BanLat.Examples.Lp.Basic
import BanLat.Operators.Hom
import BanLat.Substructures.Sublattice
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
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

/-
Outline of the proof. Let `m := {A ∈ m₀ : 1_A ∈ L}`. This family is a
sub-σ-algebra of `m₀`: closure under complements uses `1_{Aᶜ} = 1 - 1_A`
and closure under countable unions uses order continuity of the `Lp` norm
together with norm-closure of `L`. One then shows that `L`, viewed as a
submodule of `Lp ℝ p μ`, coincides with `lpMeas ℝ ℝ m p μ`: the forward
inclusion follows because `m`-simple functions are dense in `lpMeas` and
their indicators belong to `L`; the reverse inclusion follows because, for
`f ∈ L`, every superlevel set `{f > λ}` lies in `m` (via
`(n · (f - λ1)⁺ ∧ 1) ↑ 1_{f > λ}` in norm). The Banach-lattice equivalence
with `Lp ℝ p (μ.trim h)` is then obtained from `lpMeasToLpTrimLie` together
with preservation of the pointwise lattice operations.
-/

namespace exists_Lp_banachLatEquiv_aux

/-- The family of `m₀`-measurable sets `A` whose indicator function
`1_A ∈ L p μ` lies in the sublattice `L`. This family will be shown to be a
sub-σ-algebra of `m₀`. -/
private def indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ)) : Set (Set Ω) :=
  {A | ∃ hA : MeasurableSet A,
    indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ) ∈ L.toSubmodule}

omit [Fact (1 ≤ p)] in
/-- The empty set belongs to `indicatorFamily` since `1_∅ = 0 ∈ L`. -/
private lemma empty_mem_indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ)) :
    ∅ ∈ indicatorFamily (μ := μ) (p := p) L := by
  exact ⟨MeasurableSet.empty, by
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
    push_neg at h_bound
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
    push_neg at hf_le
    have hω_in_A : ω ∈ A := hf_le
    rw [Set.indicator_of_mem hω_in_A]
    have h_max : max (⇑f ω - lam) 0 = ⇑f ω - lam := max_eq_left (by linarith)
    rw [h_max]
    by_cases h_ge : ((n + 1 : ℕ) : ℝ) * (⇑f ω - lam) ≥ 1
    · rw [min_eq_right h_ge, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    push_neg at h_ge
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

/-- The above linear isometry preserves the pointwise supremum. -/
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

/-- The above linear isometry preserves the pointwise infimum. -/
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
      (_ : IsFiniteMeasure ν),
      Nonempty (BanachLatEquiv ↥L.toSubmodule (Lp ℝ p ν)) := by
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
  refine ⟨Ω,
    exists_Lp_banachLatEquiv_aux.sigmaAlgebra hp_ne_top L hclosed hone,
    exists_Lp_banachLatEquiv_aux.trimmedMeasure hp_ne_top L hclosed hone,
    inferInstance,
    ⟨exists_Lp_banachLatEquiv_aux.banachLatEquiv hp_ne_top L hclosed hone⟩⟩

end ClosedSublattices
