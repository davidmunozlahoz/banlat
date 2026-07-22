import BanLat.Atom
import BanLat.Examples.Lp.Basic
import BanLat.Preliminaries.HasNoAtoms
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Vector lattice atoms in `Lₚ` spaces with `0 < p < ∞'

We characterize the **lattice atoms of `L^p(μ)`, `0 < p < ∞`:** a positive
`a ∈ L^p(μ)` is an atom if and only if `a = c 1_A` a.e., for some finite
measure-theoretic atom `A` and some `c > 0`.

In BanLat, `A` is a *measure-theoretic atom (for `μ`)* if:        (!!!)
  • `A` is `μ`-measurable.
  • `0 < μ(A)`.
  • For every measurable `B ⊆ A`, either `μ(B) = 0` or `μ(B) = μ(A)`.
-/

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0}

/-- If `s` is a measure-theoretic atom for `μ` and `f` is a.e. measurable
on `s`, then `f` is a.e. constant over `s`. -/
private lemma Measure.IsAtom.exists_ae_eq_const
    {s : Set α} (hs : μ.IsAtom s) (hμs : μ s < ∞)
    {f : α → ℝ} (hf : AEMeasurable f (μ.restrict s)) :
    ∃ c : ℝ, f =ᵐ[μ.restrict s] fun _ ↦ c := by
  let g := hf.mk f
  let ν : Measure ℝ := (μ s)⁻¹ • (μ.restrict s).map g
  have hg : Measurable g := hf.measurable_mk
  have hν_zero_one : ∀ t : Set ℝ, MeasurableSet t → ν t = 0 ∨ ν t = 1 := by
    intro t ht
    have hut : MeasurableSet (g ⁻¹' t ∩ s) := (hg ht).inter hs.1
    rcases hs.2.2 hut Set.inter_subset_right with hut0 | huts
    · left
      simp [ν, Measure.map_apply hg ht, Measure.restrict_apply (hg ht), hut0]
    · right
      simp only [ν, Measure.smul_apply, Measure.map_apply hg ht,
        Measure.restrict_apply (hg ht), huts, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hs.2.1.ne' hμs.ne
  letI : IsZeroOneMeasure ν := ⟨fun {t} ht ↦ hν_zero_one t ht⟩
  have hν_univ : ν Set.univ = 1 := by
    rw [show ν = (μ s)⁻¹ • (μ.restrict s).map g from rfl,
      Measure.smul_apply, Measure.map_apply hg MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hs.2.1.ne' hμs.ne
  letI : NeZero ν := ⟨fun hν ↦ by
    rw [hν] at hν_univ
    exact zero_ne_one hν_univ⟩
  obtain ⟨c, hν⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := ν)
  have hpre : μ.restrict s (g ⁻¹' ({c} : Set ℝ)ᶜ) = 0 := by
    have hcomp : ν ({c} : Set ℝ)ᶜ = 0 := by simp [hν]
    change (μ s)⁻¹ * (μ.restrict s).map g ({c} : Set ℝ)ᶜ = 0 at hcomp
    rw [Measure.map_apply hg (measurableSet_singleton c).compl] at hcomp
    exact (mul_eq_zero.mp hcomp).resolve_left (ENNReal.inv_ne_zero.2 hμs.ne)
  refine ⟨c, hf.ae_eq_mk.trans ?_⟩
  apply ae_iff.2
  rw [show {x | g x ≠ c} = g ⁻¹' ({c} : Set ℝ)ᶜ by ext; simp]
  exact hpre

/-- The indicator function of a measurable set is a.e. strictly positive iff
that set has strictly positive measure. -/
private lemma indicatorConstLp_pos_iff
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞)
    {c : ℝ} (hc : 0 < c) :
    0 < indicatorConstLp (p : ENNReal) hs hμs.ne c ↔ 0 < μ s := by
  let a := indicatorConstLp (p : ENNReal) hs hμs.ne c
  have hcoe : (a : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  have ha_nonneg : 0 ≤ a := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [hcoe] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      exact hc.le
    · rw [Set.indicator_of_notMem hxs]
      simp
  constructor
  · intro ha
    by_contra hμ
    have hμ0 : μ s = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hμ)
    have hzero : a = 0 := by
      apply Lp.ext
      filter_upwards [hcoe, Lp.coeFn_zero ℝ (p : ENNReal) μ,
        measure_eq_zero_iff_ae_notMem.mp hμ0] with x hxa hxzero hxs
      rw [hxa, Set.indicator_of_notMem hxs]
      simpa using hxzero.symm
    exact ha.ne' hzero
  · intro hμ
    refine lt_iff_le_and_ne.2 ⟨ha_nonneg, ?_⟩
    intro ha0
    have haeq : a = 0 := by simpa only [a] using ha0.symm
    have hzero : (a : α → ℝ) =ᵐ[μ] 0 :=
      (Lp.ext_iff.mp haeq).trans (Lp.coeFn_zero ℝ (p : ENNReal) μ)
    have hs_ae : ∀ᵐ x ∂μ, x ∉ s := by
      filter_upwards [hcoe, hzero] with x hxa hxzero
      intro hxs
      have : c = 0 := by
        rw [hxa, Set.indicator_of_mem hxs] at hxzero
        exact hxzero
      exact hc.ne' this
    exact hμ.ne' (measure_eq_zero_iff_ae_notMem.2 hs_ae)

/-- `r · (c · 1_A) = (r · c) · 1_A` -/
private lemma smul_indicatorConstLp
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞) (r c : ℝ) :
    r • indicatorConstLp (p : ENNReal) hs hμs.ne c =
      indicatorConstLp (p : ENNReal) hs hμs.ne (r * c) := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_smul r (indicatorConstLp (p : ENNReal) hs hμs.ne c),
    (indicatorConstLp_coeFn :
      ((indicatorConstLp (p : ENNReal) hs hμs.ne c : Lp ℝ (p : ENNReal) μ) :
        α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c),
    (indicatorConstLp_coeFn :
      ((indicatorConstLp (p : ENNReal) hs hμs.ne (r * c) :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ r * c)
  ] with x hsmul hc hrc
  rw [hsmul, hrc]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hc]
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs]
  · simp [Set.indicator_of_notMem hxs]

/-- `∀ f ∈ Lₚ(μ), f > 0` there exists measurable set `s`, with `0 < μ(s)`, and
some `0 < c` such that `c1_s ≤ f` a.e. -/
private lemma exists_indicatorConstLp_le_of_pos
    [Fact (0 < p)]
    {f : Lp ℝ (p : ENNReal) μ} (hf : 0 < f) :
    ∃ (s : Set α) (hs : MeasurableSet s) (hμs : μ s < ∞) (c : ℝ),
      0 < μ s ∧ 0 < c ∧
        indicatorConstLp (p : ENNReal) hs hμs.ne c ≤ f := by
  have hf_ae_nonneg : 0 ≤ᵐ[μ] (f : α → ℝ) := (Lp.coeFn_nonneg f).2 hf.le
  have hf_not_ae_zero : ¬(f : α → ℝ) =ᵐ[μ] 0 := by
    intro hzero
    apply hf.ne'
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℝ (p : ENNReal) μ).symm
  have hpos_ne_zero : μ {x | 0 < (f : α → ℝ) x} ≠ 0 := by
    intro hμ
    have hnotpos := measure_eq_zero_iff_ae_notMem.mp hμ
    apply hf_not_ae_zero
    filter_upwards [hf_ae_nonneg, hnotpos] with x hx_nonneg hx_notpos
    exact le_antisymm (not_lt.mp hx_notpos) hx_nonneg
  let S : ℕ → Set α := fun n ↦
    {x | ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (f : α → ℝ) x}
  have hcover : {x | 0 < (f : α → ℝ) x} ⊆ ⋃ n, S n := by
    intro x hx
    change 0 < (f : α → ℝ) x at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    change ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (f : α → ℝ) x
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using hn.le
  have hiUnion_ne_zero : μ (⋃ n, S n) ≠ 0 := by
    intro hμ
    exact hpos_ne_zero (measure_mono_null hcover hμ)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hiUnion_ne_zero
  let c : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  have hc : 0 < c := by positivity
  have hS : MeasurableSet (S n) :=
    (Lp.stronglyMeasurable f).measurable measurableSet_Ici
  have hp0 : (p : ENNReal) ≠ 0 := by
    exact_mod_cast (Fact.out : (0 : ℝ≥0) < p).ne'
  have hptop : (p : ENNReal) ≠ ∞ := by simp
  let ε : ℝ≥0 := ⟨c, hc.le⟩
  have hε : ε ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h
    simp only [ε, NNReal.coe_zero] at h'
    exact hc.ne' h'
  have hbig : μ {x | ε ≤ ‖(f : α → ℝ) x‖₊} < ∞ :=
    (Lp.memLp f).meas_ge_lt_top hp0 hptop hε
  have hS_finite : μ (S n) < ∞ := lt_of_le_of_lt (measure_mono fun x hx ↦ by
    change c ≤ (f : α → ℝ) x at hx
    change ε ≤ ‖(f : α → ℝ) x‖₊
    apply NNReal.coe_le_coe.1
    change c ≤ ‖(f : α → ℝ) x‖
    simpa [Real.norm_eq_abs] using hx.trans (le_abs_self ((f : α → ℝ) x))) hbig
  have hindcoe :
      ((indicatorConstLp (p : ENNReal) hS hS_finite.ne c :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] (S n).indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  refine ⟨S n, hS, hS_finite, c, hn, hc, ?_⟩
  rw [← Lp.coeFn_le]
  filter_upwards [hindcoe, hf_ae_nonneg] with x hind hnonneg
  rw [hind]
  by_cases hxs : x ∈ S n
  · rw [Set.indicator_of_mem hxs]
    exact hxs
  · rw [Set.indicator_of_notMem hxs]
    exact hnonneg

private lemma indicatorConstLp_nonneg
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞)
    {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ indicatorConstLp (p : ENNReal) hs hμs.ne c := by
  rw [← Lp.coeFn_nonneg]
  have hcoe :
      ((indicatorConstLp (p : ENNReal) hs hμs.ne c :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  filter_upwards [hcoe] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
    exact hc
  · rw [Set.indicator_of_notMem hxs]
    simp

private lemma indicatorConstLp_le_of_subset
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hμt : μ t < ∞) (hts : t ⊆ s)
    {c : ℝ} (hc : 0 ≤ c) :
    indicatorConstLp (p : ENNReal) ht hμt.ne c ≤
      indicatorConstLp (p : ENNReal) hs hμs.ne c := by
  rw [← Lp.coeFn_le]
  have htcoe :
      ((indicatorConstLp (p : ENNReal) ht hμt.ne c :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] t.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  have hscoe :
      ((indicatorConstLp (p : ENNReal) hs hμs.ne c :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  filter_upwards [htcoe, hscoe] with x htx hsx
  rw [htx, hsx]
  by_cases hxt : x ∈ t
  · rw [Set.indicator_of_mem hxt, Set.indicator_of_mem (hts hxt)]
  · rw [Set.indicator_of_notMem hxt]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      exact hc
    · rw [Set.indicator_of_notMem hxs]

private lemma indicatorConstLp_disjoint
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hμt : μ t < ∞) (hst : Disjoint s t)
    {c : ℝ} (hc : 0 ≤ c) :
    IsVLDisjoint
      (indicatorConstLp (p : ENNReal) hs hμs.ne c)
      (indicatorConstLp (p : ENNReal) ht hμt.ne c) := by
  apply isVLDisjoint_of_inf_eq_zero
  apply Lp.ext
  have hscoe :
      ((indicatorConstLp (p : ENNReal) hs hμs.ne c :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  have htcoe :
      ((indicatorConstLp (p : ENNReal) ht hμt.ne c :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] t.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  filter_upwards [Lp.coeFn_inf
    (indicatorConstLp (p : ENNReal) hs hμs.ne c)
    (indicatorConstLp (p : ENNReal) ht hμt.ne c),
    hscoe, htcoe, Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hinf hsx htx hzero
  rw [hinf, hzero]
  simp only [Pi.inf_apply]
  rw [hsx, htx]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.1 hst hxs
    rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxt]
    exact inf_eq_right.2 hc
  · rw [Set.indicator_of_notMem hxs]
    by_cases hxt : x ∈ t
    · rw [Set.indicator_of_mem hxt]
      exact inf_eq_left.2 hc
    · rw [Set.indicator_of_notMem hxt]
      simp

/-- A strictly positive constant function on a finite measure theoretic atom is
a lattice atom of `Lₚ`. -/
theorem Measure.IsAtom.isVLAtom_indicatorConstLp
    {s : Set α} (hs : μ.IsAtom s) (hμs : μ s < ∞)
    {c : ℝ} (hc : 0 < c) :
    IsVLAtom (indicatorConstLp (p : ENNReal) hs.1 hμs.ne c) := by
  let a := indicatorConstLp (p : ENNReal) hs.1 hμs.ne c
  refine ⟨(indicatorConstLp_pos_iff hs.1 hμs hc).2 hs.2.1, ?_⟩
  intro b hb_nonneg hba
  obtain ⟨d, hd⟩ := Measure.IsAtom.exists_ae_eq_const hs hμs
    (Lp.stronglyMeasurable b).measurable.aemeasurable
  have hd_on_s : ∀ᵐ x ∂μ, x ∈ s → (b : α → ℝ) x = d :=
    (ae_restrict_iff' hs.1).1 hd
  have hb_ae_nonneg : 0 ≤ᵐ[μ] (b : α → ℝ) := (Lp.coeFn_nonneg b).2 hb_nonneg
  have hba_ae : (b : α → ℝ) ≤ᵐ[μ] (a : α → ℝ) := (Lp.coeFn_le b a).2 hba
  have ha_coe : (a : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c :=
    indicatorConstLp_coeFn
  have hd_coe :
      ((indicatorConstLp (p : ENNReal) hs.1 hμs.ne d :
        Lp ℝ (p : ENNReal) μ) : α → ℝ) =ᵐ[μ] s.indicator fun _ ↦ d :=
    indicatorConstLp_coeFn
  have hb_indicator : b = indicatorConstLp (p : ENNReal) hs.1 hμs.ne d := by
    apply Lp.ext
    filter_upwards [hd_on_s, hb_ae_nonneg, hba_ae, ha_coe, hd_coe]
      with x hd_on_s hb0 hba ha hind
    rw [hind]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      exact hd_on_s hxs
    · rw [Set.indicator_of_notMem hxs]
      have hb0' : 0 ≤ (b : α → ℝ) x := by simpa using hb0
      have ha0 : (a : α → ℝ) x = 0 :=
        ha.trans (Set.indicator_of_notMem hxs fun _ ↦ c)
      exact le_antisymm (hba.trans_eq ha0) hb0'
  refine ⟨d / c, hb_indicator.trans ?_⟩
  rw [smul_indicatorConstLp hs.1 hμs]
  congr 1
  exact (div_mul_cancel₀ d hc.ne').symm

/-- If a strictly positive constant indicator is a lattice atom of `Lₚ`,
then its support is a measure theoretic atom. -/
theorem Measure.isAtom_of_isVLAtom_indicatorConstLp
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞)
    {c : ℝ} (hc : 0 < c)
    (ha : IsVLAtom (indicatorConstLp (p : ENNReal) hs hμs.ne c)) :
    μ.IsAtom s := by
  refine ⟨hs, (indicatorConstLp_pos_iff hs hμs hc).1 ha.pos, ?_⟩
  intro t ht hts
  by_cases hμt : μ t = 0
  · exact Or.inl hμt
  right
  have hμt_pos : 0 < μ t := pos_iff_ne_zero.2 hμt
  have hμt_finite : μ t < ∞ := lt_of_le_of_lt (measure_mono hts) hμs
  let u := s \ t
  have hu : MeasurableSet u := hs.diff ht
  have hus : u ⊆ s := Set.diff_subset
  have hμu_finite : μ u < ∞ := lt_of_le_of_lt (measure_mono hus) hμs
  let x := indicatorConstLp (p : ENNReal) ht hμt_finite.ne c
  let y := indicatorConstLp (p : ENNReal) hu hμu_finite.ne c
  let a := indicatorConstLp (p : ENNReal) hs hμs.ne c
  have hx0 : 0 ≤ x := indicatorConstLp_nonneg ht hμt_finite hc.le
  have hy0 : 0 ≤ y := indicatorConstLp_nonneg hu hμu_finite hc.le
  have hxa : x ≤ a := indicatorConstLp_le_of_subset hs ht hμs hμt_finite hts hc.le
  have hya : y ≤ a := indicatorConstLp_le_of_subset hs hu hμs hμu_finite hus hc.le
  have htu : Disjoint t u := Set.disjoint_sdiff_right
  have hxy : IsVLDisjoint x y :=
    indicatorConstLp_disjoint ht hu hμt_finite hμu_finite htu hc.le
  rcases eq_zero_or_eq_zero_of_isVLDisjoint_of_isVLAtom ha hx0 hxa hy0 hya hxy with
    hx | hy
  · have hx_pos : 0 < x := (indicatorConstLp_pos_iff ht hμt_finite hc).2 hμt_pos
    exact (hx_pos.ne' hx).elim
  · have hμu : μ u = 0 := by
      apply nonpos_iff_eq_zero.mp
      exact le_of_not_gt fun hμu_pos ↦
        ((indicatorConstLp_pos_iff hu hμu_finite hc).2 hμu_pos).ne' hy
    have hdiff := measure_diff hts ht.nullMeasurableSet hμt_finite.ne
    have hst : μ s ≤ μ t := tsub_eq_zero_iff_le.mp (hdiff ▸ hμu)
    exact le_antisymm (measure_mono hts) hst

/-- A strictly positive constant indicator is a lattice atom of `Lₚ`
exactly when its support is a finite measure theoretic atom. -/
theorem isVLAtom_indicatorConstLp_iff
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞)
    {c : ℝ} (hc : 0 < c) :
    IsVLAtom (indicatorConstLp (p : ENNReal) hs hμs.ne c) ↔ μ.IsAtom s := by
  exact ⟨Measure.isAtom_of_isVLAtom_indicatorConstLp hs hμs hc,
    fun ha ↦ Measure.IsAtom.isVLAtom_indicatorConstLp ha hμs hc⟩

/-- The lattice atoms of `Lₚ` are exactly the strictly positive constant
multiples of indicators of finite measure theoretic atoms. -/
theorem isVLAtom_iff_exists_isAtom
    [Fact (0 < p)]
    {a : Lp ℝ (p : ENNReal) μ} :
    IsVLAtom a ↔
      ∃ (s : Set α) (hs : μ.IsAtom s) (hμs : μ s < ∞) (c : ℝ),
        0 < c ∧
          a = indicatorConstLp (p : ENNReal) hs.1 hμs.ne c := by
  constructor
  · intro ha
    obtain ⟨s, hs, hμs, c, hμs_pos, hc, hba⟩ :=
      exists_indicatorConstLp_le_of_pos ha.pos
    let b := indicatorConstLp (p : ENNReal) hs hμs.ne c
    have hb_pos : 0 < b := (indicatorConstLp_pos_iff hs hμs hc).2 hμs_pos
    obtain ⟨r, hr⟩ := ha.2 b hb_pos.le hba
    have hr_pos : 0 < r := by
      by_contra hr_nonpos
      have hble : b ≤ 0 := by
        rw [hr]
        exact smul_nonpos_of_nonpos_of_nonneg (not_lt.mp hr_nonpos) ha.pos.le
      exact (not_le_of_gt hb_pos) hble
    have ha_recover : a = r⁻¹ • b := by
      calc
        a = (r⁻¹ * r) • a := by rw [inv_mul_cancel₀ hr_pos.ne', one_smul]
        _ = r⁻¹ • (r • a) := by rw [smul_smul]
        _ = r⁻¹ • b := by rw [← hr]
    let d := r⁻¹ * c
    have hd : 0 < d := mul_pos (inv_pos.mpr hr_pos) hc
    have ha_indicator : a = indicatorConstLp (p : ENNReal) hs hμs.ne d :=
      ha_recover.trans (smul_indicatorConstLp hs hμs r⁻¹ c)
    have hind_atom : IsVLAtom (indicatorConstLp (p : ENNReal) hs hμs.ne d) := by
      rwa [← ha_indicator]
    have hs_atom := Measure.isAtom_of_isVLAtom_indicatorConstLp hs hμs hd hind_atom
    exact ⟨s, hs_atom, hμs, d, hd, ha_indicator⟩
  · rintro ⟨s, hs, hμs, c, hc, rfl⟩
    exact Measure.IsAtom.isVLAtom_indicatorConstLp hs hμs hc
