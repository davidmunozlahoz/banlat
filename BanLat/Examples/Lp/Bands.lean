/-
Authors: Tristan Romanov
-/

import BanLat.Examples.Lp.OrderContinuous
import BanLat.OrderContinuous.Ando
import BanLat.Examples.Lp.CountableChainCondition

/-!
# Support bands in real `Lp`

Measurable sets define projection bands by almost-everywhere support. For sigma-finite
measures and finite exponents at least one, every band arises this way, uniquely modulo
null sets. The corresponding projection is multiplication by the indicator.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Lp

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
private lemma supported_sSup {s : Set α} (hs : MeasurableSet s)
    (S : Set (Lp ℝ p μ))
    (hS : ∀ f ∈ S, ∀ᵐ x ∂μ, x ∉ s → f x = 0) (hne : S.Nonempty)
    (f : Lp ℝ p μ) (hf : IsLUB S f) : ∀ᵐ x ∂μ, x ∉ s → f x = 0 := by
  classical
  obtain ⟨g0, hg0⟩ := hne
  have hg0s : ∀ᵐ x ∂μ, x ∉ s → g0 x = 0 := hS _ hg0
  have hle0 := (Lp.coeFn_le g0 f).mpr (hf.1 hg0)
  obtain ⟨g, hg⟩ : ∃ g : Lp ℝ p μ, ⇑g =ᵐ[μ] s.indicator f :=
    ⟨_, ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp⟩
  have hub : g ∈ upperBounds S := by
    intro h hh
    have hhs : ∀ᵐ x ∂μ, x ∉ s → h x = 0 := hS _ hh
    have hhf := (Lp.coeFn_le h f).mpr (hf.1 hh)
    apply (Lp.coeFn_le h g).mp
    filter_upwards [hhs, hhf, hg] with x hx1 hx2 hx3
    by_cases hxs : x ∈ s
    · have hx2' : h x ≤ f x := hx2
      rw [hx3, Set.indicator_of_mem hxs]
      exact hx2'
    · exact le_of_eq (by rw [hx3, Set.indicator_of_notMem hxs, hx1 hxs])
  have hfg := (Lp.coeFn_le f g).mpr (hf.2 hub)
  filter_upwards [hg0s, hle0, hfg, hg] with x h1 h2 h3 h4 hxs
  have h2' : g0 x ≤ f x := h2
  have h3' : f x ≤ g x := h3
  rw [h4, Set.indicator_of_notMem hxs] at h3'
  rw [h1 hxs] at h2'
  exact le_antisymm h3' h2'

variable (μ p) in
/-- `L^p(s)`: the classes that vanish almost everywhere off `s`. -/
def supportBand (s : Set α) (hs : MeasurableSet s) : Band (Lp ℝ p μ) where
  carrier := {f | ∀ᵐ x ∂μ, x ∉ s → f x = 0}
  add_mem' := by
    classical
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at *
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx hxs
    rw [hx, Pi.add_apply, hfx hxs, hgx hxs, add_zero]
  zero_mem' := by
    classical
    filter_upwards [Lp.coeFn_zero ℝ p μ] with x hx _
    rw [hx]
    rfl
  smul_mem' := by
    classical
    intro c f hf
    simp only [Set.mem_ofPred_eq] at *
    filter_upwards [Lp.coeFn_smul c f, hf] with x hx hfx hxs
    rw [hx, Pi.smul_apply, hfx hxs, smul_zero]
  sup_mem' := by
    classical
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at *
    filter_upwards [Lp.coeFn_sup f g, hf, hg] with x hx hfx hgx hxs
    rw [hx, Pi.sup_apply, hfx hxs, hgx hxs, sup_idem]
  solid' := by
    classical
    intro f g hf hg0 hgf
    simp only [Set.mem_ofPred_eq] at *
    filter_upwards [hf, (Lp.coeFn_nonneg g).mpr hg0, (Lp.coeFn_le g f).mpr hgf]
      with x h1 h2 h3 hxs
    have h2' : (0 : ℝ) ≤ g x := h2
    have h3' : g x ≤ f x := h3
    rw [h1 hxs] at h3'
    exact le_antisymm h3' h2'
  sSup_mem' := fun S hS hne f hf ↦ supported_sSup hs S (fun _ hf ↦ hS hf) hne f hf

omit [Fact (1 ≤ p)] in
/-- Membership means vanishing almost everywhere outside the set. -/
theorem mem_supportBand {s : Set α} {hs : MeasurableSet s} {f : Lp ℝ p μ} :
    f ∈ supportBand μ p s hs ↔ ∀ᵐ x ∂μ, x ∉ s → f x = 0 := Iff.rfl

omit [Fact (1 ≤ p)] in
private theorem ae_eq_zero_or_of_isVLDisjoint {f g : Lp ℝ p μ}
    (h : IsVLDisjoint f g) : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0 := by
  classical
  have hd := measure_eq_zero_iff_ae_notMem.mp (support_aeDisjoint h)
  filter_upwards [hd] with x hx
  simpa only [Set.mem_inter_iff, Function.mem_support, not_and_or, not_not] using hx

omit [Fact (1 ≤ p)] in
/-- Elements of `Lp` with a.e. disjoint supports are disjoint. -/
private theorem isVLDisjoint_of_ae {f g : Lp ℝ p μ} (h : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    IsVLDisjoint f g := by
  classical
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_inf |f| |g|, Lp.coeFn_abs f, Lp.coeFn_abs g,
    Lp.coeFn_zero ℝ p μ] with x hx hinf hf hg hz
  rw [hinf, hz]
  change min ((|f| : Lp ℝ p μ) x) ((|g| : Lp ℝ p μ) x) = (0 : ℝ)
  rw [hf, hg]
  rcases hx with h0 | h0
  · rw [h0, abs_zero]
    exact min_eq_left (abs_nonneg _)
  · rw [h0, abs_zero]
    exact min_eq_right (abs_nonneg _)

omit [Fact (1 ≤ p)] in
/-- The decomposition `f = 1_s f + 1_{sᶜ} f` along a support band. -/
private theorem exists_decomp_supportBand {s : Set α} (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    ∃ y z : Lp ℝ p μ, y ∈ supportBand μ p s hs ∧
      z ∈ disjointComplement (supportBand μ p s hs : Set (Lp ℝ p μ)) ∧ f = y + z ∧
      ⇑y =ᵐ[μ] s.indicator f := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : Lp ℝ p μ, ⇑y =ᵐ[μ] s.indicator f :=
    ⟨_, ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp⟩
  obtain ⟨z, hz⟩ : ∃ z : Lp ℝ p μ, ⇑z =ᵐ[μ] sᶜ.indicator f :=
    ⟨_, ((Lp.memLp f).indicator hs.compl.nullMeasurableSet).coeFn_toLp⟩
  refine ⟨y, z, ?_, ?_, ?_, hy⟩
  · rw [mem_supportBand]
    filter_upwards [hy] with x hx hxs
    rw [hx, Set.indicator_of_notMem hxs]
  · intro a ha
    have ha' : ∀ᵐ x ∂μ, x ∉ s → a x = 0 := ha
    apply isVLDisjoint_of_ae
    filter_upwards [hz, ha'] with x hx hax
    by_cases hxs : x ∈ s
    · left
      rw [hx, Set.indicator_of_notMem (show x ∉ sᶜ from fun h ↦ h hxs)]
    · right
      exact hax hxs
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add y z, hy, hz] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2, Set.indicator_self_add_compl_apply]

variable (μ p) in
/-- `L^p(s)` is a projection band, for every measure and every `1 ≤ p ≤ ∞`. -/
def supportProjectionBand {s : Set α} (hs : MeasurableSet s) : ProjectionBand (Lp ℝ p μ) where
  toBand := supportBand μ p s hs
  decomposition' f := by
    obtain ⟨y, z, hy, hz, hf, -⟩ := exists_decomp_supportBand hs f
    exact ⟨y, z, hy, hz, hf⟩

omit [Fact (1 ≤ p)] in
/-- The band projection onto `L^p(s)` is multiplication by the indicator of `s`. -/
theorem bandProjection_supportProjectionBand {s : Set α} (hs : MeasurableSet s)
    (f : Lp ℝ p μ) :
    ⇑((supportProjectionBand μ p hs).bandProjection f) =ᵐ[μ] s.indicator f := by
  classical
  obtain ⟨y, z, hy, hz, hf, hyf⟩ := exists_decomp_supportBand hs f
  have hPy : (supportProjectionBand μ p hs).bandProjection f = y := by
    rw [hf, map_add, (supportProjectionBand μ p hs).bandProjection_eq_of_mem hy,
      (supportProjectionBand μ p hs).bandProjection_eq_zero_of_mem_dc hz, add_zero]
  rw [hPy]
  exact hyf

omit [Fact (1 ≤ p)] in
private lemma measure_sdiff_eq_zero_of_supportBand_subset [SigmaFinite μ]
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : (supportBand μ p s hs : Set (Lp ℝ p μ)) ⊆ supportBand μ p t ht) :
    μ (s \ t) = 0 := by
  classical
  have key : ∀ n, ∀ᵐ x ∂μ, x ∈ s ∩ spanningSets μ n → x ∈ t := by
    intro n
    have hmeas : MeasurableSet (s ∩ spanningSets μ n) :=
      hs.inter (measurableSet_spanningSets μ n)
    have hfin : μ (s ∩ spanningSets μ n) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_spanningSets_lt_top μ n)).ne
    obtain ⟨e, he⟩ : ∃ e : Lp ℝ p μ,
        ⇑e =ᵐ[μ] (s ∩ spanningSets μ n).indicator (fun _ ↦ (1 : ℝ)) :=
      ⟨indicatorConstLp p hmeas hfin (1 : ℝ), indicatorConstLp_coeFn⟩
    have hes : e ∈ supportBand μ p s hs := by
      filter_upwards [he] with x hx hxs
      rw [hx, Set.indicator_of_notMem
        (show x ∉ s ∩ spanningSets μ n from fun hx' ↦ hxs hx'.1)]
    have het : ∀ᵐ x ∂μ, x ∉ t → e x = 0 := h hes
    filter_upwards [he, het] with x hx hxt hxsn
    by_contra hnt
    have h1 := hxt hnt
    rw [hx, Set.indicator_of_mem hxsn] at h1
    exact one_ne_zero h1
  have hst : ∀ᵐ x ∂μ, x ∈ s → x ∈ t := by
    filter_upwards [ae_all_iff.mpr key] with x hx hxs
    have hxU : x ∈ ⋃ n, spanningSets μ n := by
      rw [iUnion_spanningSets]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxU
    exact hx n ⟨hxs, hn⟩
  have h0 : μ {x | ¬(x ∈ s → x ∈ t)} = 0 := ae_iff.mp hst
  exact measure_mono_null
    (fun x (hx : x ∈ s \ t) ↦ show ¬(x ∈ s → x ∈ t) from fun h' ↦ hx.2 (h' hx.1)) h0

omit [Fact (1 ≤ p)] in
/-- For σ-finite `μ`, inclusion of support bands is inclusion of the sets up to null sets. -/
theorem supportBand_subset_iff [SigmaFinite μ] {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    (supportBand μ p s hs : Set (Lp ℝ p μ)) ⊆ supportBand μ p t ht ↔ μ (s \ t) = 0 := by
  classical
  constructor
  · exact measure_sdiff_eq_zero_of_supportBand_subset hs ht
  · intro h f hf
    have hf' : ∀ᵐ x ∂μ, x ∉ s → f x = 0 := hf
    have hst : ∀ᵐ x ∂μ, x ∉ s \ t :=
      ae_iff.mpr (measure_mono_null (fun x (hx : ¬¬ x ∈ s \ t) ↦ not_not.mp hx) h)
    filter_upwards [hf', hst] with x h1 h2 hxt
    by_cases hxs : x ∈ s
    · exact (h2 ⟨hxs, hxt⟩).elim
    · exact h1 hxs

omit [Fact (1 ≤ p)] in
/-- For σ-finite `μ`, two support bands agree iff the sets agree up to a null set. -/
theorem supportBand_eq_iff [SigmaFinite μ] {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    (supportBand μ p s hs : Set (Lp ℝ p μ)) = supportBand μ p t ht ↔ s =ᵐ[μ] t := by
  classical
  rw [Set.Subset.antisymm_iff, supportBand_subset_iff, supportBand_subset_iff, ae_eq_set]

end General

section OrderContinuous

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0} [Fact (1 ≤ p)]

local instance instFactOneLEENNRealLpBand : Fact (1 ≤ (p : ℝ≥0∞)) :=
  ⟨by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)⟩

private theorem exists_decomp (B : Band (Lp ℝ (p : ℝ≥0∞) μ))
    (f : Lp ℝ (p : ℝ≥0∞) μ) :
    ∃ y z : Lp ℝ (p : ℝ≥0∞) μ, y ∈ B ∧
      z ∈ disjointComplement (B : Set (Lp ℝ (p : ℝ≥0∞) μ)) ∧ f = y + z := by
  classical
  obtain ⟨P, hP⟩ := BanachLattice.projectionBand_of_isClosed_orderIdeal
    B.toOrderIdeal B.isClosed_coe
  obtain ⟨y, z, hy, hz, hf⟩ := P.decomposition f
  refine ⟨y, z, ?_, ?_, hf⟩
  · have hy' : y ∈ (P : Set (Lp ℝ (p : ℝ≥0∞) μ)) := hy
    rw [hP] at hy'
    exact hy'
  · intro b hb
    have hb' : b ∈ (B.toOrderIdeal : Set (Lp ℝ (p : ℝ≥0∞) μ)) := hb
    rw [← hP] at hb'
    exact hz b hb'

omit [Fact (1 ≤ p)] in
private lemma band_mem_supported [SigmaFinite μ]
    (B : Band (Lp ℝ (p : ℝ≥0∞) μ))
    (e y z : ℕ → Lp ℝ (p : ℝ≥0∞) μ)
    (he : ∀ n, ⇑(e n) =ᵐ[μ] (spanningSets μ n).indicator (fun _ ↦ (1 : ℝ)))
    (hz : ∀ n, z n ∈ disjointComplement (B : Set (Lp ℝ (p : ℝ≥0∞) μ)))
    (hyz : ∀ n, e n = y n + z n) (f : Lp ℝ (p : ℝ≥0∞) μ) (hf : f ∈ B) :
    ∀ᵐ x ∂μ, x ∉ ⋃ n, {x | y n x ≠ 0} → f x = 0 := by
  classical
  let A : Set α := ⋃ n, {x | y n x ≠ 0}
  have h1 : ∀ᵐ x ∂μ, ∀ n, e n x = y n x + z n x := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_add (y n) (z n)] with x hx
    rw [hyz n]
    exact hx
  have h2 : ∀ᵐ x ∂μ, ∀ n, z n x = 0 ∨ f x = 0 := by
    rw [ae_all_iff]
    intro n
    exact ae_eq_zero_or_of_isVLDisjoint (hz n f hf)
  have h3 : ∀ᵐ x ∂μ, ∀ n, e n x = (spanningSets μ n).indicator (fun _ ↦ (1 : ℝ)) x :=
    ae_all_iff.mpr he
  filter_upwards [h1, h2, h3] with x h1x h2x h3x hxA
  have hxU : x ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]
    trivial
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hxU
  have hyN : y N x = 0 := by
    by_contra hne
    exact hxA (Set.mem_iUnion.mpr ⟨N, hne⟩)
  have hzN : z N x = 1 := by
    have h := h1x N
    rw [h3x N, Set.indicator_of_mem hN, hyN, zero_add] at h
    exact h.symm
  rcases h2x N with h | h
  · rw [hzN] at h
    exact absurd h one_ne_zero
  · exact h

private lemma supported_mem_band
    (B : Band (Lp ℝ (p : ℝ≥0∞) μ)) (y : ℕ → Lp ℝ (p : ℝ≥0∞) μ)
    (hy : ∀ n, y n ∈ B) (f : Lp ℝ (p : ℝ≥0∞) μ)
    (hf : ∀ᵐ x ∂μ, x ∉ ⋃ n, {x | y n x ≠ 0} → f x = 0) : f ∈ B := by
  classical
  let A : Set α := ⋃ n, {x | y n x ≠ 0}
  have hf' : ∀ᵐ x ∂μ, x ∉ A → f x = 0 := hf
  obtain ⟨g, w, hg, hw, hfgw⟩ := exists_decomp B f
  have hw0 : w = 0 := by
    have hwy : ∀ n, ∀ᵐ x ∂μ, w x = 0 ∨ y n x = 0 :=
      fun n ↦ ae_eq_zero_or_of_isVLDisjoint (hw (y n) (hy n))
    have hwg : ∀ᵐ x ∂μ, w x = 0 ∨ g x = 0 := ae_eq_zero_or_of_isVLDisjoint (hw g hg)
    have hsum : ∀ᵐ x ∂μ, f x = g x + w x := by
      filter_upwards [Lp.coeFn_add g w] with x hx
      rw [hfgw]
      exact hx
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [ae_all_iff.mpr hwy, hwg, hsum, hf'] with x h1 h2 h3 h4
    by_cases hxA : x ∈ A
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxA
      rcases h1 n with h | h
      · exact h
      · exact (hn h).elim
    · rcases h2 with h | h
      · exact h
      · rw [h4 hxA, h, zero_add] at h3
        exact h3.symm
  rw [hfgw, hw0, add_zero]
  exact hg

/-- **Classification.** For σ-finite `μ` and finite `p ≥ 1`, every band of `Lp ℝ p μ` is a
support band `L^p(A)`. -/
theorem exists_eq_supportBand [SigmaFinite μ] (B : Band (Lp ℝ (p : ℝ≥0∞) μ)) :
    ∃ (A : Set α) (hA : MeasurableSet A),
      (B : Set (Lp ℝ (p : ℝ≥0∞) μ)) = supportBand μ (p : ℝ≥0∞) A hA := by
  classical
  have hfin : ∀ n, μ (spanningSets μ n) ≠ ∞ := fun n ↦ (measure_spanningSets_lt_top μ n).ne
  let e : ℕ → Lp ℝ (p : ℝ≥0∞) μ := fun n ↦
    indicatorConstLp (p : ℝ≥0∞) (measurableSet_spanningSets μ n) (hfin n) (1 : ℝ)
  have he : ∀ n, ⇑(e n) =ᵐ[μ] (spanningSets μ n).indicator (fun _ ↦ (1 : ℝ)) :=
    fun n ↦ indicatorConstLp_coeFn
  choose y z hy hz hyz using fun n ↦ exists_decomp B (e n)
  let A : Set α := ⋃ n, {x | y n x ≠ 0}
  have hA : MeasurableSet A := MeasurableSet.iUnion fun n ↦
    (Lp.stronglyMeasurable (y n)).measurable (measurableSet_singleton (0 : ℝ)).compl
  refine ⟨A, hA, ?_⟩
  apply Set.Subset.antisymm
  · intro f hf
    exact band_mem_supported B e y z he hz hyz f hf
  · intro f hf
    exact supported_mem_band B y hy f hf

/-- **Classification with uniqueness.** For σ-finite `μ` and finite `p ≥ 1`, every band of
`Lp ℝ p μ` is `L^p(A)` for a measurable `A`, unique up to a null set. -/
theorem exists_supportBand_unique_ae [SigmaFinite μ] (B : Band (Lp ℝ (p : ℝ≥0∞) μ)) :
    ∃ (A : Set α) (hA : MeasurableSet A),
      (B : Set (Lp ℝ (p : ℝ≥0∞) μ)) = supportBand μ (p : ℝ≥0∞) A hA ∧
      ∀ (A' : Set α) (hA' : MeasurableSet A'),
        (B : Set (Lp ℝ (p : ℝ≥0∞) μ)) = supportBand μ (p : ℝ≥0∞) A' hA' → A' =ᵐ[μ] A := by
  classical
  obtain ⟨A, hA, hB⟩ := exists_eq_supportBand B
  refine ⟨A, hA, hB, fun A' hA' hB' ↦ ?_⟩
  exact (supportBand_eq_iff (μ := μ) (p := (p : ℝ≥0∞)) hA' hA).mp (hB'.symm.trans hB)

end OrderContinuous

end MeasureTheory.Lp
