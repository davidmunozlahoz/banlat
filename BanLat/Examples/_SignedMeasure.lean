import BanLat.ALSpace
import BanLat.Atom
import BanLat.Examples.Lp.Basic
import BanLat.OrderContinuous.Basic
import BanLat.SignedMeasure.Basic

/-!
# Further structure on signed measures

The Banach-lattice structure on `MeasureTheory.SignedMeasure α` is developed in
`BanLat.SignedMeasure.Basic`. This file adds the remaining signed-measure
structure used later in the project:

* the AL-space axiom for the total-variation norm;
* identification of principal bands with absolutely continuous signed measures,
  and the resulting Radon–Nikodym equivalence with `L¹`;
* atoms and Dirac measures.
-/

open MeasureTheory

namespace MeasureTheory
namespace SignedMeasure

variable {α : Type*} [MeasurableSpace α]

/-! ### AL-space structure

For non-negative signed measures `s` and `t`, the total-variation norm is
additive: `‖s + t‖ = (s + t) univ = s univ + t univ = ‖s‖ + ‖t‖`. This is the
AL-axiom, making `SignedMeasure α` an AL-space — equivalently, an
`L¹`-space in the abstract sense of Kakutani. -/

/-- The total-variation norm is additive on the positive cone: for
non-negative signed measures `s` and `t`, `‖s + t‖ = ‖s‖ + ‖t‖`. -/
private lemma norm_add_of_nonneg {s t : SignedMeasure α}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : ‖s + t‖ = ‖s‖ + ‖t‖ := by
  rw [norm_of_nonneg (add_nonneg hs ht), norm_of_nonneg hs, norm_of_nonneg ht,
      VectorMeasure.add_apply]

/-- `SignedMeasure α` is an AL-space: the total-variation norm is
additive on the positive cone. -/
noncomputable instance instALSpace : ALSpace (SignedMeasure α) where
  norm_add_eq_of_nonneg := norm_add_of_nonneg

/-! ### Principal bands and `L¹(μ)` via the Radon–Nikodym correspondence

For a non-negative signed measure `s : SignedMeasure α`, the principal band
`Band.principalBand s` consists of the signed measures absolutely continuous
with respect to `s`. The **Radon–Nikodym derivative** `ν ↦ dν/ds` yields a
Banach-lattice isometric isomorphism from that principal band onto
`L¹(s⁺)`, where `s⁺` is the positive Jordan part of `s`. -/

private lemma eq_posPart_toSignedMeasure_of_nonneg
    {s : SignedMeasure α} (hs : 0 ≤ s) :
    s = s.toJordanDecomposition.posPart.toSignedMeasure := by
  have hneg : s.toJordanDecomposition.negPart.toSignedMeasure = 0 :=
    nonneg_iff_negPart_eq_zero.mp hs
  have h := posPart_sub_negPart s
  change s.toJordanDecomposition.posPart.toSignedMeasure -
      s.toJordanDecomposition.negPart.toSignedMeasure = s at h
  rw [hneg, sub_zero] at h
  exact h.symm

private lemma real_apply_posPart_of_nonneg
    {s : SignedMeasure α} (hs : 0 ≤ s) {E : Set α} (hE : MeasurableSet E) :
    (s.toJordanDecomposition.posPart E).toReal = s E := by
  conv_rhs => rw [eq_posPart_toSignedMeasure_of_nonneg hs]
  rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def]

/-- For `0 ≤ s`, absolute continuity of `ν` against `s` (as a signed measure)
is equivalent to absolute continuity of `ν` against the positive Jordan part of
`s` (as a vector measure in `ℝ≥0∞`). -/
private lemma absolutelyContinuous_iff_posPart_of_nonneg
    {s : SignedMeasure α} (hs : 0 ≤ s) {ν : SignedMeasure α} :
    ν ≪ᵥ s ↔ ν ≪ᵥ s.toJordanDecomposition.posPart.toENNRealVectorMeasure := by
  constructor
  · intro h
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hposE => ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hposE
    have hsE : s E = 0 := by
      rw [← real_apply_posPart_of_nonneg hs hE, hposE, ENNReal.toReal_zero]
    exact h hsE
  · intro h
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hsE => ?_
    have hfin : s.toJordanDecomposition.posPart E ≠ ⊤ := measure_ne_top _ _
    have hposzero : s.toJordanDecomposition.posPart E = 0 := by
      have : (s.toJordanDecomposition.posPart E).toReal = 0 := by
        rw [real_apply_posPart_of_nonneg hs hE]; exact hsE
      rcases (ENNReal.toReal_eq_zero_iff _).mp this with h1 | h1
      · exact h1
      · exact absurd h1 hfin
    have hE' : s.toJordanDecomposition.posPart.toENNRealVectorMeasure E = 0 := by
      rw [Measure.toENNRealVectorMeasure_apply_measurable hE]
      exact hposzero
    exact h hE'

/-- For `0 ≤ s`, `ν ≪ᵥ s` iff `ν.totalVariation ≪ s.toJordanDecomposition.posPart`. -/
private lemma totalVariation_absolutelyContinuous_iff_of_nonneg
    {s : SignedMeasure α} (hs : 0 ≤ s) {ν : SignedMeasure α} :
    ν ≪ᵥ s ↔ ν.totalVariation ≪ s.toJordanDecomposition.posPart := by
  rw [absolutelyContinuous_iff_posPart_of_nonneg hs]
  rw [absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]

/-- The posPart of an absolutely continuous signed measure is still absolutely
continuous (on the `totalVariation` side). -/
private lemma abs_le_of_absolutelyContinuous
    {s : SignedMeasure α} (hs : 0 ≤ s) {ν₁ ν₂ : SignedMeasure α}
    (h : ν₁ ≪ᵥ s) (hle : |ν₂| ≤ |ν₁|) : ν₂ ≪ᵥ s := by
  rw [totalVariation_absolutelyContinuous_iff_of_nonneg hs] at h ⊢
  refine Measure.AbsolutelyContinuous.mk fun E hE hposE => ?_
  have hν₁ : ν₁.totalVariation E = 0 := h hposE
  -- |ν₂| ≤ |ν₁| implies ν₂.totalVariation E ≤ ν₁.totalVariation E as ennreal?
  -- Use abs_apply_eq_totalVariation
  have h1 : (ν₁.totalVariation E).toReal = (|ν₁| : SignedMeasure α) E :=
    (abs_apply_eq_totalVariation ν₁ E hE).symm
  have h2 : (ν₂.totalVariation E).toReal = (|ν₂| : SignedMeasure α) E :=
    (abs_apply_eq_totalVariation ν₂ E hE).symm
  have h3 : (|ν₂| : SignedMeasure α) E ≤ (|ν₁| : SignedMeasure α) E := hle E hE
  have h4 : (ν₂.totalVariation E).toReal ≤ (ν₁.totalVariation E).toReal := by
    rw [h2, h1]; exact h3
  have hν₁zero : (ν₁.totalVariation E).toReal = 0 := by rw [hν₁]; rfl
  rw [hν₁zero] at h4
  have hν₂nn : 0 ≤ (ν₂.totalVariation E).toReal := ENNReal.toReal_nonneg
  have hν₂real : (ν₂.totalVariation E).toReal = 0 := le_antisymm h4 hν₂nn
  have hfin : ν₂.totalVariation E ≠ ⊤ := measure_ne_top _ _
  rcases (ENNReal.toReal_eq_zero_iff _).mp hν₂real with h5 | h5
  · exact h5
  · exact absurd h5 hfin

/-- The value of a signed measure at a fixed measurable set is bounded in
absolute value by the total-variation norm. A local copy, available before the
`applyCLM` definition in the Atoms section. -/
private lemma abs_apply_le_norm' (s : SignedMeasure α) {E : Set α}
    (hE : MeasurableSet E) : |s E| ≤ ‖s‖ := by
  have h_tv : (|s| : SignedMeasure α) E ≤ ‖s‖ := by
    rw [abs_apply_eq_totalVariation s E hE, norm_def]
    exact ENNReal.toReal_mono (totalVariation_univ_lt_top s).ne
      (measure_mono (Set.subset_univ E))
  have h_pos : s E ≤ (|s| : SignedMeasure α) E := le_abs_self s E hE
  have h_neg : -s E ≤ (|s| : SignedMeasure α) E := by
    have h := (neg_le_abs s) E hE
    rwa [VectorMeasure.neg_apply] at h
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Evaluation of a signed measure at a fixed measurable set is continuous. -/
private lemma continuous_apply_measurable {E : Set α} (hE : MeasurableSet E) :
    Continuous (fun ν : SignedMeasure α => ν E) := by
  refine Metric.continuous_iff.mpr fun ν ε hε => ⟨ε, hε, fun ν' hν' => ?_⟩
  rw [Real.dist_eq]
  have hsub : ν' E - ν E = (ν' - ν) E := by
    rw [VectorMeasure.sub_apply]
  rw [hsub]
  calc |(ν' - ν) E| ≤ ‖ν' - ν‖ := abs_apply_le_norm' _ hE
    _ = dist ν' ν := (dist_eq_norm _ _).symm
    _ < ε := hν'

/-- The set of signed measures absolutely continuous to `s` forms an order
ideal. -/
private def absolutelyContinuousOrderIdeal {s : SignedMeasure α} (hs : 0 ≤ s) :
    OrderIdeal (SignedMeasure α) where
  toSubmodule :=
    { carrier := {ν | ν ≪ᵥ s}
      add_mem' := fun hν₁ hν₂ => VectorMeasure.AbsolutelyContinuous.add hν₁ hν₂
      zero_mem' := VectorMeasure.AbsolutelyContinuous.zero _
      smul_mem' := fun _ _ hν => VectorMeasure.AbsolutelyContinuous.smul hν }
  sup_mem' := fun {ν₁ ν₂} hν₁ hν₂ => by
    change ν₁ ⊔ ν₂ ≪ᵥ s
    rw [max_def]
    refine VectorMeasure.AbsolutelyContinuous.add hν₂ ?_
    have hsub : ν₁ - ν₂ ≪ᵥ s := VectorMeasure.AbsolutelyContinuous.sub hν₁ hν₂
    refine abs_le_of_absolutelyContinuous hs hsub ?_
    rw [abs_of_nonneg (zero_le_posPart _)]
    intro E hE
    rw [abs_eq_posPart_add_negPart, VectorMeasure.add_apply]
    have h2 : (0 : SignedMeasure α) E ≤ (ν₁ - ν₂).negPart E :=
      zero_le_negPart _ E hE
    rw [VectorMeasure.zero_apply] at h2
    linarith
  solid' := fun {ν₁ ν₂} hν₁ h₀ν₂ hν₂le => by
    change ν₂ ≪ᵥ s
    change ν₁ ≪ᵥ s at hν₁
    have h0ν₁ : 0 ≤ ν₁ := le_trans h₀ν₂ hν₂le
    refine abs_le_of_absolutelyContinuous hs hν₁ ?_
    rw [abs_of_nonneg h₀ν₂, abs_of_nonneg h0ν₁]
    exact hν₂le

/-- The set of signed measures absolutely continuous to `s` is closed in the
TV norm. -/
private lemma isClosed_absolutelyContinuous (s : SignedMeasure α) :
    IsClosed {ν : SignedMeasure α | ν ≪ᵥ s} := by
  have heq : {ν : SignedMeasure α | ν ≪ᵥ s} =
      ⋂ (E : Set α) (_ : MeasurableSet E) (_ : s E = 0), {ν | ν E = 0} := by
    ext ν
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · exact fun h E _ hsE => h hsE
    · intro h
      refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hsE => ?_
      exact h E hE hsE
  rw [heq]
  refine isClosed_iInter fun E => isClosed_iInter fun hE => isClosed_iInter fun _ => ?_
  exact isClosed_singleton.preimage (continuous_apply_measurable hE)

private lemma principalBand_subset_absolutelyContinuous
    {s : SignedMeasure α} (hs : 0 ≤ s) :
    (Band.principalBand s : Set (SignedMeasure α)) ⊆ {ν | ν ≪ᵥ s} := by
  set J := absolutelyContinuousOrderIdeal hs with hJ_def
  have hJ_set : (J : Set (SignedMeasure α)) = {ν | ν ≪ᵥ s} := rfl
  have hJ_closed : IsClosed ((J : Set (SignedMeasure α))) := by
    rw [hJ_set]
    exact isClosed_absolutelyContinuous s
  obtain ⟨B, hB⟩ := BanachLattice.band_of_isClosed_orderIdeal J hJ_closed
  have hB_eq : (B : Set (SignedMeasure α)) = {ν | ν ≪ᵥ s} := by
    rw [hB]; exact hJ_set
  -- s ∈ B via s ≪ᵥ s
  have hs_in : s ∈ (B : Set (SignedMeasure α)) := by
    rw [hB_eq]
    exact VectorMeasure.AbsolutelyContinuous.refl s
  have hsub : (Band.principalBand s : Set (SignedMeasure α)) ⊆ (B : Set (SignedMeasure α)) :=
    Band.bandGenerated_le (Set.singleton_subset_iff.mpr hs_in)
  exact hB_eq ▸ hsub

/-- The TV norm of `μ.withDensityᵥ f` equals the L¹ norm of `f` for integrable
`f`. -/
private lemma norm_withDensityᵥ_eq (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) :
    ‖μ.withDensityᵥ f‖ = ∫ x, |f x| ∂μ := by
  obtain ⟨g, hgm, hgae⟩ : ∃ g : α → ℝ, Measurable g ∧ f =ᵐ[μ] g :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  have hgi : Integrable g μ := hf.congr hgae
  have heq : μ.withDensityᵥ f = μ.withDensityᵥ g := WithDensityᵥEq.congr_ae hgae
  rw [heq, norm_def, totalVariation_withDensityᵥ_apply_univ hgm hgi]
  refine integral_congr_ae ?_
  filter_upwards [hgae] with x hx
  rw [hx]

/-- The map `f ↦ μ.withDensityᵥ f` from `Lp ℝ 1 μ` to `SignedMeasure α` is
continuous. -/
private lemma continuous_withDensityᵥ_L1 {μ : Measure α} [IsFiniteMeasure μ] :
    Continuous (fun f : Lp ℝ 1 μ => (μ.withDensityᵥ (f : α → ℝ) : SignedMeasure α)) := by
  refine Metric.continuous_iff.mpr fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩
  rw [dist_eq_norm] at hg ⊢
  have hgi : Integrable (⇑g : α → ℝ) μ := memLp_one_iff_integrable.mp (Lp.memLp g)
  have hfi : Integrable (⇑f : α → ℝ) μ := memLp_one_iff_integrable.mp (Lp.memLp f)
  have h_sub : (μ.withDensityᵥ (⇑g : α → ℝ) : SignedMeasure α) -
      (μ.withDensityᵥ (⇑f : α → ℝ) : SignedMeasure α) =
      μ.withDensityᵥ ((⇑g : α → ℝ) - ⇑f) := (withDensityᵥ_sub hgi hfi).symm
  rw [h_sub, norm_withDensityᵥ_eq μ (hgi.sub hfi)]
  have hL1 : ‖g - f‖ = ∫ x, ‖(⇑(g - f) : α → ℝ) x‖ ∂μ := L1.norm_eq_integral_norm (g - f)
  rw [hL1] at hg
  have hcoe : (⇑(g - f) : α → ℝ) =ᵐ[μ] ((⇑g : α → ℝ) - ⇑f) := Lp.coeFn_sub g f
  have heq_int : ∫ x, ‖(⇑(g - f) : α → ℝ) x‖ ∂μ =
      ∫ x, |(⇑g : α → ℝ) x - (⇑f : α → ℝ) x| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    rw [hx, Real.norm_eq_abs]
    rfl
  rw [heq_int] at hg
  exact hg

/-- The indicator `A.indicator (fun _ => c)` yields a withDensityᵥ that lies
in the principal band of `s`. -/
private lemma withDensityᵥ_indicator_mem_principalBand
    {s : SignedMeasure α} (hs : 0 ≤ s) (c : ℝ) {A : Set α} (hA : MeasurableSet A) :
    (s.toJordanDecomposition.posPart).withDensityᵥ
      (A.indicator (fun _ => c)) ∈ Band.principalBand s := by
  set μ := s.toJordanDecomposition.posPart with hμ_def
  have hint : Integrable (A.indicator (fun _ : α => c)) μ :=
    (integrable_const c).indicator hA
  -- The indicator's withDensityᵥ equals c • (μ.restrict A).toSignedMeasure
  have h_eq : μ.withDensityᵥ (A.indicator (fun _ : α => c)) =
      c • (μ.restrict A).toSignedMeasure := by
    ext E hE
    rw [withDensityᵥ_apply hint hE, VectorMeasure.smul_apply, smul_eq_mul,
        Measure.toSignedMeasure_apply_measurable hE,
        setIntegral_indicator hA, setIntegral_const, smul_eq_mul,
        measureReal_restrict_apply hE]
    ring
  rw [h_eq]
  -- c • (μ.restrict A).toSignedMeasure ∈ principalBand s
  have h_restr_le : (μ.restrict A).toSignedMeasure ≤ s := by
    intro E hE
    rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def,
        Measure.restrict_apply hE]
    rw [← real_apply_posPart_of_nonneg hs hE]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
  have h_restr_nn : (0 : SignedMeasure α) ≤ (μ.restrict A).toSignedMeasure :=
    Measure.zero_le_toSignedMeasure _
  have h_restr_in : (μ.restrict A).toSignedMeasure ∈ Band.principalBand s := by
    apply Band.principal_le_principalBand s
    refine ⟨1, zero_le_one, ?_⟩
    rw [one_smul, abs_of_nonneg h_restr_nn, abs_of_nonneg hs]
    exact h_restr_le
  exact (Band.principalBand s).toSubmodule.smul_mem c h_restr_in

/-- For every integrable function `g`, `μ.withDensityᵥ g` lies in the principal
band of the non-negative signed measure `s` whose positive Jordan part is `μ`. -/
private lemma withDensityᵥ_mem_principalBand
    {s : SignedMeasure α} (hs : 0 ≤ s) {g : α → ℝ}
    (hg : Integrable g s.toJordanDecomposition.posPart) :
    (s.toJordanDecomposition.posPart).withDensityᵥ g ∈
      Band.principalBand s := by
  refine hg.induction
    (P := fun g => s.toJordanDecomposition.posPart.withDensityᵥ g ∈
      (Band.principalBand s : Set (SignedMeasure α)))
    ?_ ?_ ?_ ?_
  · intro c A hA _
    exact withDensityᵥ_indicator_mem_principalBand hs c hA
  · intro g₁ g₂ _ hg₁ hg₂ hP₁ hP₂
    rw [withDensityᵥ_add hg₁ hg₂]
    exact (Band.principalBand s).toSubmodule.add_mem hP₁ hP₂
  · have hB_closed : IsClosed (Band.principalBand s : Set (SignedMeasure α)) :=
      Band.isClosed_coe _
    exact hB_closed.preimage continuous_withDensityᵥ_L1
  · intro g₁ g₂ hae _ hP₁
    rwa [← WithDensityᵥEq.congr_ae hae]

theorem principalBand_eq_absolutelyContinuous {s : SignedMeasure α} (hs : 0 ≤ s) :
    (Band.principalBand s : Set (SignedMeasure α)) = {ν | ν ≪ᵥ s} := by
  apply Set.Subset.antisymm (principalBand_subset_absolutelyContinuous hs)
  intro ν hν
  change ν ≪ᵥ s at hν
  set μ := s.toJordanDecomposition.posPart with hμ_def
  have hν_μ : ν ≪ᵥ μ.toENNRealVectorMeasure :=
    (absolutelyContinuous_iff_posPart_of_nonneg hs).mp hν
  have hrn : μ.withDensityᵥ (ν.rnDeriv μ) = ν :=
    withDensityᵥ_rnDeriv_eq ν μ hν_μ
  rw [← hrn]
  exact withDensityᵥ_mem_principalBand hs (integrable_rnDeriv ν μ)

/-- Forward direction of the Radon–Nikodym isomorphism: take a signed measure
in the principal band of `s` to its Radon–Nikodym derivative as an `L¹`
function. -/
private noncomputable def principalBandToLp {s : SignedMeasure α} (_hs : 0 ≤ s)
    (v : ↥(Band.principalBand s).toSubmodule) :
    Lp ℝ 1 s.toJordanDecomposition.posPart :=
  MemLp.toLp (v.val.rnDeriv s.toJordanDecomposition.posPart)
    (memLp_one_iff_integrable.mpr
      (integrable_rnDeriv v.val s.toJordanDecomposition.posPart))

/-- Inverse direction of the Radon–Nikodym isomorphism: take an `L¹` function
to its associated density-weighted signed measure. -/
private noncomputable def lpToPrincipalBand {s : SignedMeasure α} (hs : 0 ≤ s)
    (f : Lp ℝ 1 s.toJordanDecomposition.posPart) :
    ↥(Band.principalBand s).toSubmodule :=
  ⟨s.toJordanDecomposition.posPart.withDensityᵥ (⇑f),
    withDensityᵥ_mem_principalBand hs (memLp_one_iff_integrable.mp (Lp.memLp f))⟩

private lemma band_ac {s : SignedMeasure α} (hs : 0 ≤ s)
    {v : SignedMeasure α} (hv : v ∈ (Band.principalBand s : Set _)) :
    v ≪ᵥ s.toJordanDecomposition.posPart.toENNRealVectorMeasure :=
  (absolutelyContinuous_iff_posPart_of_nonneg hs).mp
    (principalBand_subset_absolutelyContinuous hs hv)

set_option maxHeartbeats 800000 in
-- `unfold` of nested `lpToPrincipalBand`/`principalBandToLp` is expensive
private lemma leftInv_eq {s : SignedMeasure α} (hs : 0 ≤ s)
    (v : ↥(Band.principalBand s).toSubmodule) :
    lpToPrincipalBand hs (principalBandToLp hs v) = v := by
  set μ := s.toJordanDecomposition.posPart with hμ
  refine Subtype.ext ?_
  unfold lpToPrincipalBand principalBandToLp
  exact (WithDensityᵥEq.congr_ae (MemLp.coeFn_toLp _)).trans
    (withDensityᵥ_rnDeriv_eq v.val μ (band_ac hs v.prop))

private lemma rightInv_ae {s : SignedMeasure α} (_hs : 0 ≤ s)
    (f : Lp ℝ 1 s.toJordanDecomposition.posPart) :
    SignedMeasure.rnDeriv
      (s.toJordanDecomposition.posPart.withDensityᵥ (⇑f))
      s.toJordanDecomposition.posPart
        =ᵐ[s.toJordanDecomposition.posPart] ⇑f := by
  have hfi : Integrable (⇑f) s.toJordanDecomposition.posPart :=
    memLp_one_iff_integrable.mp (Lp.memLp f)
  exact (Integrable.withDensityᵥ_eq_iff (integrable_rnDeriv _ _) hfi).mp
    (withDensityᵥ_rnDeriv_eq _ _
      (Measure.withDensityᵥ_absolutelyContinuous _ f))

set_option maxHeartbeats 400000 in
-- `simp only` of nested definitions is expensive
private lemma rightInv_eq {s : SignedMeasure α} (hs : 0 ≤ s)
    (f : Lp ℝ 1 s.toJordanDecomposition.posPart) :
    principalBandToLp hs (lpToPrincipalBand hs f) = f := by
  simp only [principalBandToLp, lpToPrincipalBand]
  exact (MemLp.toLp_congr _ _ (rightInv_ae hs f)).trans
    (Lp.toLp_coeFn f (Lp.memLp f))

private lemma norm_map_eq {s : SignedMeasure α} (hs : 0 ≤ s)
    (v : ↥(Band.principalBand s).toSubmodule) :
    ‖principalBandToLp hs v‖ = ‖v‖ := by
  set μ := s.toJordanDecomposition.posPart
  have hfi := integrable_rnDeriv v.val μ
  change ‖MemLp.toLp (v.val.rnDeriv μ) _‖ = ‖v.val‖
  rw [L1.norm_eq_integral_norm]
  calc ∫ x, ‖(MemLp.toLp (v.val.rnDeriv μ)
        (memLp_one_iff_integrable.mpr hfi) : α → ℝ) x‖ ∂μ
      = ∫ x, |v.val.rnDeriv μ x| ∂μ := by
        exact integral_congr_ae (by
          filter_upwards [MemLp.coeFn_toLp
            (memLp_one_iff_integrable.mpr hfi)] with x hx
          rw [hx, Real.norm_eq_abs])
    _ = ‖μ.withDensityᵥ (v.val.rnDeriv μ)‖ :=
        (norm_withDensityᵥ_eq μ hfi).symm
    _ = ‖v.val‖ := by
        rw [withDensityᵥ_rnDeriv_eq _ _ (band_ac hs v.prop)]

private lemma monotone_principalBandToLp {s : SignedMeasure α} (hs : 0 ≤ s)
    {v w : ↥(Band.principalBand s).toSubmodule} (h : v ≤ w) :
    principalBandToLp hs v ≤ principalBandToLp hs w := by
  set μ := s.toJordanDecomposition.posPart
  have hvi := integrable_rnDeriv v.val μ
  have hwi := integrable_rnDeriv w.val μ
  have h_ae : v.val.rnDeriv μ ≤ᵐ[μ] w.val.rnDeriv μ := by
    refine ae_le_of_forall_setIntegral_le hvi hwi fun E hE _ => ?_
    rw [← withDensityᵥ_apply hvi hE, ← withDensityᵥ_apply hwi hE,
        withDensityᵥ_rnDeriv_eq _ _ (band_ac hs v.prop),
        withDensityᵥ_rnDeriv_eq _ _ (band_ac hs w.prop)]
    exact h E hE
  change (principalBandToLp hs v : α →ₘ[μ] ℝ) ≤ principalBandToLp hs w
  rw [← AEEqFun.coeFn_le]
  filter_upwards [MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hvi),
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hwi), h_ae]
    with x hvx hwx hle
  exact hvx ▸ hwx ▸ hle

private lemma monotone_lpToPrincipalBand {s : SignedMeasure α} (hs : 0 ≤ s)
    {f g : Lp ℝ 1 s.toJordanDecomposition.posPart} (h : f ≤ g) :
    lpToPrincipalBand hs f ≤ lpToPrincipalBand hs g := by
  intro E hE
  simp only [lpToPrincipalBand]
  have hfi : Integrable (⇑f) s.toJordanDecomposition.posPart :=
    memLp_one_iff_integrable.mp (Lp.memLp f)
  have hgi : Integrable (⇑g) s.toJordanDecomposition.posPart :=
    memLp_one_iff_integrable.mp (Lp.memLp g)
  rw [withDensityᵥ_apply hfi hE, withDensityᵥ_apply hgi hE]
  have h_ae : (⇑f : α → ℝ) ≤ᵐ[s.toJordanDecomposition.posPart] ⇑g :=
    AEEqFun.coeFn_le.mpr h
  exact setIntegral_mono_ae hfi.integrableOn hgi.integrableOn h_ae

private lemma map_neg_eq {s : SignedMeasure α} (hs : 0 ≤ s)
    (v : ↥(Band.principalBand s).toSubmodule) :
    principalBandToLp hs (-v) = -principalBandToLp hs v := by
  change MemLp.toLp _ _ = -MemLp.toLp _ _
  rw [← MemLp.toLp_neg]
  exact MemLp.toLp_congr _ _ (rnDeriv_neg v.val _)

set_option maxHeartbeats 800000 in
-- assembling the `BanachLatEquiv` structure involves expensive unification
/-- The Radon–Nikodym correspondence `ν ↦ dν/ds⁺` is a Banach-lattice
isometric isomorphism from the principal band of a non-negative signed
measure `s` onto `L¹(s⁺)`, where `s⁺` is the positive Jordan part of `s`. -/
noncomputable def principalBandBanachLatEquivL1 {s : SignedMeasure α}
    (hs : 0 ≤ s) :
    BanachLatEquiv ↥(Band.principalBand s).toSubmodule
      (MeasureTheory.Lp ℝ 1 s.toJordanDecomposition.posPart) := by
  set μ := s.toJordanDecomposition.posPart
  have hmap_add : ∀ v w : ↥(Band.principalBand s).toSubmodule,
      principalBandToLp hs (v + w) =
        principalBandToLp hs v + principalBandToLp hs w := by
    intro v w; change MemLp.toLp _ _ = MemLp.toLp _ _ + MemLp.toLp _ _
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (rnDeriv_add v.val w.val μ)
  have hmap_smul : ∀ (r : ℝ) (v : ↥(Band.principalBand s).toSubmodule),
      principalBandToLp hs (r • v) =
        r • principalBandToLp hs v := by
    intro r v; change MemLp.toLp _ _ = r • MemLp.toLp _ _
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (rnDeriv_smul v.val μ r)
  have hmap_sup : ∀ v w : ↥(Band.principalBand s).toSubmodule,
      principalBandToLp hs (v ⊔ w) =
        principalBandToLp hs v ⊔ principalBandToLp hs w := by
    intro v w; apply le_antisymm
    · have hv : v ≤ lpToPrincipalBand hs (principalBandToLp hs v ⊔
          principalBandToLp hs w) := by
        calc v = lpToPrincipalBand hs (principalBandToLp hs v) :=
              (leftInv_eq hs v).symm
          _ ≤ _ := monotone_lpToPrincipalBand hs le_sup_left
      have hw : w ≤ lpToPrincipalBand hs (principalBandToLp hs v ⊔
          principalBandToLp hs w) := by
        calc w = lpToPrincipalBand hs (principalBandToLp hs w) :=
              (leftInv_eq hs w).symm
          _ ≤ _ := monotone_lpToPrincipalBand hs le_sup_right
      calc principalBandToLp hs (v ⊔ w)
          ≤ principalBandToLp hs (lpToPrincipalBand hs
            (principalBandToLp hs v ⊔ principalBandToLp hs w)) :=
            monotone_principalBandToLp hs (sup_le hv hw)
        _ = _ := rightInv_eq hs _
    · exact sup_le (monotone_principalBandToLp hs le_sup_left)
        (monotone_principalBandToLp hs le_sup_right)
  have hmap_inf : ∀ v w : ↥(Band.principalBand s).toSubmodule,
      principalBandToLp hs (v ⊓ w) =
        principalBandToLp hs v ⊓ principalBandToLp hs w := by
    intro v w
    have lhs : principalBandToLp hs (v ⊓ w) =
        principalBandToLp hs v + principalBandToLp hs w -
          (principalBandToLp hs v ⊔ principalBandToLp hs w) := by
      conv_lhs => rw [eq_sub_of_add_eq (inf_add_sup v w), sub_eq_add_neg]
      rw [hmap_add, map_neg_eq, hmap_add, hmap_sup, sub_eq_add_neg]
    rw [lhs, ← eq_sub_of_add_eq (inf_add_sup _ _)]
  exact {
    toLinearIsometryEquiv := {
      toLinearEquiv := {
        toFun := principalBandToLp hs
        map_add' := hmap_add
        map_smul' := hmap_smul
        invFun := lpToPrincipalBand hs
        left_inv := leftInv_eq hs
        right_inv := rightInv_eq hs
      }
      norm_map' := norm_map_eq hs
    }
    map_sup' := hmap_sup
    map_inf' := hmap_inf
  }

/-! ### Atoms and Dirac deltas

In a vector lattice, an **atom** (`IsVLAtom`) is a strictly positive element
whose order interval `[0, a]` is one-dimensional: every `0 ≤ x ≤ a` is a
scalar multiple of `a`. For the Banach lattice `SignedMeasure α` with
measurable singletons, the atoms are precisely the strictly positive scalar
multiples of the Dirac measures `δ_x` at points `x ∈ K`. -/

section Atoms

variable [MeasurableSingletonClass α]

/-- The Dirac delta at a point, viewed as a finite signed measure. -/
noncomputable def dirac (x : α) : SignedMeasure α :=
  (Measure.dirac x).toSignedMeasure

omit [MeasurableSingletonClass α] in
/-- The Dirac delta evaluates to `1` on any measurable set containing the
point. -/
theorem dirac_apply_of_mem {x : α} {i : Set α} (hi : MeasurableSet i)
    (hx : x ∈ i) : dirac x i = 1 := by
  unfold dirac
  rw [Measure.toSignedMeasure_apply_measurable hi, measureReal_def,
      Measure.dirac_apply_of_mem hx, ENNReal.toReal_one]

omit [MeasurableSingletonClass α] in
/-- The Dirac delta evaluates to `0` on any measurable set not containing the
point. -/
theorem dirac_apply_of_notMem {x : α} {i : Set α} (hi : MeasurableSet i)
    (hx : x ∉ i) : dirac x i = 0 := by
  unfold dirac
  rw [Measure.toSignedMeasure_apply_measurable hi, measureReal_def,
      Measure.dirac_apply' x hi, Set.indicator_of_notMem hx, ENNReal.toReal_zero]

omit [MeasurableSingletonClass α] in
/-- The Dirac delta is non-negative as a signed measure. -/
theorem zero_le_dirac (x : α) : (0 : SignedMeasure α) ≤ dirac x :=
  Measure.zero_le_toSignedMeasure _

/-- The Dirac delta is non-zero. -/
theorem dirac_ne_zero (x : α) : dirac x ≠ 0 := by
  intro h
  have h₁ : dirac x {x} = 1 :=
    dirac_apply_of_mem (measurableSet_singleton x) (Set.mem_singleton x)
  rw [h, VectorMeasure.zero_apply] at h₁
  exact one_ne_zero h₁.symm

omit [MeasurableSingletonClass α] in
/-- The norm (total variation) of a Dirac delta is `1`. -/
theorem norm_dirac (x : α) : ‖dirac x‖ = 1 := by
  rw [norm_of_nonneg (zero_le_dirac x)]
  exact dirac_apply_of_mem MeasurableSet.univ (Set.mem_univ x)

/-- The Dirac measures at two distinct points are mutually singular. -/
private theorem mutuallySingular_dirac_dirac {x y : α} (h : x ≠ y) :
    Measure.dirac x ⟂ₘ Measure.dirac y := by
  refine ⟨{x}ᶜ, (measurableSet_singleton x).compl, ?_, ?_⟩
  · rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (by simp) _
  · rw [compl_compl, Measure.dirac_apply]
    exact Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr h.symm) _

/-- The positive part of `dirac x - dirac y` is `dirac x` when `x ≠ y`. -/
private theorem posPart_dirac_sub_dirac {x y : α} (h : x ≠ y) :
    (dirac x - dirac y).posPart = dirac x := by
  let j : JordanDecomposition α :=
    { posPart := Measure.dirac x
      negPart := Measure.dirac y
      mutuallySingular := mutuallySingular_dirac_dirac h }
  have hjd : (dirac x - dirac y).toJordanDecomposition = j :=
    toJordanDecomposition_eq rfl
  change (dirac x - dirac y).toJordanDecomposition.posPart.toSignedMeasure =
       (Measure.dirac x).toSignedMeasure
  rw [hjd]

/-- Two Dirac deltas at distinct points are vector-lattice disjoint. -/
theorem isVLDisjoint_dirac_of_ne {x y : α} (h : x ≠ y) :
    IsVLDisjoint (dirac x) (dirac y) := by
  refine isVLDisjoint_of_inf_eq_zero ?_
  change dirac x - (dirac x - dirac y).posPart = 0
  rw [posPart_dirac_sub_dirac h, sub_self]

omit [MeasurableSingletonClass α] in
/-- A non-negative signed measure dominated by `dirac x` vanishes outside `x`. -/
private theorem apply_eq_zero_of_notMem_of_le_dirac {x : α} {y : SignedMeasure α}
    (hy0 : 0 ≤ y) (hyd : y ≤ dirac x) {i : Set α} (hi : MeasurableSet i)
    (hx : x ∉ i) : y i = 0 := by
  have h1 : (0 : SignedMeasure α) i ≤ y i := hy0 _ hi
  rw [VectorMeasure.zero_apply] at h1
  have h2 : y i ≤ dirac x i := hyd _ hi
  rw [dirac_apply_of_notMem hi hx] at h2
  linarith

/-- A non-negative signed measure dominated by `dirac x` is determined on sets
containing `x` by its value on the singleton `{x}`. -/
private theorem apply_eq_singleton_of_mem_of_le_dirac {x : α} {y : SignedMeasure α}
    (hy0 : 0 ≤ y) (hyd : y ≤ dirac x) {i : Set α} (hi : MeasurableSet i)
    (hx : x ∈ i) : y i = y {x} := by
  have hx_set : MeasurableSet ({x} : Set α) := measurableSet_singleton x
  have h_subset : ({x} : Set α) ⊆ i := Set.singleton_subset_iff.mpr hx
  have h_split : y ({x} : Set α) + y (i \ {x}) = y i :=
    VectorMeasure.of_add_of_diff hx_set hi h_subset
  have h_diff_zero : y (i \ {x}) = 0 :=
    apply_eq_zero_of_notMem_of_le_dirac hy0 hyd (hi.diff hx_set) (by simp)
  rw [h_diff_zero, add_zero] at h_split
  exact h_split.symm

/-- The Dirac delta is itself an atom of `SignedMeasure α`. -/
theorem isVLAtom_dirac (x : α) : IsVLAtom (dirac x) := by
  refine ⟨lt_of_le_of_ne (zero_le_dirac x) (Ne.symm (dirac_ne_zero x)), ?_⟩
  intro y hy0 hyd
  refine ⟨y {x}, ?_⟩
  ext i hi
  rw [VectorMeasure.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ i
  · rw [dirac_apply_of_mem hi hx, mul_one]
    exact apply_eq_singleton_of_mem_of_le_dirac hy0 hyd hi hx
  · rw [dirac_apply_of_notMem hi hx, mul_zero]
    exact apply_eq_zero_of_notMem_of_le_dirac hy0 hyd hi hx

/-- A strictly positive scalar multiple of a Dirac delta is an atom of
`SignedMeasure α`. -/
theorem isVLAtom_smul_dirac {c : ℝ} (hc : 0 < c) (x : α) :
    IsVLAtom (c • dirac x) :=
  IsVLAtom.smul (isVLAtom_dirac x) hc

end Atoms
end SignedMeasure
end MeasureTheory
