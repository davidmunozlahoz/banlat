/-
Author: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Lp.WeakUnit
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Change of densities in `L^p` spaces

For `1 ≤ p < ∞`, let `e ∈ L^p(μ)` be a weak order unit with `‖e‖ = 1` and define
`ν` by `dν = |e|^p dμ`. Then `ν` is a probability measure and `f ↦ |e|f` is a lattice
isometry from `L^p(ν)` onto `L^p(μ)`.

Thus:
* If `μ` is sigma-finite and `L^p(μ) ≠ {0}`, then `L^p(μ)` is lattice isometric to
  `L^p(ν)` for some probability measure `ν`.
* If `L^p(μ)` is separable and `L^p(μ) ≠ {0}`, then `L^p(μ)` is lattice isometric to
  `L^p(ν)` for some probability measure `ν`.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.Lp

universe u

variable {α : Type u} [MeasurableSpace α] {p : ℝ≥0}

/- If `h : α → [0, ∞)`, define the measure `ν` by `dν = h^p dμ`. -/
private noncomputable def densityMeasure (μ : Measure α) (h : α → ℝ≥0) : Measure α :=
  μ.withDensity fun x ↦ (h x : ℝ≥0∞) ^ (p : ℝ)

private lemma measurable_density {h : α → ℝ≥0} (hh : Measurable h) :
    Measurable fun x ↦ (h x : ℝ≥0∞) ^ (p : ℝ) := by
  exact hh.coe_nnreal_ennreal.pow_const _

variable [Fact (1 ≤ p)]

/- If `dν = h^p dμ` and `f ∈ L^p(ν)`, then `‖hf‖_{Lᵖ(μ)} = ‖f‖_{Lᵖ(ν)}`. -/
private lemma eLpNorm_mul_density
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    eLpNorm (fun x ↦ (h x : ℝ) * f x) (p : ENNReal) μ =
      eLpNorm f (p : ENNReal) (densityMeasure (p := p) μ h) := by
  have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
  have hhf : AEStronglyMeasurable (fun x ↦ (h x : ℝ) * f x) μ :=
    (hh.coe_nnreal_real.mul (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable
  rw [eLpNorm_nnreal_eq_lintegral hp hhf,
    eLpNorm_nnreal_eq_lintegral hp (Lp.aestronglyMeasurable f)]
  congr 1
  change (∫⁻ x, ‖(h x : ℝ) * f x‖ₑ ^ (p : ℝ) ∂μ) =
    ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ.withDensity (fun x ↦ (h x : ℝ≥0∞) ^ (p : ℝ))
  have hf_meas : Measurable fun x ↦ ‖f x‖ₑ ^ (p : ℝ) :=
    (Lp.stronglyMeasurable f).measurable.enorm.pow_const _
  rw [lintegral_withDensity_eq_lintegral_mul μ (measurable_density hh) hf_meas]
  apply lintegral_congr
  intro x
  simp [ENNReal.mul_rpow_of_nonneg]

/- If `dν = h^p dμ` and `f ∈ L^p(ν)`, then `h f ∈ L^p(μ)`. -/
private lemma memLp_mul_density
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    MemLp (fun x ↦ (h x : ℝ) * f x) (p : ENNReal) μ := by
  rw [memLp_iff, eLpNorm_mul_density μ hh f]
  exact Lp.memLp f

/- If `f = g` a.e. with respect to `h^p μ`, then `h f = h g` a.e. with respect to `μ`. -/
private lemma ae_mul_eq_mul_of_ae_eq_density
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h) {f g : α → ℝ}
    (hfg : f =ᵐ[densityMeasure (p := p) μ h] g) :
    (fun x ↦ (h x : ℝ) * f x) =ᵐ[μ] fun x ↦ (h x : ℝ) * g x := by
  change f =ᵐ[μ.withDensity (fun x ↦ (h x : ℝ≥0∞) ^ (p : ℝ))] g at hfg
  have hfg' := (ae_withDensity_iff (measurable_density hh)).mp hfg
  filter_upwards [hfg'] with x hx
  by_cases hzero : h x = 0
  · simp [hzero]
  · rw [hx (by
      simpa [ENNReal.rpow_eq_zero_iff, lt_of_lt_of_le zero_lt_one Fact.out]
        using hzero)]

/- If `dν = h^p dμ`, define `densityMul : L^p(ν) → L^p(μ)` by `densityMul f = h f`. -/
private noncomputable def densityMul
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    Lp ℝ (p : ENNReal) μ :=
  (memLp_mul_density μ hh f).toLp fun x ↦ (h x : ℝ) * f x

/- The element `densityMul f` is represented a.e. by the function `h f`. -/
private lemma densityMul_coeFn
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    ⇑(densityMul μ hh f) =ᵐ[μ] fun x ↦ (h x : ℝ) * f x :=
  (memLp_mul_density μ hh f).coeFn_toLp

/- `densityMul` preserves addition. -/
private lemma densityMul_add
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f g : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    densityMul μ hh (f + g) = densityMul μ hh f + densityMul μ hh g := by
  apply Lp.ext
  have hfg := ae_mul_eq_mul_of_ae_eq_density μ hh (Lp.coeFn_add f g)
  filter_upwards [densityMul_coeFn μ hh (f + g), hfg,
    Lp.coeFn_add (densityMul μ hh f) (densityMul μ hh g),
    densityMul_coeFn μ hh f, densityMul_coeFn μ hh g] with x hL hfgx hR hf hg
  rw [hL, hR]
  change (h x : ℝ) * (f + g) x = densityMul μ hh f x + densityMul μ hh g x
  rw [hf, hg, ← mul_add]
  simpa only [Pi.add_apply] using hfgx

/- `densityMul` preserves scalar multiplication. -/
private lemma densityMul_smul
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h) (c : ℝ)
    (f : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    densityMul μ hh (c • f) = c • densityMul μ hh f := by
  apply Lp.ext
  have hcf := ae_mul_eq_mul_of_ae_eq_density μ hh (Lp.coeFn_smul c f)
  filter_upwards [densityMul_coeFn μ hh (c • f), hcf,
    Lp.coeFn_smul c (densityMul μ hh f), densityMul_coeFn μ hh f]
    with x hL hcfx hR hf
  rw [hL, hR]
  change (h x : ℝ) * (c • f) x = c * densityMul μ hh f x
  calc
    (h x : ℝ) * (c • f) x = (h x : ℝ) * (c * f x) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hcfx
    _ = c * ((h x : ℝ) * f x) := by ring
    _ = c * densityMul μ hh f x := congrArg (c * ·) hf.symm

/- `densityMul` is an isometry. -/
private lemma norm_densityMul
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    ‖densityMul μ hh f‖ = ‖f‖ := by
  rw [densityMul, Lp.norm_toLp, eLpNorm_mul_density μ hh f, Lp.norm_def]

/- `densityMul` preserves suprema. -/
private lemma densityMul_sup
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f g : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    densityMul μ hh (f ⊔ g) = densityMul μ hh f ⊔ densityMul μ hh g := by
  apply Lp.ext
  have hfg := ae_mul_eq_mul_of_ae_eq_density μ hh (Lp.coeFn_sup f g)
  filter_upwards [densityMul_coeFn μ hh (f ⊔ g), hfg,
    Lp.coeFn_sup (densityMul μ hh f) (densityMul μ hh g),
    densityMul_coeFn μ hh f, densityMul_coeFn μ hh g] with x hL hfgx hR hf hg
  rw [hL, hR]
  change (h x : ℝ) * (f ⊔ g) x =
    max (densityMul μ hh f x) (densityMul μ hh g x)
  calc
    (h x : ℝ) * (f ⊔ g) x = (h x : ℝ) * max (f x) (g x) := by
      simpa only [Pi.sup_apply] using hfgx
    _ = max ((h x : ℝ) * f x) ((h x : ℝ) * g x) :=
      mul_max_of_nonneg _ _ (NNReal.coe_nonneg _)
    _ = max (densityMul μ hh f x) (densityMul μ hh g x) :=
      congrArg₂ max hf.symm hg.symm

/- `densityMul` preserves infima. -/
private lemma densityMul_inf
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h)
    (f g : Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h)) :
    densityMul μ hh (f ⊓ g) = densityMul μ hh f ⊓ densityMul μ hh g := by
  apply Lp.ext
  have hfg := ae_mul_eq_mul_of_ae_eq_density μ hh (Lp.coeFn_inf f g)
  filter_upwards [densityMul_coeFn μ hh (f ⊓ g), hfg,
    Lp.coeFn_inf (densityMul μ hh f) (densityMul μ hh g),
    densityMul_coeFn μ hh f, densityMul_coeFn μ hh g] with x hL hfgx hR hf hg
  rw [hL, hR]
  change (h x : ℝ) * (f ⊓ g) x =
    min (densityMul μ hh f x) (densityMul μ hh g x)
  calc
    (h x : ℝ) * (f ⊓ g) x = (h x : ℝ) * min (f x) (g x) := by
      simpa only [Pi.inf_apply] using hfgx
    _ = min ((h x : ℝ) * f x) ((h x : ℝ) * g x) :=
      mul_min_of_nonneg _ _ (NNReal.coe_nonneg _)
    _ = min (densityMul μ hh f x) (densityMul μ hh g x) :=
      congrArg₂ min hf.symm hg.symm

/- If `dν = h^p dμ`, `densityMul : L^p(ν) → L^p(μ)` defines a linear isometry. -/
private noncomputable def densityMulLI
    (μ : Measure α) {h : α → ℝ≥0} (hh : Measurable h) :
    Lp ℝ (p : ENNReal) (densityMeasure (p := p) μ h) →ₗᵢ[ℝ]
      Lp ℝ (p : ENNReal) μ where
  toFun := densityMul μ hh
  map_add' := densityMul_add μ hh
  map_smul' := densityMul_smul μ hh
  norm_map' := norm_densityMul μ hh

omit [Fact (1 ≤ p)] in
/- For every `[e] ∈ L^p(μ)`, the function `x ↦ |e(x)|` is measurable. -/
private lemma measurable_nnnorm_coeFn (μ : Measure α) (e : Lp ℝ (p : ENNReal) μ) :
    Measurable fun x ↦ ‖e x‖₊ := by
  exact (Lp.stronglyMeasurable e).measurable.nnnorm

/- If `e` is a quasi-interior point of `L^p(μ)` and the measure `ν` defined by
`dν = |e|^p dμ` is finite, then `densityMul : L^p(ν) → L^p(μ)` is surjective. -/
private lemma densityMulLI_surjective_of_quasiInteriorPoint
    (μ : Measure α) (e : Lp ℝ (p : ENNReal) μ) (he : QuasiInteriorPoint e)
    [IsFiniteMeasure (densityMeasure (p := p) μ (fun x ↦ ‖e x‖₊))] :
    Function.Surjective
      (densityMulLI (p := p) μ (measurable_nnnorm_coeFn μ e)) := by
  let T := densityMulLI (p := p) μ (measurable_nnnorm_coeFn μ e)
  have hclosed : IsClosed (Set.range T) := T.isometry.isClosedEmbedding.isClosed_range
  have hprincipal : (OrderIdeal.principal e : Set (Lp ℝ (p : ENNReal) μ)) ⊆
      Set.range T := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hx
    let q : α → ℝ := fun a ↦ x a / (‖e a‖₊ : ℝ)
    have hq_meas :
        AEStronglyMeasurable q (densityMeasure (p := p) μ (fun x ↦ ‖e x‖₊)) :=
      ((Lp.stronglyMeasurable x).measurable.div
        (measurable_nnnorm_coeFn μ e).coe_nnreal_real).aestronglyMeasurable
    have hxc' : |x| ≤ c • e := by simpa [abs_of_nonneg he.1] using hxc
    have hxe := (Lp.coeFn_le |x| (c • e)).mpr hxc'
    have he_nonneg := (Lp.coeFn_nonneg e).mpr he.1
    have hq_boundμ : ∀ᵐ a ∂μ, ‖q a‖ ≤ c := by
      filter_upwards [hxe, Lp.coeFn_abs x, Lp.coeFn_smul c e, he_nonneg]
        with a hle habs hsmul hea
      rw [habs, hsmul] at hle
      change |x a| ≤ c * e a at hle
      change |x a / (‖e a‖₊ : ℝ)| ≤ c
      rw [abs_div, abs_of_nonneg (NNReal.coe_nonneg _)]
      by_cases ha : e a = 0
      · simpa [ha] using hc
      · change |x a| / ‖e a‖ ≤ c
        rw [div_le_iff₀ (norm_pos_iff.mpr ha)]
        simpa [Real.norm_eq_abs, abs_of_nonneg hea] using hle
    have hq_bound : ∀ᵐ a ∂densityMeasure (p := p) μ (fun x ↦ ‖e x‖₊), ‖q a‖ ≤ c :=
      (withDensity_absolutelyContinuous μ
        (fun x ↦ (‖e x‖₊ : ℝ≥0∞) ^ (p : ℝ))).ae_le
        hq_boundμ
    have hq_mem :
        MemLp q (p : ENNReal) (densityMeasure (p := p) μ (fun x ↦ ‖e x‖₊)) :=
      MemLp.of_bound hq_meas c hq_bound
    let qLp := hq_mem.toLp q
    refine ⟨qLp, ?_⟩
    change densityMul μ (measurable_nnnorm_coeFn μ e) qLp = x
    apply Lp.ext
    have hq_coe := ae_mul_eq_mul_of_ae_eq_density μ (measurable_nnnorm_coeFn μ e)
      hq_mem.coeFn_toLp
    have hmul : (fun a ↦ (‖e a‖₊ : ℝ) * q a) =ᵐ[μ] x := by
      filter_upwards [hxe, Lp.coeFn_abs x, Lp.coeFn_smul c e] with a hle habs hsmul
      rw [habs, hsmul] at hle
      change |x a| ≤ c * e a at hle
      change (‖e a‖₊ : ℝ) * (x a / (‖e a‖₊ : ℝ)) = x a
      by_cases ha : e a = 0
      · have hxa : x a = 0 := by
          apply abs_eq_zero.mp
          exact le_antisymm (by simpa [ha] using hle) (abs_nonneg _)
        simp [ha, hxa]
      · have hden : (‖e a‖₊ : ℝ) ≠ 0 := by simpa using ha
        rw [mul_comm, div_mul_cancel₀ _ hden]
    filter_upwards [densityMul_coeFn μ (measurable_nnnorm_coeFn μ e) qLp,
      hq_coe, hmul] with a hT hq hq_eq
    rw [hT, hq, hq_eq]
  have hrange_dense : Dense (Set.range T) := Dense.mono hprincipal he.2
  intro x
  have hx : x ∈ closure (Set.range T) := hrange_dense.closure_eq ▸ Set.mem_univ x
  rwa [hclosed.closure_eq] at hx

/- If `‖e‖_{L^p(μ)} = 1` and `dν = |e|^p dμ`, then `ν` is a probability measure. -/
private lemma isProbabilityMeasure_densityMeasure
    (μ : Measure α) (e : Lp ℝ (p : ENNReal) μ) (he : ‖e‖ = 1) :
    IsProbabilityMeasure (densityMeasure (p := p) μ (fun x ↦ ‖e x‖₊)) := by
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp only [← enorm_eq_nnnorm]
  rw [← eLpNorm_nnreal_pow_eq_lintegral
    (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne' (Lp.aestronglyMeasurable e)]
  rw [← Lp.enorm_def]
  have hnn : ‖e‖₊ = 1 := NNReal.eq he
  rw [enorm_eq_nnnorm, hnn]
  simp

/-- If `e ∈ L^p(μ)` is a normalized weak order unit, then there is a probability
measure `ν` such that `L^p(μ)` and `L^p(ν)` are lattice isometric. -/
theorem exists_banachLatEquiv_isProbabilityMeasure_of_weakOrderUnit
    (μ : Measure α) {e : Lp ℝ (p : ENNReal) μ} (he : WeakOrderUnit e)
    (he_norm : ‖e‖ = 1) :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧
      Nonempty
        (BanachLatEquiv
          (Lp ℝ (p : ENNReal) μ)
          (Lp ℝ (p : ENNReal) ν)) := by
  have he' : QuasiInteriorPoint e := quasiInteriorPoint_iff_weakOrderUnit.mpr he
  let ν := densityMeasure (p := p) μ (fun x ↦ ‖e x‖₊)
  let : IsProbabilityMeasure ν :=
    isProbabilityMeasure_densityMeasure μ e he_norm
  let T := densityMulLI (p := p) μ (measurable_nnnorm_coeFn μ e)
  have hT : Function.Surjective T :=
    densityMulLI_surjective_of_quasiInteriorPoint μ e he'
  refine ⟨ν, inferInstance, ?_⟩
  refine ⟨BanachLatEquiv.symm ?_⟩
  refine
    { toLinearIsometryEquiv := LinearIsometryEquiv.ofSurjective T hT
      map_sup' := densityMul_sup μ (measurable_nnnorm_coeFn μ e)
      map_inf' := densityMul_inf μ (measurable_nnnorm_coeFn μ e) }

/-- If `μ` is `σ`-finite and `L^p(μ) ≠ {0}`, then there is a probability measure `ν`
such that `L^p(μ)` and `L^p(ν)` are lattice isometric. -/
theorem exists_banachLatEquiv_isProbabilityMeasure_of_sigmaFinite
    (μ : Measure α) [SigmaFinite μ] [Nontrivial (Lp ℝ (p : ENNReal) μ)] :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧
      Nonempty
        (BanachLatEquiv
          (Lp ℝ (p : ENNReal) μ)
          (Lp ℝ (p : ENNReal) ν)) := by
  obtain ⟨e, he, he_norm⟩ := exists_weakOrderUnit_norm_one_of_sigmaFinite (p := p) μ
  exact exists_banachLatEquiv_isProbabilityMeasure_of_weakOrderUnit μ he he_norm

/-- If `L^p(μ)` is separable and `L^p(μ) ≠ {0}`, then there is a probability measure
`ν` such that `L^p(μ)` and `L^p(ν)` are lattice isometric. -/
theorem exists_banachLatEquiv_isProbabilityMeasure_of_separable
    (μ : Measure α)
    [TopologicalSpace.SeparableSpace (Lp ℝ (p : ENNReal) μ)]
    [Nontrivial (Lp ℝ (p : ENNReal) μ)] :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧
      Nonempty
        (BanachLatEquiv
          (Lp ℝ (p : ENNReal) μ)
          (Lp ℝ (p : ENNReal) ν)) := by
  obtain ⟨e, he, he_norm⟩ := exists_weakOrderUnit_norm_one_of_separable (p := p) μ
  exact exists_banachLatEquiv_isProbabilityMeasure_of_weakOrderUnit μ he he_norm

end MeasureTheory.Lp
