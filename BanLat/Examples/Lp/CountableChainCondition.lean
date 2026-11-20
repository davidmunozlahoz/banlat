/-
Authors: Pedro Tradacete
-/

import BanLat.CountableSupProperty
import BanLat.Examples.Lp.Basic

/-!
# The countable chain condition in `Lᵖ`

On a sigma-finite measure space, a family of nonzero pairwise disjoint real
`Lᵖ` functions is countable. Their supports have positive measure and are
pairwise disjoint up to null sets.
-/

open MeasureTheory

namespace MeasureTheory.Lp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ENNReal}

private lemma support_measure_pos {f : Lp ℝ p μ} (hf : f ≠ 0) :
    0 < μ (Function.support (f : Ω → ℝ)) := by
  rw [pos_iff_ne_zero]
  intro hzero
  apply hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun x hx ↦ by
    simpa only [Function.mem_support, not_ne_iff, Pi.zero_apply] using hx

/-- Disjoint elements of real `Lp` have almost-everywhere disjoint supports. -/
lemma support_aeDisjoint {f g : Lp ℝ p μ} (hfg : IsVLDisjoint f g) :
    AEDisjoint μ (Function.support (f : Ω → ℝ)) (Function.support (g : Ω → ℝ)) := by
  change μ (Function.support (f : Ω → ℝ) ∩ Function.support (g : Ω → ℝ)) = 0
  rw [measure_eq_zero_iff_ae_notMem]
  have hzero := Lp.eq_zero_iff_ae_eq_zero.mp hfg
  filter_upwards [Lp.coeFn_inf |f| |g|, Lp.coeFn_abs f, Lp.coeFn_abs g, hzero]
    with x hinf hf hg hz
  rintro ⟨hfx, hgx⟩
  have hz' := hinf.symm.trans hz
  simp only [Pi.inf_apply, hf, hg, Pi.zero_apply] at hz'
  exact (lt_min (abs_pos.mpr hfx) (abs_pos.mpr hgx)).ne' hz'

/-- Real `Lᵖ` over a sigma-finite measure has the countable chain condition. -/
theorem hasCountableChainCondition [SigmaFinite μ] :
    HasCountableChainCondition (Lp ℝ p μ) := by
  intro D hD
  let A : D → Set Ω := fun f ↦ Function.support (f.val : Ω → ℝ)
  have hAmeas (f : D) : NullMeasurableSet (A f) μ :=
    ((Lp.stronglyMeasurable f.val).measurable
      (measurableSet_singleton (0 : ℝ))).compl.nullMeasurableSet
  have hAdisj : Pairwise (Function.onFun (AEDisjoint μ) A) :=
    fun f g hfg ↦ support_aeDisjoint (hD.2 f.property g.property
      (fun h ↦ hfg (Subtype.ext h)))
  have hpos (f : D) : 0 < μ (A f) :=
    support_measure_pos (fun hf ↦ hD.1 (hf ▸ f.property))
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion₀ hAmeas hAdisj
  have hall : {f : D | 0 < μ (A f)} = Set.univ := Set.eq_univ_of_forall hpos
  rw [hall] at hc
  exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hc)

end MeasureTheory.Lp
