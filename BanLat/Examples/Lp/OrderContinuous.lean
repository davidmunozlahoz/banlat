import BanLat.Examples.Lp.Basic
import BanLat.OrderContinuous.MeyerNieberg
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Order continuity of `Lₚ` spaces, `1 ≤ p < ∞`

We use the Meyer-Nieberg theorem to conclude that real-valued
`Lₚ`-spaces have an order continuous norm when `1 ≤ p < ∞`.
-/

open MeasureTheory Filter
open scoped NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0} [Fact (1 ≤ p)]

private instance instFactOneLEENNReal : Fact (1 ≤ (p : ENNReal)) :=
  ⟨by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)⟩

omit [Fact (1 ≤ p)] in
/-- A pairwise disjoint sequence in `Lₚ` converges pointwise to zero almost
everywhere. -/
private lemma ae_tendsto_zero_of_pairwise_isVLDisjoint
    {u : ℕ → Lp ℝ (p : ENNReal) μ}
    (hdisj : Pairwise fun i j => IsVLDisjoint (u i) (u j)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds 0) := by
  have hpair : ∀ i j, i ≠ j → ∀ᵐ x ∂μ, |u i x| ⊓ |u j x| = 0 := by
    intro i j hij
    have heq : |u i| ⊓ |u j| = 0 := hdisj hij
    filter_upwards [Lp.coeFn_inf |u i| |u j|, Lp.coeFn_abs (u i),
      Lp.coeFn_abs (u j), Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hinf hi hj hz
    rw [heq] at hinf
    rw [hz] at hinf
    change (0 : ℝ) = min ((|u i| : Lp ℝ (p : ENNReal) μ) x)
      ((|u j| : Lp ℝ (p : ENNReal) μ) x) at hinf
    rw [hi, hj] at hinf
    exact hinf.symm
  have hpairAll : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → |u i x| ⊓ |u j x| = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hne => (hne hij).elim
    · exact (hpair i j hij).mono fun _ hx _ => hx
  filter_upwards [hpairAll] with x hx
  by_cases hnonzero : ∃ N, u N x ≠ 0
  · obtain ⟨N, hN⟩ := hnonzero
    have heventually : ∀ᶠ n in atTop, u n x = 0 := by
      refine eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
      have hne : N ≠ n := by omega
      have hmin := hx N n hne
      have hor : |u N x| = 0 ∨ |u n x| = 0 := by
        rcases le_total |u N x| |u n x| with hle | hle
        · left
          rwa [min_eq_left hle] at hmin
        · right
          rwa [min_eq_right hle] at hmin
      exact abs_eq_zero.mp (hor.resolve_left (abs_ne_zero.mpr hN))
    exact (tendsto_congr' heventually).mpr tendsto_const_nhds
  · have heventually : ∀ᶠ n in atTop, u n x = 0 :=
      Eventually.of_forall fun n => not_not.mp fun hn => hnonzero ⟨n, hn⟩
    exact (tendsto_congr' heventually).mpr tendsto_const_nhds

/-- An almost-everywhere convergent sequence in `Lₚ` dominated in lattice
order by a common `Lₚ` function converges in `Lₚ`. -/
private lemma tendsto_zero_of_ae_tendsto_of_abs_le
    {u : ℕ → Lp ℝ (p : ENNReal) μ} {g : Lp ℝ (p : ENNReal) μ}
    (hu : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds 0))
    (hug : ∀ n, |u n| ≤ g) :
    Tendsto u atTop (nhds 0) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one Fact.out
  have hp_real_pos : 0 < (p : ℝ) := NNReal.coe_pos.mpr hp_pos
  have hp_ne_zero : (p : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hp_pos).ne'
  have hp_ne_top : (p : ENNReal) ≠ ⊤ := by simp
  have hpreal : (p : ENNReal).toReal = (p : ℝ) := by simp
  have hnorm : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ₑ ≤ ‖g x‖ₑ := by
    intro n
    have hle := (Lp.coeFn_le |u n| g).2 (hug n)
    filter_upwards [hle, Lp.coeFn_abs (u n)] with x hx habs
    rw [habs] at hx
    rw [Real.enorm_eq_ofReal_abs,
      Real.enorm_eq_ofReal ((abs_nonneg _).trans hx)]
    exact ENNReal.ofReal_le_ofReal hx
  have h_integral :
      Tendsto (fun n ↦ ∫⁻ x, ‖u n x‖ₑ ^ (p : ℝ) ∂μ) atTop (nhds 0) := by
    have hmeas : ∀ n, AEMeasurable (fun x ↦ ‖u n x‖ₑ ^ (p : ℝ)) μ := fun n =>
      (Lp.aestronglyMeasurable (u n)).enorm.pow_const (p : ℝ)
    have hbound : ∀ n, (fun x ↦ ‖u n x‖ₑ ^ (p : ℝ)) ≤ᵐ[μ]
        fun x ↦ ‖g x‖ₑ ^ (p : ℝ) := fun n =>
      (hnorm n).mono fun _ hx => ENNReal.rpow_le_rpow hx hp_real_pos.le
    have hfin : ∫⁻ x, ‖g x‖ₑ ^ (p : ℝ) ∂μ ≠ ⊤ := by
      have hfin' : ∫⁻ x, ‖g x‖ₑ ^ (p : ENNReal).toReal ∂μ ≠ ⊤ := by
        exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          hp_ne_zero hp_ne_top
          (Lp.eLpNorm_ne_top g).lt_top).ne
      convert hfin' using 1
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ‖u n x‖ₑ ^ (p : ℝ)) atTop (nhds 0) := by
      filter_upwards [hu] with x hx
      have henorm : Tendsto (fun n ↦ ‖u n x‖ₑ) atTop (nhds 0) := by
        simpa using (continuous_enorm.tendsto 0).comp hx
      rw [← ENNReal.zero_rpow_of_pos hp_real_pos]
      exact ((@ENNReal.continuous_rpow_const (p : ℝ)).tendsto 0).comp henorm
    simpa using
      tendsto_lintegral_of_dominated_convergence'
        (fun x ↦ ‖g x‖ₑ ^ (p : ℝ)) hmeas hbound hfin hlim
  have heLp : Tendsto (fun n ↦ eLpNorm (u n) (p : ENNReal) μ)
      atTop (nhds 0) := by
    have hroot : Tendsto
        (fun n ↦ (∫⁻ x, ‖u n x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)))
        atTop (nhds 0) := by
      rw [← ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp_real_pos)]
      exact ((@ENNReal.continuous_rpow_const (1 / (p : ℝ))).tendsto 0).comp h_integral
    simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal
      hp_ne_zero hp_ne_top, hpreal] using hroot
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine heLp.congr' (Eventually.of_forall fun n => ?_)
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hx
  rw [Pi.sub_apply, hx]
  simp

/-- Every order-bounded pairwise lattice-disjoint sequence in `Lₚ` converges
to zero in `Lₚ`. -/
private lemma tendsto_zero_of_pairwise_isVLDisjoint_of_bddAbove
    {u : ℕ → Lp ℝ (p : ENNReal) μ}
    (hdisj : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Tendsto u atTop (nhds 0) := by
  obtain ⟨g, hg⟩ := hbd
  apply tendsto_zero_of_ae_tendsto_of_abs_le (g := g)
    (ae_tendsto_zero_of_pairwise_isVLDisjoint hdisj)
  intro n
  exact hg ⟨n, rfl⟩

/-- For `1 ≤ p < ∞`, the norm on `Lp ℝ (p : ENNReal) μ` is order continuous. -/
noncomputable instance instIsOrderContinuousNormLp :
    IsOrderContinuousNorm (Lp ℝ (p : ENNReal) μ) := by
  apply BanachLattice.isOrderContinuousNorm_of_disjoint_tendsto_zero
  intro u hdisj hbd
  exact tendsto_zero_of_pairwise_isVLDisjoint_of_bddAbove hdisj hbd
