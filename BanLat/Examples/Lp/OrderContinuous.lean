/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Lp.Convergence
import BanLat.OrderContinuous.MeyerNieberg

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
  let : Fact (0 < (p : ENNReal)) :=
    ⟨lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ (p : ENNReal))⟩
  have hnorm : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ g x := by
    intro n
    have hle := (Lp.coeFn_le |u n| g).2 (hug n)
    filter_upwards [hle, Lp.coeFn_abs (u n)] with x hx habs
    simpa only [Real.norm_eq_abs, habs] using hx
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ u n x) atTop
        (nhds ((0 : Lp ℝ (p : ENNReal) μ) x)) := by
    filter_upwards [hu, Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hx hz
    simpa only [hz, Pi.zero_apply] using hx
  have hq := Lp.tendsto_quasiLp_of_dominated_convergence
    (f := u) (f_lim := 0) ENNReal.coe_ne_top g hnorm hlim
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' u 0).mpr
    ((Lp.tendsto_quasiLp_iff_tendsto_eLpNorm u 0).mp hq)

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
