/-
Authors: Pedro Tradacete
-/

import BanLat.CountableSupProperty

/-!
# Weak order units and the countable chain condition

A Banach lattice with the countable chain condition admits a weak order unit.
A countable maximal disjoint family supplies positive vectors whose suitably
scaled sum is disjoint only from zero.
-/

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

private lemma exists_summable_pos_scaling {D : Set X} (hD : D.Countable)
    (hpos : ∀ x ∈ D, 0 < x) :
    ∃ c : D → ℝ, (∀ x, 0 < c x) ∧ Summable (fun x ↦ c x • (x : X)) := by
  obtain ⟨δ, hδ, s, hs, _⟩ := hD.exists_pos_hasSum_le zero_lt_one
  let c : D → ℝ := fun x ↦ δ x / ‖(x : X)‖
  have hx (x : D) : 0 < ‖(x : X)‖ := norm_pos_iff.mpr (hpos x x.property).ne'
  have hc (x : D) : 0 < c x := div_pos (hδ x) (hx x)
  refine ⟨c, hc, ?_⟩
  apply Summable.of_norm
  have hn (x : D) : ‖c x • (x : X)‖ = δ x := by
    rw [norm_smul, Real.norm_of_nonneg (hc x).le]
    exact div_mul_cancel₀ _ (hx x).ne'
  exact hs.summable.congr (fun x ↦ (hn x).symm)

/-- A Banach lattice with the countable chain condition has a weak order unit. -/
theorem exists_weakOrderUnit_of_hasCountableChainCondition
    (hX : HasCountableChainCondition X) : ∃ e : X, WeakOrderUnit e := by
  obtain ⟨D, hD, hpos⟩ := exists_isMaximalDisjoint_pos X
  obtain ⟨c, hc, hsum⟩ := exists_summable_pos_scaling (hX D hD.1) hpos
  have hn (x : D) : 0 ≤ c x • (x : X) := smul_nonneg (hc x).le (hpos x x.property).le
  refine ⟨∑' x : D, c x • (x : X), tsum_nonneg hn, ?_⟩
  intro x hx
  apply (isMaximalDisjoint_iff_forall_eq_zero hpos hD.1).mp hD x
  intro a ha
  have hle : |c ⟨a, ha⟩ • a| ≤ |∑' x : D, c x • (x : X)| := by
    rw [abs_of_nonneg (hn ⟨a, ha⟩), abs_of_nonneg (tsum_nonneg hn)]
    exact hsum.le_tsum ⟨a, ha⟩ (fun b _ ↦ hn b)
  have hd := (hx.mono_right hle).smul_right (c ⟨a, ha⟩)⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ (hc ⟨a, ha⟩).ne', one_smul] using hd

end
