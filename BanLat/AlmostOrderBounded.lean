/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Normed
import BanLat.Tactic.LLexpr

/-!
# Almost order bounded sets


A subset `A` of a normed vector lattice `X` is almost order bounded if, for every
`ε > 0`, there exists `u ≥ 0` such that `A ⊆ [-u, u]_o + ε B_X`, where `B_X` is
the closed unit ball of `X`. Equivalently, `u` can be chosen so that
`‖(|x| - u)⁺‖ ≤ ε` for every `x ∈ A`.
-/

open Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]

/-- A set `F` is almost order bounded if for every `ε > 0` there exists `u ≥ 0`
such that `‖(|f| - u)⁺‖ ≤ ε` for all `f ∈ F`. -/
def AlmostOrderBounded (F : Set E) : Prop :=
  ∀ ε > 0, ∃ u : E, 0 ≤ u ∧ ∀ f ∈ F, ‖(|f| - u)⁺‖ ≤ ε

/-- For any element `f` of a normed vector lattice and any `u ≥ 0`,
there exists `g ∈ [-u, u]_o` such that `‖f - g‖ = ‖(|f| - u)⁺‖`.
One such element is `(f ⊓ u) ⊔ (-u)`. -/
private lemma exists_interval_approx (f u : E) (hu : 0 ≤ u) :
    ∃ g ∈ [-u, u]_o, ‖f - g‖ = ‖(|f| - u)⁺‖ := by
  refine ⟨(f ⊓ u) ⊔ (-u), ⟨le_sup_right, sup_le inf_le_right (by llarith)⟩, ?_⟩
  rw [← norm_abs_eq_norm]
  congr 1
  llarith

/-- A set `F` in a normed vector lattice is almost order bounded if and only if,
for every `ε > 0`, there exists `u ≥ 0` such that every `f ∈ F` can be written
as `f = g + h` with `g ∈ [-u, u]_o` and `‖h‖ ≤ ε`. -/
theorem almostOrderBounded_iff_subset_add_closedBall {F : Set E} :
    AlmostOrderBounded F ↔ ∀ ε > 0, ∃ u : E, 0 ≤ u ∧
      F ⊆ [-u, u]_o + Metric.closedBall 0 ε := by
  constructor
  · intro h ε hε
    obtain ⟨u, hu, htail⟩ := h ε hε
    refine ⟨u, hu, fun f hf ↦ ?_⟩
    obtain ⟨g, hg, hnorm⟩ := exists_interval_approx f u hu
    exact ⟨g, hg, f - g, mem_closedBall_zero_iff.mpr
      (hnorm.trans_le (htail f hf)), by abel_nf⟩
  · intro h ε hε
    obtain ⟨u, hu, hF⟩ := h ε hε
    refine ⟨u, hu, fun f hf ↦ ?_⟩
    obtain ⟨g, hg, z, hz, rfl⟩ := hF hf
    apply le_trans (norm_le_norm_of_abs_le_abs (b := z) ?_)
      (mem_closedBall_zero_iff.mp hz)
    rw [abs_of_nonneg (posPart_nonneg _), posPart_def]
    apply sup_le _ (abs_nonneg z)
    apply sub_le_iff_le_add.mpr
    calc
      |g + z| ≤ |g| + |z| := abs_add_le g z
      _ ≤ u + |z| := add_le_add (sup_le hg.2 (neg_le.mpr hg.1)) le_rfl
      _ = |z| + u := add_comm _ _
