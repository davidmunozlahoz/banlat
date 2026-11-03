/-
Authors: Pedro Tradacete
-/

import BanLat.L1repr.Basic
import BanLat.Quotient

/-!
# `L¹` models of positive functionals

A positive functional `h` induces the lattice seminorm `x ↦ h |x|`. Quotienting
by its null ideal makes the induced functional strictly positive. Its existing
`L¹` representation allows to map the original lattice as a dense sublattice of the `L¹` space.
This map need not be injective when the original functional has a nontrivial null ideal.
-/

noncomputable section

open MeasureTheory

universe u

variable {X : Type u} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

private def positiveNullIdeal (h : X →ₗ[ℝ] ℝ) (hh : Positive h) : OrderIdeal X :=
  (OrderBoundedHom.ofPositive h hh).null

private lemma mem_positiveNullIdeal (h : X →ₗ[ℝ] ℝ) (hh : Positive h) (x : X) :
    x ∈ positiveNullIdeal h hh ↔ h |x| = 0 := by
  rw [positiveNullIdeal, OrderBoundedHom.mem_null]
  have hpos : 0 ≤ OrderBoundedHom.ofPositive h hh :=
    OrderBoundedHom.le_iff.mpr (fun y hy ↦ hh y hy)
  rw [abs_of_nonneg hpos]
  rfl

private lemma positiveNullIdeal_le_ker (h : X →ₗ[ℝ] ℝ) (hh : Positive h) :
    (positiveNullIdeal h hh).toSubmodule ≤ h.ker := by
  intro x hx
  have habs : |h x| ≤ 0 :=
    (Positive.abs_le_map_abs hh x).trans_eq ((mem_positiveNullIdeal h hh x).mp hx)
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

private lemma strictlyPositive_quotient (h : X →ₗ[ℝ] ℝ) (hh : Positive h) :
    StrictlyPositive (Submodule.liftQ (positiveNullIdeal h hh).toSubmodule h
      (positiveNullIdeal_le_ker h hh)) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (positiveNullIdeal h hh).lift_pos hq.le
  change 0 < h x
  apply lt_of_le_of_ne (hh x hx)
  intro hzero
  have hmem : x ∈ positiveNullIdeal h hh :=
    (mem_positiveNullIdeal h hh x).mpr (by simpa only [abs_of_nonneg hx] using hzero.symm)
  have hqzero : (positiveNullIdeal h hh).mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  exact hq.ne' hqzero

/-- Every positive functional induces a lattice homomorphism with dense range into an `L¹` space. -/
theorem exists_L1_representation_of_positive (h : X →ₗ[ℝ] ℝ) (hh : Positive h) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (T : VecLatHom X (Lp ℝ 1 μ)),
      DenseRange T ∧ ∀ x, ‖T x‖ = h |x| := by
  let J := positiveNullIdeal h hh
  let hbar := Submodule.liftQ J.toSubmodule h (positiveNullIdeal_le_ker h hh)
  obtain ⟨Ω, mΩ, μ, T, _, hTdense, hTrep⟩ :=
    exists_L1_representation_of_strictlyPositive hbar (strictlyPositive_quotient h hh)
  refine ⟨Ω, mΩ, μ, T.comp J.mkQVecLatHom, ?_, ?_⟩
  · change DenseRange (T ∘ J.mkQ)
    rw [DenseRange, (Submodule.mkQ_surjective J.toSubmodule).range_comp]
    exact hTdense
  · intro x
    change ‖T (J.mkQ x)‖ = h |x|
    rw [norm_map_eq_apply_abs hbar T hTrep, ← J.mkQ_abs]
    rfl

end
