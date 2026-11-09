/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Bidual
import BanLat.Functionals.Positive.Separation
import BanLat.Operators.StrictlyPositive
import BanLat.QuasiInteriorPoint

/-!
# Quasi-interior points and strictly positive functionals

A nonnegative vector `e` in a real Banach lattice `X` is quasi-interior if and only if
`f e > 0` for every nonzero positive continuous linear functional `f` on `X`.
Equivalently, evaluation at `e`, viewed as the canonical image of `e` in the bidual,
is a strictly positive functional on `X*`.
-/

section QuasiInteriorPointDuality

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
/-- A positive continuous linear functional that vanishes at a quasi-interior point
is identically zero. -/
private lemma eq_zero_of_apply_quasiInteriorPoint_eq_zero {e : X}
    (he : QuasiInteriorPoint e) {f : StrongDual ℝ X} (hf : 0 ≤ f) (hfe : f e = 0) :
    f = 0 := by
  apply DFunLike.coe_injective
  apply Continuous.ext_on he.2 f.continuous continuous_const
  intro x hx
  obtain ⟨c, _, hxc⟩ := hx
  have hbound : |f x| ≤ 0 := calc
    |f x| ≤ f |x| := StrongDual.abs_apply_le_apply_abs hf x
    _ ≤ f (c • e) := StrongDual.apply_le_apply_of_nonneg hf
      (by simpa only [abs_of_nonneg he.1] using hxc)
    _ = 0 := by rw [map_smul, hfe, smul_zero]
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

/-- If a nonnegative vector `e` is not quasi-interior, there exists a nonzero
positive continuous linear functional that vanishes at `e`. -/
private lemma exists_positive_apply_eq_zero_of_not_quasiInteriorPoint {e : X}
    (he : 0 ≤ e) (hq : ¬ QuasiInteriorPoint e) :
    ∃ f : StrongDual ℝ X, 0 ≤ f ∧ f ≠ 0 ∧ f e = 0 := by
  let J := (OrderIdeal.principal e).topologicalClosure
  have hJ : J ≠ ⊤ := by
    intro h
    apply hq
    refine ⟨he, ?_⟩
    change Dense ((OrderIdeal.principal e).toSubmodule : Set X)
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact congrArg (fun I : OrderIdeal X ↦ I.toSubmodule) h
  obtain ⟨f, hf, hne, hvanish⟩ :=
    StrongDual.exists_positive_annihilator J isClosed_closure hJ
  exact ⟨f, hf, hne, hvanish e (subset_closure (OrderIdeal.self_mem_principal e))⟩

/-- A positive vector in a real Banach lattice is quasi-interior iff every nonzero
positive continuous real functional takes a strictly positive value at it. -/
theorem quasiInteriorPoint_iff_forall_dual_apply_pos {e : X} (he : 0 ≤ e) :
    QuasiInteriorPoint e ↔
      ∀ f : StrongDual ℝ X, 0 ≤ f → f ≠ 0 → 0 < f e := by
  constructor
  · intro hq f hf hne
    exact lt_of_le_of_ne (StrongDual.apply_nonneg_of_nonneg hf he)
      (fun hzero ↦ hne (eq_zero_of_apply_quasiInteriorPoint_eq_zero hq hf hzero.symm))
  · intro h
    by_contra hq
    obtain ⟨f, hf, hne, hfe⟩ :=
      exists_positive_apply_eq_zero_of_not_quasiInteriorPoint he hq
    exact (h f hf hne).ne' hfe

/-- A positive vector in a real Banach lattice is quasi-interior iff its canonical
image in the bidual is a strictly positive functional on the continuous dual. -/
theorem quasiInteriorPoint_iff_strictlyPositive_inclusion {e : X} (he : 0 ≤ e) :
    QuasiInteriorPoint e ↔ StrictlyPositive (BidualSpace.inclusion e).toLinearMap := by
  rw [quasiInteriorPoint_iff_forall_dual_apply_pos he]
  constructor
  · intro h f hf
    exact h f hf.le (ne_of_gt hf)
  · intro h f hf hne
    exact h f (lt_of_le_of_ne hf (Ne.symm hne))

end QuasiInteriorPointDuality
