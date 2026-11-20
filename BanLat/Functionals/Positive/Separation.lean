/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Dual
import BanLat.Substructures.Ideal
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Positive functionals separating closed ideals

Every proper closed order ideal `J` in a real normed vector lattice admits a
nonzero positive continuous linear functional that vanishes on every element of `J`.
-/

namespace StrongDual

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

/-- The modulus of a continuous real linear functional, computed in the order dual,
is again continuous and can therefore be represented by an element of `StrongDual ℝ X`. -/
private lemma exists_continuous_modulus (φ : StrongDual ℝ X) :
    ∃ g : StrongDual ℝ X, ∀ x, g x = |φ.toOrderDualSpace| x := by
  let f := |φ.toOrderDualSpace|
  have hf : Positive f.toLinearMap := OrderDualSpace.nonneg_iff.mp (abs_nonneg _)
  have hb (x : X) : ‖f.toLinearMap x‖ ≤ ‖φ‖ * ‖x‖ := by
    calc ‖f.toLinearMap x‖ = |f x| := Real.norm_eq_abs _
      _ ≤ f |x| := Positive.abs_le_map_abs hf x
      _ ≤ ‖φ‖ * ‖x‖ := by
        apply (OrderDualSpace.isLUB_abs_apply (φ := φ.toOrderDualSpace) (abs_nonneg x)).2
        rintro _ ⟨y, hy, rfl⟩
        change |φ y| ≤ ‖φ‖ * ‖x‖
        calc |φ y| = ‖φ y‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖φ‖ * ‖y‖ := φ.le_opNorm y
          _ ≤ ‖φ‖ * ‖x‖ := mul_le_mul_of_nonneg_left
            (norm_le_norm_of_abs_le_abs hy) (norm_nonneg φ)
  exact ⟨f.toLinearMap.mkContinuous ‖φ‖ hb, fun _ ↦ rfl⟩

/-- Every proper closed order ideal `J` admits a nonzero continuous real linear
functional that vanishes on every element of `J`. -/
private lemma exists_annihilating_functional (J : OrderIdeal X)
    (hclosed : IsClosed (J : Set X)) (hJ : J ≠ ⊤) :
    ∃ f : StrongDual ℝ X, f ≠ 0 ∧ ∀ x ∈ J, f x = 0 := by
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hJ)
  obtain ⟨f, a, hfa, hax⟩ :=
    geometric_hahn_banach_closed_point J.toSubmodule.convex hclosed hx
  have hzero : ∀ y ∈ J, f y = 0 := by
    intro y hy
    by_contra hfy
    have hbound := hfa (((a + 1) / f y) • y) (J.toSubmodule.smul_mem _ hy)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfy] at hbound
    linarith
  refine ⟨f, ?_, hzero⟩
  intro hf
  have ha := hfa 0 J.toSubmodule.zero_mem
  simp only [hf, zero_apply] at ha hax
  exact (ha.trans hax).false

/-- If a continuous linear functional `f` vanishes on an order ideal `J`, then
its order-dual modulus vanishes at `|x|` for every `x ∈ J`. -/
private lemma modulus_vanishes_on_ideal (J : OrderIdeal X) (f : StrongDual ℝ X)
    (hf : ∀ x ∈ J, f x = 0) {x : X} (hx : x ∈ J) :
    |f.toOrderDualSpace| |x| = 0 := by
  apply le_antisymm ?_
    (OrderDualSpace.nonneg_iff.mp (abs_nonneg f.toOrderDualSpace) |x| (abs_nonneg x))
  apply (OrderDualSpace.isLUB_abs_apply (φ := f.toOrderDualSpace) (abs_nonneg x)).2
  rintro _ ⟨y, hy, rfl⟩
  change |f y| ≤ 0
  rw [hf y (J.mem_of_abs_le_abs hx hy), abs_zero]

/-- Every proper closed order ideal in a real normed vector lattice is annihilated
by a nonzero positive continuous real functional. -/
theorem exists_positive_annihilator (J : OrderIdeal X)
    (hclosed : IsClosed (J : Set X)) (hJ : J ≠ ⊤) :
    ∃ g : StrongDual ℝ X, 0 ≤ g ∧ g ≠ 0 ∧ ∀ x ∈ J, g x = 0 := by
  obtain ⟨f, hf, hvanish⟩ := exists_annihilating_functional J hclosed hJ
  obtain ⟨g, hmod⟩ := exists_continuous_modulus f
  have hg : 0 ≤ g := nonneg_iff.mpr fun x hx ↦ by
    rw [hmod]
    exact OrderDualSpace.nonneg_iff.mp (abs_nonneg f.toOrderDualSpace) x hx
  refine ⟨g, hg, ?_, fun x hx ↦ ?_⟩
  · intro hzero
    apply hf
    have habs : |f.toOrderDualSpace| = 0 := by
      ext x
      rw [← hmod x, hzero]
      rfl
    have hz := (abs_eq_zero_iff_zero f.toOrderDualSpace).mp habs
    ext x
    exact congrArg (fun k : OrderDualSpace X ↦ k x) hz
  · have hbound := abs_apply_le_apply_abs hg x
    rw [hmod |x|, modulus_vanishes_on_ideal J f hvanish hx] at hbound
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

end StrongDual
