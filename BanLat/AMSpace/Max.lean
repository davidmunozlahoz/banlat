import BanLat.AMSpace.Dual
import BanLat.Bidual
import BanLat.Substructures.Band.PPP

/-!
# The maximum formula in AM-spaces

This file proves that the disjoint AM-space axiom implies the usual maximum
formula for suprema of arbitrary non-negative elements.
-/

namespace AMSpace

noncomputable section

private lemma nonneg_of_isVLDisjoint_add_eq_of_nonneg
    {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    {x y z : E} (hx : 0 ≤ x) (hyz : IsVLDisjoint y z) (hadd : y + z = x) :
  0 ≤ y ∧ 0 ≤ z := by
  have hsub : |y| + |z| - (y + z) = 0 := by
    calc
      |y| + |z| - (y + z) = |y + z| - (y + z) := by
        rw [abs_add_of_isVLDisjoint hyz]
      _ = |x| - x := by rw [hadd]
      _ = 0 := by rw [abs_of_nonneg hx, sub_self]
  have hy0 : |y| - y = 0 := by
    have hle : |y| - y ≤ |y| + |z| - (y + z) := by
      calc
        |y| - y ≤ (|y| - y) + (|z| - z) :=
          le_add_of_nonneg_right (sub_nonneg.mpr (le_abs_self z))
        _ = |y| + |z| - (y + z) := by abel
    exact le_antisymm (by rwa [hsub] at hle) (sub_nonneg.mpr (le_abs_self y))
  have hz0 : |z| - z = 0 := by
    calc
      |z| - z = 0 + (|z| - z) := by rw [zero_add]
      _ = (|y| - y) + (|z| - z) := by rw [hy0]
      _ = |y| + |z| - (y + z) := by abel
      _ = 0 := hsub
  constructor
  · rw [← sub_eq_zero.mp hy0]
    exact abs_nonneg y
  · rw [← sub_eq_zero.mp hz0]
    exact abs_nonneg z

private lemma StrongDual.norm_sup_le_max_of_nonneg_of_alSpace
    {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [BanachLattice E] [HasPrincipalProjectionProperty E]
    (hAL : ∀ {u v : E}, u ⊓ v = 0 → ‖u + v‖ = ‖u‖ + ‖v‖)
    {φ ψ : StrongDual ℝ E} (hφ : 0 ≤ φ) (_hψ : 0 ≤ ψ) :
    ‖φ ⊔ ψ‖ ≤ max ‖φ‖ ‖ψ‖ := by
  have hsup_nonneg : 0 ≤ φ ⊔ ψ := le_sup_of_le_left hφ
  rw [StrongDual.norm_of_nonneg hsup_nonneg]
  set S := ((φ ⊔ ψ : StrongDual ℝ E) : E → ℝ) ''
    ({x : E | ‖x‖ ≤ 1} ∩ {x : E | 0 ≤ x})
  have hS_ne : S.Nonempty := by
    refine ⟨0, 0, ⟨by simp, le_rfl⟩, ?_⟩
    simp
  refine csSup_le hS_ne ?_
  rintro r ⟨x, ⟨hx_norm, hx_nonneg⟩, rfl⟩
  let φ' : OrderDualSpace E := StrongDual.toOrderDualSpace φ
  let ψ' : OrderDualSpace E := StrongDual.toOrderDualSpace ψ
  have hLUB := OrderBoundedHom.isLUB_sup_apply_disjoint
    (f := φ') (g := ψ') hx_nonneg
  change (φ' ⊔ ψ') x ≤ max ‖φ‖ ‖ψ‖
  refine hLUB.2 ?_
  rintro w ⟨u, v, huv_disj, huv_sum, rfl⟩
  obtain ⟨hu_nonneg, hv_nonneg⟩ :=
    nonneg_of_isVLDisjoint_add_eq_of_nonneg hx_nonneg huv_disj huv_sum
  have huv_inf : u ⊓ v = 0 :=
    inf_eq_zero_of_isVLDisjoint hu_nonneg hv_nonneg huv_disj
  have hnorm_add : ‖u‖ + ‖v‖ = ‖x‖ := by
    rw [← huv_sum, hAL huv_inf]
  have hφu : φ u ≤ ‖φ‖ * ‖u‖ := by
    calc
      φ u ≤ ‖φ u‖ := by exact le_abs_self (φ u)
      _ ≤ ‖φ‖ * ‖u‖ := φ.le_opNorm u
  have hψv : ψ v ≤ ‖ψ‖ * ‖v‖ := by
    calc
      ψ v ≤ ‖ψ v‖ := by exact le_abs_self (ψ v)
      _ ≤ ‖ψ‖ * ‖v‖ := ψ.le_opNorm v
  have hmax_nonneg : 0 ≤ max ‖φ‖ ‖ψ‖ :=
    le_max_of_le_left (norm_nonneg φ)
  calc
    φ u + ψ v ≤ ‖φ‖ * ‖u‖ + ‖ψ‖ * ‖v‖ := add_le_add hφu hψv
    _ ≤ max ‖φ‖ ‖ψ‖ * ‖u‖ + max ‖φ‖ ‖ψ‖ * ‖v‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v))
    _ = max ‖φ‖ ‖ψ‖ * (‖u‖ + ‖v‖) := by ring
    _ = max ‖φ‖ ‖ψ‖ * ‖x‖ := by rw [hnorm_add]
    _ ≤ max ‖φ‖ ‖ψ‖ * 1 :=
      mul_le_mul_of_nonneg_left hx_norm hmax_nonneg
    _ = max ‖φ‖ ‖ψ‖ := by rw [mul_one]

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [AMSpace X]

/-- In an AM-space, the norm of the supremum of two non-negative elements is
the maximum of their norms. -/
theorem norm_sup_eq_max_of_nonneg {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x ⊔ y‖ = max ‖x‖ ‖y‖ := by
  apply le_antisymm
  · haveI : ALSpace (StrongDual ℝ X) :=
      StrongDual.instALSpace_of_amSpace (X := X)
    haveI : HasPrincipalProjectionProperty (StrongDual ℝ X) := by
      infer_instance
    let x'' : StrongDual ℝ (StrongDual ℝ X) := BidualSpace.inclusion x
    let y'' : StrongDual ℝ (StrongDual ℝ X) := BidualSpace.inclusion y
    have hx' : 0 ≤ x'' := by
      dsimp [x'']
      exact BidualSpace.inclusion_nonneg hx
    have hy' : 0 ≤ y'' := by
      dsimp [y'']
      exact BidualSpace.inclusion_nonneg hy
    have hle : ‖x'' ⊔ y''‖ ≤ max ‖x''‖ ‖y''‖ :=
      StrongDual.norm_sup_le_max_of_nonneg_of_alSpace
        (E := StrongDual ℝ X)
        (fun {u v} huv => ALSpace.norm_add_eq_of_inf_eq_zero huv)
        (φ := x'') (ψ := y'') hx' hy'
    have hx''_def : x'' = BidualSpace.inclusion x := rfl
    have hy''_def : y'' = BidualSpace.inclusion y := rfl
    rw [hx''_def, hy''_def, ← BidualSpace.inclusion_sup,
      BidualSpace.norm_inclusion (X := X) (x ⊔ y),
      BidualSpace.norm_inclusion (X := X) x,
      BidualSpace.norm_inclusion (X := X) y] at hle
    exact hle
  · have hsup_nonneg : 0 ≤ x ⊔ y := le_sup_of_le_left hx
    refine max_le ?_ ?_
    · exact norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg hx, abs_of_nonneg hsup_nonneg]
        exact le_sup_left)
    · exact norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg hy, abs_of_nonneg hsup_nonneg]
        exact le_sup_right)

end

end AMSpace
