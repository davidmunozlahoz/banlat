import BanLat.ALSpace.Basic
import BanLat.AMSpace.Basic
import BanLat.AMSpace.Max
import BanLat.Dual

/-!
# Additivity in AL-spaces

This file proves that the AL-space axiom, stated for disjoint positive sums,
implies additivity of the norm on the whole positive cone.
-/

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

private lemma StrongDual.apply_nonneg_of_nonneg {φ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) {x : X} (hx : 0 ≤ x) : 0 ≤ φ x := by
  change StrongDual.toOrderDualSpace 0 ≤ StrongDual.toOrderDualSpace φ at hφ
  simpa using hφ x hx

private lemma StrongDual.apply_le_apply_of_nonneg {φ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) {x y : X} (hxy : x ≤ y) : φ x ≤ φ y := by
  have hnonneg : 0 ≤ φ (y - x) :=
    StrongDual.apply_nonneg_of_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

omit [ALSpace X] in
private lemma nonneg_of_isVLDisjoint_add_eq_of_nonneg
    {x y z : X} (hx : 0 ≤ x) (hyz : IsVLDisjoint y z) (hadd : y + z = x) :
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

private lemma exists_decomposition_apply_add_apply_lt
    {φ ψ : StrongDual ℝ X} (hdisj : φ ⊓ ψ = 0)
    {u : X} (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ u₁ u₂ : X, 0 ≤ u₁ ∧ 0 ≤ u₂ ∧ u₁ + u₂ = u ∧
      φ u₁ + ψ u₂ < ε := by
  let φ' : OrderDualSpace X := StrongDual.toOrderDualSpace φ
  let ψ' : OrderDualSpace X := StrongDual.toOrderDualSpace ψ
  have hglb : IsGLB
      {r : ℝ | ∃ y z : X, 0 ≤ y ∧ 0 ≤ z ∧ y + z = u ∧
        r = φ' y + ψ' z} 0 := by
    have h := OrderDualSpace.isGLB_inf_apply (φ := φ') (ψ := ψ') hu
    have hzero : (φ' ⊓ ψ') u = 0 := by
      dsimp [φ', ψ']
      change (φ ⊓ ψ) u = 0
      rw [hdisj]
      rfl
    simpa [hzero] using h
  by_contra hno
  have hlower : ε ∈ lowerBounds
      {r : ℝ | ∃ y z : X, 0 ≤ y ∧ 0 ≤ z ∧ y + z = u ∧
        r = φ' y + ψ' z} := by
    rintro r ⟨y, z, hy, hz, hyz, rfl⟩
    exact le_of_not_gt (fun hlt => hno ⟨y, z, hy, hz, hyz, hlt⟩)
  have hε_le_zero : ε ≤ 0 := hglb.2 hlower
  exact (not_lt_of_ge hε_le_zero) hε

private lemma StrongDual.add_apply_le_max_of_nonneg_inf_eq_zero
    {φ ψ : StrongDual ℝ X} (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ) (hdisj : φ ⊓ ψ = 0)
    {x : X} (hx : 0 ≤ x) (hxnorm : ‖x‖ ≤ 1) :
    (φ + ψ) x ≤ max ‖φ‖ ‖ψ‖ := by
  by_contra hle
  have hlt : max ‖φ‖ ‖ψ‖ < (φ + ψ) x := lt_of_not_ge hle
  set ε : ℝ := ((φ + ψ) x - max ‖φ‖ ‖ψ‖) / 3 with hε_def
  have hεpos : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨u, v, hu0, hv0, huv, huv_small⟩ :=
    exists_decomposition_apply_add_apply_lt hdisj hx hεpos
  set w : X := u ⊓ v with hw_def
  set a : X := v - w with ha_def
  set b : X := u - w with hb_def
  have hw0 : 0 ≤ w := by rw [hw_def]; exact le_inf hu0 hv0
  have ha0 : 0 ≤ a := by rw [ha_def, hw_def]; exact sub_nonneg.mpr inf_le_right
  have hb0 : 0 ≤ b := by rw [hb_def, hw_def]; exact sub_nonneg.mpr inf_le_left
  have hab_disj : a ⊓ b = 0 := by
    apply inf_eq_zero_of_isVLDisjoint ha0 hb0
    rw [ha_def, hb_def, hw_def]
    exact isVLDisjoint_comm.mp (isVLDisjoint_sub_inf u v)
  have hab_le_x : a + b ≤ x := by
    rw [ha_def, hb_def, hw_def, ← huv]
    calc
      v - u ⊓ v + (u - u ⊓ v) = u + v - ((u ⊓ v) + (u ⊓ v)) := by abel
      _ ≤ u + v := sub_le_self _ (add_nonneg (le_inf hu0 hv0) (le_inf hu0 hv0))
  have hab_norm : ‖a‖ + ‖b‖ = ‖a + b‖ := by
    rw [ALSpace.norm_add_eq_of_inf_eq_zero hab_disj]
  have hab_norm_le : ‖a + b‖ ≤ ‖x‖ := by
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (add_nonneg ha0 hb0), abs_of_nonneg hx]
    exact hab_le_x
  have hmax_nonneg : 0 ≤ max ‖φ‖ ‖ψ‖ :=
    le_max_of_le_left (norm_nonneg φ)
  have hφa : φ a ≤ ‖φ‖ * ‖a‖ := by
    calc φ a ≤ ‖φ a‖ := le_abs_self _
      _ ≤ ‖φ‖ * ‖a‖ := φ.le_opNorm a
  have hψb : ψ b ≤ ‖ψ‖ * ‖b‖ := by
    calc ψ b ≤ ‖ψ b‖ := le_abs_self _
      _ ≤ ‖ψ‖ * ‖b‖ := ψ.le_opNorm b
  have h_ab_bound : φ a + ψ b ≤ max ‖φ‖ ‖ψ‖ := by
    calc
      φ a + ψ b ≤ ‖φ‖ * ‖a‖ + ‖ψ‖ * ‖b‖ := add_le_add hφa hψb
      _ ≤ max ‖φ‖ ‖ψ‖ * ‖a‖ + max ‖φ‖ ‖ψ‖ * ‖b‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg a))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg b))
      _ = max ‖φ‖ ‖ψ‖ * (‖a‖ + ‖b‖) := by ring
      _ = max ‖φ‖ ‖ψ‖ * ‖a + b‖ := by rw [hab_norm]
      _ ≤ max ‖φ‖ ‖ψ‖ * ‖x‖ := mul_le_mul_of_nonneg_left hab_norm_le hmax_nonneg
      _ ≤ max ‖φ‖ ‖ψ‖ * 1 := mul_le_mul_of_nonneg_left hxnorm hmax_nonneg
      _ = max ‖φ‖ ‖ψ‖ := by rw [mul_one]
  have hw_le_u : w ≤ u := by rw [hw_def]; exact inf_le_left
  have hw_le_v : w ≤ v := by rw [hw_def]; exact inf_le_right
  have hφw_le : φ w ≤ φ u := StrongDual.apply_le_apply_of_nonneg hφ hw_le_u
  have hψw_le : ψ w ≤ ψ v := StrongDual.apply_le_apply_of_nonneg hψ hw_le_v
  have hcross : φ v + ψ u ≤ φ a + ψ b + ε := by
    have hv_eq : v = a + w := by rw [ha_def]; abel
    have hu_eq : u = b + w := by rw [hb_def]; abel
    calc
      φ v + ψ u = φ a + ψ b + (φ w + ψ w) := by
        rw [hv_eq, hu_eq, map_add, map_add]; abel
      _ ≤ φ a + ψ b + (φ u + ψ v) := by linarith
      _ ≤ φ a + ψ b + ε := by linarith
  have hmain : (φ + ψ) x ≤ max ‖φ‖ ‖ψ‖ + 2 * ε := by
    calc
      (φ + ψ) x = φ u + ψ v + (φ v + ψ u) := by
        rw [← huv]
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      _ ≤ ε + (φ a + ψ b + ε) := by linarith
      _ ≤ max ‖φ‖ ‖ψ‖ + 2 * ε := by linarith
  rw [hε_def] at hmain
  linarith

/-- The norm dual of an AL-space is an AM-space. -/
noncomputable instance StrongDual.instAMSpace_of_alSpace :
    AMSpace (StrongDual ℝ X) where
  norm_add_eq_max_of_inf_eq_zero {φ ψ} hφψ := by
    have hφ : 0 ≤ φ := by
      rw [← hφψ]
      exact inf_le_left
    have hψ : 0 ≤ ψ := by
      rw [← hφψ]
      exact inf_le_right
    have hsum : 0 ≤ φ + ψ := add_nonneg hφ hψ
    refine le_antisymm ?_ ?_
    · rw [StrongDual.norm_of_nonneg hsum]
      set S := ((φ + ψ : StrongDual ℝ X) : X → ℝ) ''
        ({x : X | ‖x‖ ≤ 1} ∩ {x : X | 0 ≤ x})
      have hS_ne : S.Nonempty := by
        refine ⟨0, 0, ⟨by simp, le_rfl⟩, by simp⟩
      refine csSup_le hS_ne ?_
      rintro r ⟨x, ⟨hxnorm, hx0⟩, rfl⟩
      exact StrongDual.add_apply_le_max_of_nonneg_inf_eq_zero hφ hψ hφψ hx0 hxnorm
    · refine max_le ?_ ?_
      · apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg hφ, abs_of_nonneg hsum]
        exact le_add_of_nonneg_right hψ
      · apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg hψ, abs_of_nonneg hsum]
        exact le_add_of_nonneg_left hφ

/-- In an AL-space, the norm is additive on positive elements. -/
theorem norm_add_eq_of_nonneg {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  refine le_antisymm (norm_add_le x y) ?_
  obtain ⟨φ, hφnorm, hφx⟩ := exists_dual_vector'' ℝ x
  obtain ⟨ψ, hψnorm, hψy⟩ := exists_dual_vector'' ℝ y
  let φp : StrongDual ℝ X := |φ|
  let ψp : StrongDual ℝ X := |ψ|
  have hφp0 : 0 ≤ φp := abs_nonneg φ
  have hψp0 : 0 ≤ ψp := abs_nonneg ψ
  have hφpnorm : ‖φp‖ ≤ 1 := by
    rw [StrongDual.norm_abs]
    exact hφnorm
  have hψpnorm : ‖ψp‖ ≤ 1 := by
    rw [StrongDual.norm_abs]
    exact hψnorm
  have hφpx : ‖x‖ ≤ φp x := by
    calc
      ‖x‖ = φ x := hφx.symm
      _ ≤ |φ x| := le_abs_self _
      _ ≤ φp x := by
        change |φ x| ≤ (|StrongDual.toOrderDualSpace φ| : OrderDualSpace X) x
        exact (OrderDualSpace.isLUB_abs_apply
          (φ := StrongDual.toOrderDualSpace φ) hx).1
          ⟨x, by rw [abs_of_nonneg hx], rfl⟩
  have hψpy : ‖y‖ ≤ ψp y := by
    calc
      ‖y‖ = ψ y := hψy.symm
      _ ≤ |ψ y| := le_abs_self _
      _ ≤ ψp y := by
        change |ψ y| ≤ (|StrongDual.toOrderDualSpace ψ| : OrderDualSpace X) y
        exact (OrderDualSpace.isLUB_abs_apply
          (φ := StrongDual.toOrderDualSpace ψ) hy).1
          ⟨y, by rw [abs_of_nonneg hy], rfl⟩
  let θ : StrongDual ℝ X := φp ⊔ ψp
  have hθ0 : 0 ≤ θ := le_sup_of_le_left hφp0
  have hθnorm : ‖θ‖ ≤ 1 := by
    rw [AMSpace.norm_sup_eq_max_of_nonneg hφp0 hψp0]
    exact max_le hφpnorm hψpnorm
  have hφp_le : φp ≤ θ := le_sup_left
  have hψp_le : ψp ≤ θ := le_sup_right
  have hx_le : φp x ≤ θ x := by
    change StrongDual.toOrderDualSpace φp ≤ StrongDual.toOrderDualSpace θ at hφp_le
    exact OrderDualSpace.le_iff.mp hφp_le x hx
  have hy_le : ψp y ≤ θ y := by
    change StrongDual.toOrderDualSpace ψp ≤ StrongDual.toOrderDualSpace θ at hψp_le
    exact OrderDualSpace.le_iff.mp hψp_le y hy
  calc
    ‖x‖ + ‖y‖ ≤ θ x + θ y := add_le_add (hφpx.trans hx_le) (hψpy.trans hy_le)
    _ = θ (x + y) := by rw [map_add]
    _ ≤ ‖θ (x + y)‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ‖θ‖ * ‖x + y‖ := θ.le_opNorm (x + y)
    _ ≤ 1 * ‖x + y‖ := mul_le_mul_of_nonneg_right hθnorm (norm_nonneg _)
    _ = ‖x + y‖ := one_mul _

end ALSpace
