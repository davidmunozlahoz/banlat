import BanLat.AMSpace.Basic
import BanLat.ALSpace.Basic
import BanLat.Dual

/-!
# The dual of an AM-space

This file records that the norm dual of an AM-space is an AL-space.
-/

namespace AMSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [AMSpace X]

private lemma StrongDual.exists_pos_norm_le_one_norm_sub_lt
    {φ : StrongDual ℝ X} (hφ : 0 ≤ φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, 0 ≤ x ∧ ‖x‖ ≤ 1 ∧ ‖φ‖ - ε < φ x := by
  obtain ⟨x, hxnorm, hxφ⟩ :=
    φ.exists_lt_apply_of_lt_opNorm (sub_lt_self _ hε)
  refine ⟨|x|, abs_nonneg x, ?_, ?_⟩
  · rw [norm_abs_eq_norm]
    exact hxnorm.le
  · exact hxφ.trans_le (by
      rw [Real.norm_eq_abs]
      exact StrongDual.abs_apply_le_apply_abs hφ x)

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

private lemma StrongDual.exists_disjoint_pos_norm_le_one_norm_sub_lt
    {φ ψ : StrongDual ℝ X} (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ)
    (hdisj : φ ⊓ ψ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ x y : X, 0 ≤ x ∧ 0 ≤ y ∧ x ⊓ y = 0 ∧ ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      ‖φ‖ - ε < φ x ∧ ‖ψ‖ - ε < ψ y := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨u, hu0, hunorm, huφ⟩ :=
    StrongDual.exists_pos_norm_le_one_norm_sub_lt hφ hε4
  obtain ⟨v, hv0, hvnorm, hvψ⟩ :=
    StrongDual.exists_pos_norm_le_one_norm_sub_lt hψ hε4
  obtain ⟨u₁, u₂, hu₁0, hu₂0, hu_sum, hu_small⟩ :=
    exists_decomposition_apply_add_apply_lt hdisj hu0 hε4
  obtain ⟨v₁, v₂, hv₁0, hv₂0, hv_sum, hv_small⟩ :=
    exists_decomposition_apply_add_apply_lt hdisj hv0 hε4
  set w : X := u₂ ⊓ v₁
  refine ⟨u₂ - w, v₁ - w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr inf_le_left
  · exact sub_nonneg.mpr inf_le_right
  · exact inf_eq_zero_of_isVLDisjoint
      (sub_nonneg.mpr inf_le_left) (sub_nonneg.mpr inf_le_right)
      (by simpa [w] using isVLDisjoint_sub_inf u₂ v₁)
  · have hle_abs : |u₂ - w| ≤ |u| := by
      rw [abs_of_nonneg (sub_nonneg.mpr inf_le_left), abs_of_nonneg hu0]
      have hw0 : 0 ≤ w := le_inf hu₂0 hv₁0
      exact (sub_le_self u₂ hw0).trans (by
        rw [← hu_sum]
        exact le_add_of_nonneg_left hu₁0)
    exact (norm_le_norm_of_abs_le_abs hle_abs).trans hunorm
  · have hle_abs : |v₁ - w| ≤ |v| := by
      rw [abs_of_nonneg (sub_nonneg.mpr inf_le_right), abs_of_nonneg hv0]
      have hw0 : 0 ≤ w := le_inf hu₂0 hv₁0
      exact (sub_le_self v₁ hw0).trans (by
        rw [← hv_sum]
        exact le_add_of_nonneg_right hv₂0)
    exact (norm_le_norm_of_abs_le_abs hle_abs).trans hvnorm
  · have hφu₁_nonneg : 0 ≤ φ u₁ := StrongDual.apply_nonneg_of_nonneg hφ hu₁0
    have hψu₂_nonneg : 0 ≤ ψ u₂ := StrongDual.apply_nonneg_of_nonneg hψ hu₂0
    have hφu₁_lt : φ u₁ < ε / 4 := by linarith
    have hψu₂_lt : ψ u₂ < ε / 4 := by linarith
    have hφv₁_nonneg : 0 ≤ φ v₁ := StrongDual.apply_nonneg_of_nonneg hφ hv₁0
    have hψv₂_nonneg : 0 ≤ ψ v₂ := StrongDual.apply_nonneg_of_nonneg hψ hv₂0
    have hφv₁_lt : φ v₁ < ε / 4 := by linarith
    have hψv₂_lt : ψ v₂ < ε / 4 := by linarith
    have hφw_le : φ w ≤ φ v₁ :=
      StrongDual.apply_le_apply_of_nonneg hφ inf_le_right
    have hφu₂_eq : φ u₂ = φ u - φ u₁ := by
      rw [← hu_sum, map_add]; abel
    have hcalc : φ (u₂ - w) = φ u₂ - φ w := by rw [map_sub]
    rw [hcalc]
    linarith
  · have hφu₁_nonneg : 0 ≤ φ u₁ := StrongDual.apply_nonneg_of_nonneg hφ hu₁0
    have hψu₂_nonneg : 0 ≤ ψ u₂ := StrongDual.apply_nonneg_of_nonneg hψ hu₂0
    have hφu₁_lt : φ u₁ < ε / 4 := by linarith
    have hψu₂_lt : ψ u₂ < ε / 4 := by linarith
    have hφv₁_nonneg : 0 ≤ φ v₁ := StrongDual.apply_nonneg_of_nonneg hφ hv₁0
    have hψv₂_nonneg : 0 ≤ ψ v₂ := StrongDual.apply_nonneg_of_nonneg hψ hv₂0
    have hφv₁_lt : φ v₁ < ε / 4 := by linarith
    have hψv₂_lt : ψ v₂ < ε / 4 := by linarith
    have hψw_le : ψ w ≤ ψ u₂ :=
      StrongDual.apply_le_apply_of_nonneg hψ inf_le_left
    have hψv₁_eq : ψ v₁ = ψ v - ψ v₂ := by
      rw [← hv_sum, map_add]; abel
    have hcalc : ψ (v₁ - w) = ψ v₁ - ψ w := by rw [map_sub]
    rw [hcalc]
    linarith

private lemma StrongDual.norm_add_eq_of_nonneg_inf_eq_zero
    {φ ψ : StrongDual ℝ X} (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ) (hdisj : φ ⊓ ψ = 0) :
    ‖φ + ψ‖ = ‖φ‖ + ‖ψ‖ := by
  refine le_antisymm (norm_add_le φ ψ) ?_
  by_contra hlt_not
  have hlt : ‖φ + ψ‖ < ‖φ‖ + ‖ψ‖ := lt_of_not_ge hlt_not
  set ε : ℝ := (‖φ‖ + ‖ψ‖ - ‖φ + ψ‖) / 3 with hε_def
  have hεpos : 0 < ε := by
    rw [hε_def]
    linarith
  obtain ⟨x, y, hx0, hy0, hxy, hxnorm, hynorm, hxφ, hyψ⟩ :=
    StrongDual.exists_disjoint_pos_norm_le_one_norm_sub_lt hφ hψ hdisj hεpos
  have hsum_norm : ‖x + y‖ ≤ 1 := by
    have hsup : x + y = x ⊔ y :=
      add_eq_sup_of_isVLDisjoint_of_nonneg hx0 hy0 (isVLDisjoint_of_inf_eq_zero hxy)
    rw [hsup, AMSpace.norm_sup_eq_max_of_inf_eq_zero hxy]
    exact max_le hxnorm hynorm
  have hpos_sum : 0 ≤ (φ + ψ) (x + y) := by
    apply add_nonneg
    · exact StrongDual.apply_nonneg_of_nonneg hφ (add_nonneg hx0 hy0)
    · exact StrongDual.apply_nonneg_of_nonneg hψ (add_nonneg hx0 hy0)
  have hle_norm : (φ + ψ) (x + y) ≤ ‖φ + ψ‖ := by
    have hle := (φ + ψ).le_opNorm (x + y)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos_sum] at hle
    exact hle.trans (by simpa using mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _))
  have hlarge : ‖φ‖ + ‖ψ‖ - 2 * ε < (φ + ψ) (x + y) := by
    rw [map_add]
    change ‖φ‖ + ‖ψ‖ - 2 * ε < (φ x + ψ x) + (φ y + ψ y)
    have hφy_nonneg : 0 ≤ φ y := StrongDual.apply_nonneg_of_nonneg hφ hy0
    have hψx_nonneg : 0 ≤ ψ x := StrongDual.apply_nonneg_of_nonneg hψ hx0
    linarith
  have : ‖φ‖ + ‖ψ‖ - 2 * ε < ‖φ + ψ‖ := hlarge.trans_le hle_norm
  rw [hε_def] at this
  linarith

/-- The norm dual of an AM-space is an AL-space. -/
noncomputable instance StrongDual.instALSpaceOfAMSpace :
    ALSpace (StrongDual ℝ X) where
  norm_add_eq_of_inf_eq_zero {φ ψ} hφψ := by
    have hφ : 0 ≤ φ := by
      rw [← hφψ]
      exact inf_le_left
    have hψ : 0 ≤ ψ := by
      rw [← hφψ]
      exact inf_le_right
    exact StrongDual.norm_add_eq_of_nonneg_inf_eq_zero hφ hψ hφψ

end AMSpace
