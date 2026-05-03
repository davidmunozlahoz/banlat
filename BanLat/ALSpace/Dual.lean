import BanLat.ALSpace.Basic
import BanLat.AMSpace.Basic
import BanLat.AMSpace.Max
import BanLat.Dual

/-!
# The dual of an AL-space

This file introduces the canonical unit functional on the norm dual of an
AL-space and the statement-level infrastructure for the fact that the norm dual
of an AL-space is an AM-space with unit.
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

private lemma StrongDual.abs_apply_le_apply_abs {φ : StrongDual ℝ X}
    (hφ : 0 ≤ φ) (x : X) : |φ x| ≤ φ |x| := by
  have hle₁ : φ x ≤ φ |x| :=
    StrongDual.apply_le_apply_of_nonneg hφ (le_abs_self x)
  have hle₂ : -φ x ≤ φ |x| := by
    have h := StrongDual.apply_le_apply_of_nonneg hφ (neg_le_abs x)
    rwa [map_neg] at h
  exact abs_le.mpr ⟨by linarith, hle₁⟩

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

private lemma norm_add_eq_of_nonneg {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
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

private noncomputable def dualUnitLinearMap (X : Type*)
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [ALSpace X] :
    X →ₗ[ℝ] ℝ :=
  Positive.extension
    (fun x : X => fun _ => norm_nonneg x)
    (fun _ _ hx hy => norm_add_eq_of_nonneg hx hy)

/-- The additive map underlying the canonical unit functional on the dual of an
AL-space. -/
private noncomputable def dualUnitAddMonoidHom (X : Type*)
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [ALSpace X] :
    X →+ ℝ := by
  exact (dualUnitLinearMap X).toAddMonoidHom

/-- The canonical unit functional on the norm dual of an AL-space. -/
noncomputable def dualUnit (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [ALSpace X] : StrongDual ℝ X := by
  refine (dualUnitLinearMap X).mkContinuous 1 ?_
  intro x
  have hpos : Positive (dualUnitLinearMap X) :=
    Positive.extension_positive
      (fun x : X => fun _ => norm_nonneg x)
      (fun _ _ hx hy => norm_add_eq_of_nonneg hx hy)
  have h := Positive.abs_le_map_abs hpos x
  have hnonneg :
      dualUnitLinearMap X |x| = ‖|x|‖ := by
    exact Positive.extension_nonneg
      (fun x : X => fun _ => norm_nonneg x)
      (fun _ _ hx hy => norm_add_eq_of_nonneg hx hy)
      (abs_nonneg x)
  rw [Real.norm_eq_abs, one_mul]
  exact h.trans (by rw [hnonneg, norm_abs_eq_norm])

@[simp]
theorem dualUnit_apply (x : X) :
    dualUnit X x = ‖x⁺‖ - ‖x⁻‖ := by
  rfl

/-- On the positive cone, the canonical dual unit agrees with the norm. -/
theorem dualUnit_apply_of_nonneg {x : X} (hx : 0 ≤ x) :
    dualUnit X x = ‖x‖ := by
  rw [dualUnit_apply, posPart_of_nonneg hx, negPart_of_nonneg hx, norm_zero, sub_zero]

/-- The canonical dual unit is a positive functional. -/
theorem dualUnit_nonneg :
    (0 : StrongDual ℝ X) ≤ dualUnit X := by
  change (0 : OrderDualSpace X) ≤ StrongDual.toOrderDualSpace (dualUnit X)
  rw [OrderDualSpace.nonneg_iff]
  intro x hx
  rw [StrongDual.toOrderDualSpace_apply, dualUnit_apply_of_nonneg hx]
  exact norm_nonneg x

/-- The modulus of a dual functional is dominated by its norm times the
canonical dual unit. -/
theorem abs_le_norm_smul_dualUnit (φ : StrongDual ℝ X) :
    (|φ| : StrongDual ℝ X) ≤ ‖φ‖ • dualUnit X := by
  change StrongDual.toOrderDualSpace (|φ| : StrongDual ℝ X) ≤
    StrongDual.toOrderDualSpace (‖φ‖ • dualUnit X)
  rw [OrderDualSpace.le_iff]
  intro x hx
  change (|StrongDual.toOrderDualSpace φ| : OrderDualSpace X) x ≤
    (‖φ‖ • dualUnit X) x
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, dualUnit_apply_of_nonneg hx]
  refine (OrderDualSpace.isLUB_abs_apply
    (φ := StrongDual.toOrderDualSpace φ) hx).2 ?_
  rintro r ⟨y, hyx, rfl⟩
  have hynorm : ‖y‖ ≤ ‖x‖ :=
    norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx]; exact hyx)
  calc
    |φ y| = ‖φ y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ‖ * ‖y‖ := φ.le_opNorm y
    _ ≤ ‖φ‖ * ‖x‖ := mul_le_mul_of_nonneg_left hynorm (norm_nonneg φ)

/-- The dual norm is the gauge norm with respect to the canonical dual unit. -/
theorem norm_eq_gaugeNorm_dualUnit (φ : StrongDual ℝ X) :
    ‖φ‖ = OrderIdeal.gaugeNorm (dualUnit X) φ := by
  apply le_antisymm
  · have hunit : 0 ≤ (dualUnit X : StrongDual ℝ X) := dualUnit_nonneg (X := X)
    have hne : {c : ℝ | 0 ≤ c ∧ |φ| ≤ c • |dualUnit X|}.Nonempty := by
      refine ⟨‖φ‖, norm_nonneg φ, ?_⟩
      simpa [abs_of_nonneg hunit] using abs_le_norm_smul_dualUnit (X := X) φ
    apply le_csInf hne
    intro c hc
    have hc0 : 0 ≤ c := hc.1
    have hle : (|φ| : StrongDual ℝ X) ≤ c • dualUnit X := by
      have hle_abs := hc.2
      rwa [abs_of_nonneg hunit] at hle_abs
    refine ContinuousLinearMap.opNorm_le_bound φ hc0 fun x => ?_
    have h_abs_apply : |φ x| ≤ (|φ| : StrongDual ℝ X) |x| := by
      change |φ x| ≤ (|StrongDual.toOrderDualSpace φ| : OrderDualSpace X) |x|
      exact (OrderDualSpace.isLUB_abs_apply
        (φ := StrongDual.toOrderDualSpace φ) (abs_nonneg x)).1
        ⟨x, le_refl _, rfl⟩
    have h_eval : (|φ| : StrongDual ℝ X) |x| ≤ (c • dualUnit X) |x| := by
      change StrongDual.toOrderDualSpace (|φ| : StrongDual ℝ X) ≤
        StrongDual.toOrderDualSpace (c • dualUnit X) at hle
      exact OrderDualSpace.le_iff.mp hle |x| (abs_nonneg x)
    rw [Real.norm_eq_abs]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul,
      dualUnit_apply_of_nonneg (abs_nonneg x), norm_abs_eq_norm] at h_eval
    exact h_abs_apply.trans h_eval
  · exact OrderIdeal.gaugeNorm_le_of_abs_le (dualUnit X) (norm_nonneg φ)
      (by
        have hunit : 0 ≤ (dualUnit X : StrongDual ℝ X) := dualUnit_nonneg (X := X)
        simpa [abs_of_nonneg hunit] using abs_le_norm_smul_dualUnit (X := X) φ)

/-- The canonical dual unit is a strong order unit on the dual of a
non-trivial AL-space. -/
theorem dualUnit_strongOrderUnit [Nontrivial X] :
    StrongOrderUnit (dualUnit X) := by
  letI : Nontrivial X := inferInstance
  refine ⟨dualUnit_nonneg (X := X), fun φ => ?_⟩
  exact ⟨‖φ‖, norm_nonneg φ, abs_le_norm_smul_dualUnit (X := X) φ⟩

/-- The norm dual of a non-trivial AL-space is an AM-space with unit. -/
noncomputable instance StrongDual.instAMSpaceWithUnit_of_alSpace [Nontrivial X] :
    AMSpaceWithUnit (StrongDual ℝ X) := by
  exact
    { unit := dualUnit X
      strongOrderUnit_unit := dualUnit_strongOrderUnit (X := X)
      norm_eq_gaugeNorm := norm_eq_gaugeNorm_dualUnit (X := X) }

end ALSpace
