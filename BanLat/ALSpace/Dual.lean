import BanLat.ALSpace.Add

/-!
# The dual of an AL-space

This file introduces the canonical unit functional on the norm dual of an
AL-space and the statement-level infrastructure for the fact that the norm dual
of a non-trivial AL-space is an AM-space with unit.
-/

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

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
