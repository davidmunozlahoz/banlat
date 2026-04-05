import BanLat.AMSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice

/-!
# Spaces of continuous functions as Banach lattices and AM-spaces

For a compact topological space `K`, the space `C(K, ℝ)` of continuous
real-valued functions equipped with the supremum norm and the pointwise order
is a Banach lattice. Its norm is an AM-norm, so `C(K, ℝ)` is an AM-space.
When `K` is nonempty the constant function `1` is a strong unit and the sup
norm agrees with the gauge norm, making `C(K, ℝ)` an AM-space with unit.
-/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-! ### Lattice and order structure

Mathlib provides `Lattice C(K, ℝ)` (pointwise, via
`ContinuousMap.instLatticeOfTopologicalLattice`) and `IsOrderedAddMonoid C(K, ℝ)`
(via `ContinuousMap.instIsOrderedAddMonoid`). The norm comes from
`ContinuousMap.instNormedAddCommGroup`.
-/

/-! ### Vector lattice -/

/-- `C(K, ℝ)` is a vector lattice: a real module whose positive cone is closed
under scalar multiplication by non-negative reals. -/
noncomputable instance instVectorLatticeCofK : VectorLattice C(K, ℝ) where
  smul_le_smul_of_nonneg_left {a} ha {b₁ b₂} hb := by
    rw [ContinuousMap.le_def] at hb ⊢
    intro x; simp only [ContinuousMap.smul_apply]
    exact smul_le_smul_of_nonneg_left (hb x) ha

/-! ### Normed vector lattice -/

/-- The sup norm on `C(K, ℝ)` is solid: `|f| ≤ |g|` pointwise implies
`‖f‖ ≤ ‖g‖`. -/
instance instHasSolidNormCofK : HasSolidNorm C(K, ℝ) where
  solid {f g} h := by
    simp only [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_mono ⟨‖g‖, Set.forall_mem_range.mpr
      (fun x => ContinuousMap.norm_coe_le_norm g x)⟩
    intro x
    have := ContinuousMap.le_def.mp h x
    rw [ContinuousMap.abs_apply, ContinuousMap.abs_apply] at this
    exact HasSolidNorm.solid this

/-- `C(K, ℝ)` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeCofK :
    NormedVectorLattice C(K, ℝ) where

/-! ### Banach lattice -/

/-- `C(K, ℝ)` is a Banach lattice: a complete normed vector lattice. -/
noncomputable instance instBanachLatticeCofK : BanachLattice C(K, ℝ) where

/-! ### AM-space -/

private theorem norm_coe_le_norm_nonneg
    {f : C(K, ℝ)} (hf : 0 ≤ f) (x : K) : f x ≤ ‖f‖ := by
  calc f x
      = |f x| := (abs_of_nonneg (ContinuousMap.le_def.mp hf x)).symm
    _ = ‖f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f x

/-- `C(K, ℝ)` is an AM-space: for non-negative `f, g`, the sup norm satisfies
`‖f ⊔ g‖ = max ‖f‖ ‖g‖`. -/
noncomputable instance instAMSpaceCofK : AMSpace C(K, ℝ) where
  norm_sup_eq_max_of_nonneg {f g} hf hg := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _
        (le_max_of_le_left (norm_nonneg f))).mpr
      intro x
      rw [ContinuousMap.sup_apply, Real.norm_eq_abs,
        abs_of_nonneg
          (le_sup_of_le_left (ContinuousMap.le_def.mp hf x))]
      exact max_le_max (norm_coe_le_norm_nonneg hf x)
        (norm_coe_le_norm_nonneg hg x)
    · exact max_le
        (HasSolidNorm.solid (by
          rw [abs_of_nonneg hf,
            abs_of_nonneg (le_sup_of_le_left hf)]
          exact le_sup_left))
        (HasSolidNorm.solid (by
          rw [abs_of_nonneg hg,
            abs_of_nonneg (le_sup_of_le_left hf)]
          exact le_sup_right))

/-! ### Strong unit and AM-space with unit -/

variable [Nonempty K]

/-- The constant function `1` is a strong unit in `C(K, ℝ)`. -/
instance instIsStrongUnitOne :
    IsStrongUnit C(K, ℝ) (ContinuousMap.const K (1 : ℝ)) where
  pos := by
    apply lt_of_le_of_ne
    · intro x; simp
    · intro h
      have := congr_fun
        (congr_arg ContinuousMap.toFun h)
        (Classical.arbitrary K)
      simp at this
  dominates f := by
    refine ⟨‖f‖ + 1, by linarith [norm_nonneg f], ?_⟩
    rw [ContinuousMap.le_def]
    intro x
    rw [ContinuousMap.abs_apply, ContinuousMap.smul_apply,
      ContinuousMap.const_apply, smul_eq_mul, mul_one]
    calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f x
      _ ≤ ‖f‖ + 1 := le_add_of_nonneg_right one_pos.le

omit [CompactSpace K] [Nonempty K] in
private theorem abs_const_one :
    |ContinuousMap.const K (1 : ℝ)| = ContinuousMap.const K 1 :=
  abs_of_nonneg (fun _ => by simp)

private theorem gauge_set_eq (f : C(K, ℝ)) :
    {c : ℝ | 0 ≤ c ∧
      |f| ≤ c • |ContinuousMap.const K (1 : ℝ)|}
    = {c : ℝ | ‖f‖ ≤ c} := by
  ext c; simp only [Set.mem_setOf_eq, abs_const_one]
  constructor
  · rintro ⟨_, hle⟩
    rw [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_le; intro x; rw [Real.norm_eq_abs]
    have := ContinuousMap.le_def.mp hle x
    rwa [ContinuousMap.abs_apply,
      ContinuousMap.smul_apply,
      ContinuousMap.const_apply,
      smul_eq_mul, mul_one] at this
  · intro hc
    refine ⟨le_trans (norm_nonneg f) hc, ?_⟩
    rw [ContinuousMap.le_def]; intro x
    rw [ContinuousMap.abs_apply,
      ContinuousMap.smul_apply,
      ContinuousMap.const_apply, smul_eq_mul, mul_one]
    calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f x
      _ ≤ c := hc

private theorem norm_eq_gaugeNorm_const (f : C(K, ℝ)) :
    ‖f‖ = OrderIdeal.gaugeNorm
      (ContinuousMap.const K (1 : ℝ)) f := by
  unfold OrderIdeal.gaugeNorm
  rw [gauge_set_eq]; exact csInf_Ici.symm

/-- `C(K, ℝ)` is an AM-space with unit `𝟙 = 1`. The sup norm agrees with the
gauge norm with respect to the constant function `1`. -/
noncomputable instance instAMSpaceWithUnitCofK :
    AMSpaceWithUnit C(K, ℝ) where
  unit := ContinuousMap.const K 1
  unit_pos := by
    apply lt_of_le_of_ne
    · intro x; simp
    · intro h
      have := congr_fun
        (congr_arg ContinuousMap.toFun h)
        (Classical.arbitrary K)
      simp at this
  norm_eq_gaugeNorm := norm_eq_gaugeNorm_const
