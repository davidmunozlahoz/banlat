/-
Authors: David Muñoz-Lahoz
-/

import BanLat.AMSpace.Basic
import BanLat.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice

/-!
# `C(K, ℝ)` as a Banach lattice

For a compact topological space `K`, the space `C(K, ℝ)` of continuous
real-valued functions equipped with the supremum norm and the pointwise order
is a Banach lattice.
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

/-! ### AM-space with unit -/

omit [CompactSpace K] in
private theorem mul_eq_zero_of_inf_eq_zero {f g : C(K, ℝ)}
    (hfg : f ⊓ g = 0) : f * g = 0 := by
  ext t
  have ht := congrArg (fun h : C(K, ℝ) => h t) hfg
  change min (f t) (g t) = 0 at ht
  rcases le_total (f t) (g t) with h | h
  · have : f t = 0 := by simpa [min_eq_left h] using ht
    simp [this]
  · have : g t = 0 := by simpa [min_eq_right h] using ht
    simp [this]

private theorem one_strongOrderUnit : StrongOrderUnit (1 : C(K, ℝ)) := by
  refine ⟨?_, fun f => ⟨‖f‖, norm_nonneg f, ?_⟩⟩
  · rw [ContinuousMap.le_def]
    intro t
    simp
  rw [ContinuousMap.le_def]
  intro t
  simpa [ContinuousMap.abs_apply, ContinuousMap.smul_apply, Real.norm_eq_abs] using
    ContinuousMap.norm_coe_le_norm f t

private theorem norm_eq_gaugeNorm_one (f : C(K, ℝ)) :
    ‖f‖ = OrderIdeal.gaugeNorm (1 : C(K, ℝ)) f := by
  have hf : f ∈ OrderIdeal.principal (1 : C(K, ℝ)) := by
    refine ⟨‖f‖, norm_nonneg f, ?_⟩
    rw [ContinuousMap.le_def]
    intro t
    simpa [ContinuousMap.abs_apply, ContinuousMap.smul_apply, Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm f t
  apply le_antisymm
  · apply (ContinuousMap.norm_le f (OrderIdeal.gaugeNorm_nonneg 1 f)).mpr
    intro t
    have ht := ContinuousMap.le_def.mp
      (OrderIdeal.abs_le_gaugeNorm_smul_abs (1 : C(K, ℝ)) hf) t
    simpa [ContinuousMap.abs_apply, ContinuousMap.smul_apply, Real.norm_eq_abs] using ht
  · apply OrderIdeal.gaugeNorm_le_of_abs_le 1 (norm_nonneg f)
    rw [ContinuousMap.le_def]
    intro t
    simpa [ContinuousMap.abs_apply, ContinuousMap.smul_apply, Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm f t

/-- With the constant-one function as its distinguished unit, `C(K, ℝ)` is an
AM-space with unit. -/
noncomputable instance instAMSpaceWithUnitCofK : AMSpaceWithUnit C(K, ℝ) where
  norm_add_eq_max_of_inf_eq_zero hfg :=
    ContinuousMap.norm_add_eq_max (mul_eq_zero_of_inf_eq_zero hfg)
  unit := 1
  strongOrderUnit_unit := one_strongOrderUnit
  norm_eq_gaugeNorm := norm_eq_gaugeNorm_one
