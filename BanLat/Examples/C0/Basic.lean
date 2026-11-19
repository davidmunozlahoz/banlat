/-
Authors: Pedro Tradacete
-/

import BanLat.Normed
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Real continuous functions vanishing at infinity

The supremum norm and pointwise order make `C₀(α, ℝ)` a Banach lattice. For
`α = ℕ` with its discrete topology, this is the classical null-sequence space `c₀`.
-/

noncomputable section

open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α : Type*} [TopologicalSpace α]

/-- Real continuous functions vanishing at infinity carry the pointwise lattice order. -/
instance instLatticeReal : Lattice C₀(α, ℝ) where
  le f g := ∀ x, f x ≤ g x
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh x := (hfg x).trans (hgh x)
  le_antisymm _ _ hfg hgf := ext fun x ↦ le_antisymm (hfg x) (hgf x)
  sup f g := ⟨f.toContinuousMap ⊔ g.toContinuousMap,
    (sup_idem (0 : ℝ)) ▸ (zero_at_infty f).sup_nhds (zero_at_infty g)⟩
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ hfh hgh x := sup_le (hfh x) (hgh x)
  inf f g := ⟨f.toContinuousMap ⊓ g.toContinuousMap,
    (inf_idem (0 : ℝ)) ▸ (zero_at_infty f).inf_nhds (zero_at_infty g)⟩
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ hfg hfh x := le_inf (hfg x) (hfh x)

/-- Addition preserves the pointwise order on real functions vanishing at infinity. -/
instance instIsOrderedAddMonoidReal : IsOrderedAddMonoid C₀(α, ℝ) where
  add_le_add_left _ _ h k x := add_le_add_left (h x) (k x)

/-- Real functions vanishing at infinity form a vector lattice under pointwise operations. -/
instance instVectorLatticeReal : VectorLattice C₀(α, ℝ) where
  smul_le_smul_of_nonneg_left {_} ha {_ _} hfg x := smul_le_smul_of_nonneg_left (hfg x) ha

/-- The supremum norm on real functions vanishing at infinity is solid. -/
instance instHasSolidNormReal : HasSolidNorm C₀(α, ℝ) where
  solid {f g} h :=
    (BoundedContinuousFunction.norm_le (norm_nonneg g.toBCF)).mpr fun x ↦
      (HasSolidNorm.solid (show |f x| ≤ |g x| from h x)).trans (g.toBCF.norm_coe_le_norm x)

/-- Real functions vanishing at infinity form a normed vector lattice. -/
instance instNormedVectorLatticeReal : NormedVectorLattice C₀(α, ℝ) where

/-- Real functions vanishing at infinity form a Banach lattice. -/
instance instBanachLatticeReal : BanachLattice C₀(α, ℝ) where

variable [DiscreteTopology α]

/-- Interprets a finitely supported function on a discrete space `f : α →₀ ℝ` as an element
of `C₀(α, ℝ)`. -/
def ofFinsupp (f : α →₀ ℝ) : C₀(α, ℝ) where
  toContinuousMap := ⟨f, continuous_of_discreteTopology⟩
  zero_at_infty' := (HasCompactSupport.of_support_subset_isCompact
    f.hasFiniteSupport.isCompact (Set.Subset.refl _)).is_zero_at_infty

/-- A function with finite support when considered as a function vanishing at infinity takes
the same values. -/
@[simp]
theorem ofFinsupp_apply (f : α →₀ ℝ) (x : α) : ofFinsupp f x = f x := rfl

/-- The inclusion of finitely supported functions into functions vanishing at infinity is linear. -/
def ofFinsuppLinear : (α →₀ ℝ) →ₗ[ℝ] C₀(α, ℝ) where
  toFun := ofFinsupp
  map_add' _ _ := ext fun _ ↦ rfl
  map_smul' _ _ := ext fun _ ↦ rfl

/-- The inclusion of finitely supported functions into functions vanishing at infinity preserves
absolute values pointwise. -/
@[simp]
theorem ofFinsupp_abs (f : α →₀ ℝ) : ofFinsupp |f| = |ofFinsupp f| := rfl

/-- Truncating a function on a finite set has supremum norm bounded by the uniform bound
for its values outside that set. -/
private lemma norm_sub_ofFinsupp_sum_le (f : C₀(α, ℝ)) (s : Finset α)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ x ∉ s, ‖f x‖ ≤ ε) :
    ‖f - ofFinsupp (∑ x ∈ s, Finsupp.single x (f x))‖ ≤ ε := by
  classical
  apply (BoundedContinuousFunction.norm_le hε).mpr
  intro x
  change ‖f x - (∑ y ∈ s, Finsupp.single y (f y)) x‖ ≤ ε
  by_cases hx : x ∈ s
  · simpa [Finset.sum_apply, Finsupp.single_apply, hx] using hε
  · simpa [Finset.sum_apply, Finsupp.single_apply, hx] using h x hx

/-- Finitely supported real functions are dense among functions vanishing at infinity
on a discrete space. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (α := α)) := by
  classical
  intro f
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hev : ∀ᶠ x in Filter.cofinite, ‖f x‖ < ε / 2 := by
    simpa only [Filter.cocompact_eq_cofinite, dist_zero_right] using
      Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (half_pos hε)
  let s := (Filter.eventually_cofinite.mp hev).toFinset
  refine ⟨ofFinsupp (∑ x ∈ s, Finsupp.single x (f x)), ⟨_, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  refine (norm_sub_ofFinsupp_sum_le f s (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  intro x hx
  exact le_of_lt (by simpa [s] using hx)

end ZeroAtInftyContinuousMap
