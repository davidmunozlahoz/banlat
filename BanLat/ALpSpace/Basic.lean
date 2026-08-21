import BanLat.Disjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# ALₚ-spaces

Let `1 ≤ p < ∞`.

An **ALₚ-space** is a Banach lattice whose norm satisfies the ALₚ-axiom:
`‖x + y‖^p = ‖x‖^p + ‖y‖^p` for all `x, y` with `x ⊓ y = 0`.
-/

open scoped ENNReal NNReal BigOperators

/-! ### ALₚ-spaces -/

/-- An **ALₚ-space** is a Banach lattice whose norm is `p`-additive on
disjoint elements: if `x ⊓ y = 0`, then `‖x + y‖^p = ‖x‖^p + ‖y‖^p`. -/
class ALpSpace (p : ℝ≥0) (X : Type*) [Fact (1 ≤ p)]
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    extends BanachLattice X where
  norm_add_rpow_eq_of_isVLDisjoint {x y : X}
      (hxy : IsVLDisjoint x y) :
    ‖x + y‖ ^ (p : ℝ) = ‖x‖ ^ (p : ℝ) + ‖y‖ ^ (p : ℝ)

namespace ALpSpace

variable {p : ℝ≥0} {X : Type*} [Fact (1 ≤ p)]
  [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [ALpSpace p X]

private lemma isVLDisjoint_finset_sum
    {ι : Type*} {s : Finset ι} {x : X} {f : ι → X}
    (h : ∀ i ∈ s, IsVLDisjoint x (f i)) :
    IsVLDisjoint x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right x
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add_right
      (ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

/-- The definition of `ALₚ`-space can be generalized to finite families
of pairwise lattice-disjoint elements. -/
theorem norm_sum_rpow_eq_sum_norm_rpow_of_pairwise_isVLDisjoint
    {ι : Type*} (s : Finset ι) (x : ι → X)
    (hdisj : (s : Set ι).Pairwise fun i j ↦
      IsVLDisjoint (x i) (x j)) :
    ‖∑ i ∈ s, x i‖ ^ (p : ℝ) =
      ∑ i ∈ s, ‖x i‖ ^ (p : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, norm_zero]
    exact Real.zero_rpow (NNReal.coe_ne_zero.mpr
      (lt_of_lt_of_le zero_lt_one Fact.out).ne')
  | @insert a s ha ih =>
    have hdisj_s : (s : Set ι).Pairwise fun i j ↦ IsVLDisjoint (x i) (x j) :=
      fun i hi j hj hij ↦ hdisj (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_of_mem hj) hij
    have hhead : IsVLDisjoint (x a) (∑ i ∈ s, x i) := by
      apply isVLDisjoint_finset_sum
      intro i hi
      exact hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun hai ↦ ha (hai ▸ hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      norm_add_rpow_eq_of_isVLDisjoint hhead, ih hdisj_s]

/-- If a pairwise disjoint family in an ALₚ-space has unconditional sum `y`,
then its `p`-th norm powers are summable and their sum is `‖y‖^p`. -/
theorem HasSum.norm_rpow_of_pairwise_isVLDisjoint
    {ι : Type*} {x : ι → X} {y : X}
    (hxy : HasSum x y)
    (hdisj : Pairwise fun i j ↦ IsVLDisjoint (x i) (x j)) :
    HasSum (fun i ↦ ‖x i‖ ^ (p : ℝ)) (‖y‖ ^ (p : ℝ)) := by
  rw [HasSum] at hxy ⊢
  convert hxy.norm.rpow_const (Or.inr (NNReal.coe_nonneg p)) using 1
  funext s
  symm
  apply norm_sum_rpow_eq_sum_norm_rpow_of_pairwise_isVLDisjoint
  intro i _ j _ hij
  exact hdisj hij

end ALpSpace
