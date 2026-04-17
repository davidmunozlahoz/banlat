import BanLat.Operators.Regular
import BanLat.Sublattice

/-!
# Extension theorems for operators and functionals

This file states the main Hahn-Banach-type extension theorems for linear
operators and functionals in vector and Banach lattices: extending operators
dominated by sublinear maps into order complete vector lattices, sandwich
extensions for positive operators, and norm-preserving extension of positive
functionals.
-/

open Set

/-! ### Sublinear maps -/

/-- A map from a real vector space into a vector lattice is **sublinear** if
it is subadditive and positively homogeneous. -/
structure IsSublinearMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (p : E → X) : Prop where
  sub_add : ∀ x y, p (x + y) ≤ p x + p y
  pos_homog : ∀ (r : ℝ), 0 ≤ r → ∀ x, p (r • x) = r • p x

/-! ## Hahn-Banach extension theorems -/

/-- **Hahn-Banach for vector lattices**: a linear operator from a subspace
into an order complete vector lattice, dominated by a sublinear map, extends
to the whole space while remaining dominated. -/
theorem exists_extension_le_sublinear
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] [IsOrderComplete X]
    (F : Submodule ℝ E) (p : E → X) (T : F →ₗ[ℝ] X)
    (hp : IsSublinearMap p)
    (hT : ∀ x : F, T x ≤ p (x : E)) :
    ∃ T' : E →ₗ[ℝ] X,
      (∀ x : F, T' (x : E) = T x) ∧
      (∀ x : E, T' x ≤ p x) := sorry

/-- **Hahn-Banach for operators**: a positive operator on a sublattice,
sandwiched between zero and a positive operator on the whole space, extends
to a positive operator still dominated by the upper bound. -/
theorem exists_positive_extension_of_sandwich
    {X Z : Type*} [AddCommGroup X] [AddCommGroup Z]
    [Lattice X] [Lattice Z]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Z]
    [VectorLattice X] [VectorLattice Z] [IsOrderComplete Z]
    (Y : VectorSublattice X)
    (S : Y.toSubmodule →ₗ[ℝ] Z) (T : X →ₗ[ℝ] Z)
    (hS : ∀ y : Y.toSubmodule, 0 ≤ (y : X) → 0 ≤ S y)
    (hT : Positive T)
    (hST : ∀ y : Y.toSubmodule,
      0 ≤ (y : X) → S y ≤ T (y : X)) :
    ∃ S' : X →ₗ[ℝ] Z, Positive S' ∧
      (∀ x : X, 0 ≤ x → S' x ≤ T x) ∧
      (∀ y : Y.toSubmodule, S' (y : X) = S y) := sorry

/-- **Hahn-Banach for positive functionals**: a bounded positive functional
on a sublattice of a normed lattice extends to a positive functional on the
whole space, preserving the operator norm bound. -/
theorem exists_positive_functional_extension
    {X : Type*} [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X]
    (Y : VectorSublattice X)
    (f : Y.toSubmodule →ₗ[ℝ] ℝ)
    (hf : ∀ y : Y.toSubmodule, 0 ≤ (y : X) → 0 ≤ f y)
    {C : ℝ} (hC : 0 ≤ C)
    (hfbd : ∀ y : Y.toSubmodule,
      ‖f y‖ ≤ C * ‖(y : X)‖) :
    ∃ g : X →ₗ[ℝ] ℝ,
      (∀ x : X, 0 ≤ x → 0 ≤ g x) ∧
      (∀ y : Y.toSubmodule, g (y : X) = f y) ∧
      (∀ x : X, ‖g x‖ ≤ C * ‖x‖) := sorry
