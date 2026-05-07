import BanLat.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Normed vector lattices and Banach lattices

A **normed vector lattice** is a real vector lattice whose norm satisfies the solid
axiom: `|x| ≤ |y|` implies `‖x‖ ≤ ‖y‖`. This single condition encodes compatibility
between the norm and the lattice structure. A **Banach lattice** is a normed vector
lattice whose norm is complete.

The main structural consequences proved here are:
- Lattice operations `⊔`, `⊓`, and `|·|` are norm-continuous.
- Every normed vector lattice is Archimedean.
- The positive cone is norm-closed; in particular, inequalities are preserved under
  norm convergence.
- Every order interval is closed and norm-bounded.
- Monotone Convergence: a monotone sequence that converges in norm converges to its
  supremum; dually for antitone sequences.

The final section introduces the `BanachLattice` class.
-/

/-- A normed vector lattice is a real vector lattice equipped with a lattice norm:
a norm satisfying `|x| ≤ |y| → ‖x‖ ≤ ‖y‖`. -/
class NormedVectorLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends VectorLattice X, HasSolidNorm X, NormSMulClass ℝ X

namespace NormedVectorLattice

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

instance instNormedSpace : NormedSpace ℝ X where
  norm_smul_le a x := (norm_smul a x).le

/-! ### Continuity of lattice operations -/

/-- Supremum is jointly norm-continuous. -/
theorem continuous_sup : Continuous (fun p : X × X => p.1 ⊔ p.2) :=
  ContinuousSup.continuous_sup

/-- Infimum is jointly norm-continuous. -/
theorem continuous_inf : Continuous (fun p : X × X => p.1 ⊓ p.2) :=
  ContinuousInf.continuous_inf

/-- The absolute value map is Lipschitz with constant 1; in particular it is continuous. -/
theorem lipschitzWith_abs : LipschitzWith 1 (|·| : X → X) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    exact norm_abs_sub_abs a b

/-- The norm of the positive part is bounded by the norm. -/
theorem norm_posPart_le (x : X) : ‖x⁺‖ ≤ ‖x‖ := by
  refine norm_le_norm_of_abs_le_abs ?_
  rw [abs_of_nonneg (posPart_nonneg x)]
  exact posPart_le_abs x

/-! ### Archimedean property -/

/-- Every normed vector lattice is Archimedean in the vector-lattice sense: the only
non-negative element all of whose multiples are bounded is zero. -/
instance instIsVLArchimedean : IsVLArchimedean X where
  eq_zero_of_nonneg_of_forall_nsmul_le {x y} hx h := by
    by_contra hne
    have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_lt_nsmul hxpos ‖y‖
    have h1 : ‖n • x‖ ≤ ‖y‖ := by
      apply norm_le_norm_of_abs_le_abs
      calc |n • x| = n • x := abs_of_nonneg (nsmul_nonneg hx n)
        _ ≤ y := h n
        _ ≤ |y| := le_abs_self y
    rw [show (n • x : X) = (↑n : ℝ) • x from (Nat.cast_smul_eq_nsmul ℝ n x).symm,
        norm_smul, Real.norm_natCast] at h1
    simp only [nsmul_eq_mul] at hn
    linarith

/-! ### Closed positive cone and order topology -/

/-- The order relation is closed in a normed vector lattice. -/
instance instOrderClosedTopology : OrderClosedTopology X :=
  HasSolidNorm.orderClosedTopology

/-- The positive cone `{x | 0 ≤ x}` is norm-closed. -/
theorem isClosed_nonneg_cone : IsClosed {x : X | 0 ≤ x} := isClosed_nonneg

/-- Inequalities are preserved under norm limits: if `u n ≤ v n` for all `n`, and
`u n → a`, `v n → b` in norm, then `a ≤ b`. -/
theorem le_of_tendsto_of_tendsto {u v : ℕ → X} {a b : X}
    (hu : Filter.Tendsto u Filter.atTop (nhds a))
    (hv : Filter.Tendsto v Filter.atTop (nhds b))
    (h : ∀ n, u n ≤ v n) : a ≤ b :=
  le_of_tendsto_of_tendsto' hu hv h

/-! ### Monotone Convergence Lemma -/

/-- Monotone Convergence Lemma: an increasing sequence converging in norm is a least
upper bound for its range. -/
theorem isLUB_of_monotone_tendsto {u : ℕ → X} {l : X}
    (hmono : Monotone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsLUB (Set.range u) l :=
  isLUB_of_tendsto_atTop hmono hlim

/-- Antitone Convergence Lemma: a decreasing sequence converging in norm is a greatest
lower bound for its range. -/
theorem isGLB_of_antitone_tendsto {u : ℕ → X} {l : X}
    (hanti : Antitone u) (hlim : Filter.Tendsto u Filter.atTop (nhds l)) :
    IsGLB (Set.range u) l :=
  isGLB_of_tendsto_atTop hanti hlim

/-! ### Closed and bounded intervals -/

/-- Order intervals are norm-closed. -/
theorem isClosed_interval (a b : X) : IsClosed (Set.Icc a b) := isClosed_Icc

/-- Every element `x ∈ [a, b]` satisfies `‖x‖ ≤ ‖|a| ⊔ |b|‖`. In particular, every
order interval is norm-bounded. -/
theorem norm_le_norm_abs_sup_abs_of_mem_Icc {a b x : X} (hx : x ∈ Set.Icc a b) :
    ‖x‖ ≤ ‖|a| ⊔ |b|‖ := by
  rw [← norm_abs_eq_norm x]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (le_sup_of_le_left (abs_nonneg a))]
  rw [abs]
  apply sup_le
  · -- goal: |x| ≤ |a| ⊔ |b|
    rw [abs]
    apply sup_le
    · exact le_trans hx.2 (le_trans (le_abs_self b) le_sup_right)
    · exact le_trans (neg_le_neg hx.1) (le_trans (neg_le_abs a) le_sup_left)
  · -- goal: -|x| ≤ |a| ⊔ |b|
    exact le_trans (neg_nonpos_of_nonneg (abs_nonneg x))
      (le_sup_of_le_left (abs_nonneg a))

/-- Order-bounded sets are norm-bounded. -/
theorem isBounded_of_bddBelow_bddAbove {s : Set X}
    (hl : BddBelow s) (hu : BddAbove s) : Bornology.IsBounded s := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hu
  rw [Metric.isBounded_iff_subset_closedBall (0 : X)]
  exact ⟨‖|a| ⊔ |b|‖, fun x hx => by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_norm_abs_sup_abs_of_mem_Icc ⟨ha hx, hb hx⟩⟩

end NormedVectorLattice

/-!
## Banach lattices
-/

/-- A Banach lattice is a normed vector lattice with a complete norm. -/
class BanachLattice (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends NormedVectorLattice X, CompleteSpace X

/-- `ℝ` as a Banach lattice -/
noncomputable instance : VectorLattice ℝ where

noncomputable instance : NormedVectorLattice ℝ where

noncomputable instance : BanachLattice ℝ where
