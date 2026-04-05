import BanLat.Banach
import BanLat.Band

/-!
# Order continuous norms

A normed vector lattice has an **order continuous norm** when every decreasing
sequence of non-negative elements with infimum zero converges to zero in norm.
Equivalently, every increasing positive sequence whose supremum exists converges
in norm to that supremum.

The main results stated here are:
- Equivalent characterisations of an order continuous norm for sequences.
- The Meyer-Nieberg theorem: a Banach lattice is order continuous iff every
  order-bounded pairwise disjoint sequence converges to zero in norm.
- Ando's theorem: a Banach lattice is order continuous iff every norm-closed
  ideal is a band.
-/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-! ### Definition -/

/-- A normed vector lattice has an **order continuous norm** if every antitone
sequence of non-negative elements with greatest lower bound zero converges to
zero in norm. -/
class IsOrderContinuousNorm (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {u : ℕ → X}, Antitone u → (∀ n, 0 ≤ u n) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

namespace IsOrderContinuousNorm

variable [NormedVectorLattice X] [IsOrderContinuousNorm X]

/-! ### Equivalent characterisations -/

/-- An increasing sequence with a least upper bound converges in norm to
that bound. -/
theorem tendsto_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := sorry

/-- An antitone sequence with a greatest lower bound converges in norm to
that bound. -/
theorem tendsto_of_antitone_isGLB {u : ℕ → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := sorry

/-- The norm is σ-order continuous: if `|u n - x| ≤ v n` for an antitone
sequence `v` with `inf v = 0`, then `u n → x` in norm. -/
theorem tendsto_of_abs_sub_le_antitone {u : ℕ → X} {v : ℕ → X} {x : X}
    (hv_anti : Antitone v) (hv_nn : ∀ n, 0 ≤ v n)
    (hv_glb : IsGLB (Set.range v) 0)
    (hle : ∀ n, |u n - x| ≤ v n) :
    Filter.Tendsto u Filter.atTop (nhds x) := sorry

/-- The norm itself is an order continuous function on positive elements:
if `0 ≤ u n` for all `n`, `u n` converges in order to `x`, then
`‖u n‖ → ‖x‖`. -/
theorem tendsto_norm_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u) (hnn : ∀ n, 0 ≤ u n)
    (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖x‖) := sorry

end IsOrderContinuousNorm

/-! ### Order continuity in Banach lattices -/

namespace BanachLattice

variable [BanachLattice X]

/-! #### Meyer-Nieberg theorem -/

/-- In an order continuous Banach lattice, every order-bounded pairwise
disjoint sequence converges to zero in norm. -/
theorem disjoint_bddAbove_tendsto_zero [IsOrderContinuousNorm X]
    {u : ℕ → X} (hd : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := sorry

/-- A Banach lattice whose order-bounded pairwise disjoint sequences all
converge to zero in norm has an order continuous norm. -/
theorem isOrderContinuousNorm_of_disjoint_tendsto_zero
    (h : ∀ {u : ℕ → X},
      Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
      BddAbove (Set.range fun n => |u n|) →
      Filter.Tendsto u Filter.atTop (nhds 0)) :
    IsOrderContinuousNorm X := sorry

/-- **Meyer-Nieberg theorem**: a Banach lattice has an order continuous norm
iff every order-bounded pairwise disjoint sequence converges to zero. -/
theorem isOrderContinuousNorm_iff_disjoint_tendsto_zero :
    IsOrderContinuousNorm X ↔
      (∀ {u : ℕ → X},
        Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
        BddAbove (Set.range fun n => |u n|) →
        Filter.Tendsto u Filter.atTop (nhds 0)) := sorry

/-! #### Ando's theorem -/

/-- In an order continuous Banach lattice, every norm-closed order ideal is
a band. -/
theorem band_of_isClosed_orderIdeal [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ B : Band X, (B : Set X) = (J : Set X) := sorry

/-- A Banach lattice in which every norm-closed ideal is a band has an order
continuous norm. -/
theorem isOrderContinuousNorm_of_isClosed_ideal_isBand
    (h : ∀ J : OrderIdeal X, IsClosed (J : Set X) →
      ∃ B : Band X, (B : Set X) = (J : Set X)) :
    IsOrderContinuousNorm X := sorry

/-- **Ando's theorem**: a Banach lattice has an order continuous norm iff
every norm-closed ideal is a band. -/
theorem isOrderContinuousNorm_iff_isClosed_ideal_isBand :
    IsOrderContinuousNorm X ↔
      (∀ J : OrderIdeal X, IsClosed (J : Set X) →
        ∃ B : Band X, (B : Set X) = (J : Set X)) := sorry

/-- In an order continuous Banach lattice, every norm-closed ideal is a
projection band. -/
theorem projectionBand_of_isClosed_orderIdeal
    [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ P : ProjectionBand X, (P : Set X) = (J : Set X) := sorry

end BanachLattice
