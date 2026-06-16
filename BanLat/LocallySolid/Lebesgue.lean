import BanLat.LocallySolid.Basic

/-!
# Lebesgue properties of locally solid vector lattices

This file defines the Lebesgue, sigma-Lebesgue, and pre-Lebesgue properties for locally solid
vector lattices.
-/

open scoped Topology

section Definitions

variable (E : Type*) [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [VectorLattice E] [TopologicalSpace E] [IsLocallySolidVectorLattice E]

/-- A locally solid vector lattice has the **Lebesgue property** if every antitone net of
non-negative elements with greatest lower bound zero converges topologically to zero. -/
class IsLebesgueTopology : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → E}, Antitone u → (∀ i, 0 ≤ u i) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- A locally solid vector lattice has the **sigma-Lebesgue property** if every antitone sequence
of non-negative elements with greatest lower bound zero converges topologically to zero. -/
class IsSigmaLebesgueTopology : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {u : ℕ → E}, Antitone u → (∀ n, 0 ≤ u n) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- A locally solid vector lattice has the **pre-Lebesgue property** if every increasing
order-bounded positive net is Cauchy for the canonical uniformity induced by the topological
additive group structure. -/
class IsPreLebesgueTopology : Prop where
  cauchy_of_monotone_bddAbove :
    ∀ {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → E}, Monotone u → (∀ i, 0 ≤ u i) → BddAbove (Set.range u) →
      letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      Cauchy (Filter.map u Filter.atTop)

end Definitions
