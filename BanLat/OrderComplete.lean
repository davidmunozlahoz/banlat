import BanLat.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Order completeness and sigma order completeness

A lattice is **order complete** (`IsOrderComplete`) if every non-empty bounded
above subset has a least upper bound. This is the `Prop`-valued analogue of
Mathlib's `ConditionallyCompleteLattice`. A weaker sequential variant is
**sigma order completeness** (`IsSigmaOrderComplete`): every non-empty bounded
above countable set has a least upper bound. The main results stated here are:
- `IsOrderComplete` is the `Prop` analogue of `ConditionallyCompleteLattice`;
  the two are equivalent for lattices.
- Order completeness implies sigma order completeness.
- Sigma order completeness implies the Archimedean property.
- Equivalent characterisations of both notions for vector lattices.
-/

open Set

/-! ### Order completeness -/

/-- A preorder is **order complete** (Dedekind complete) if every non-empty
bounded above subset has a least upper bound. -/
class IsOrderComplete (X : Type*) [Preorder X] : Prop where
  isLUB_of_bddAbove : ∀ {S : Set X}, BddAbove S → S.Nonempty → ∃ x, IsLUB S x

/-- Every non-empty bounded below set in an order complete preorder has a
greatest lower bound. -/
theorem isGLB_of_bddBelow [Preorder X] [IsOrderComplete X]
    {S : Set X} (hb : BddBelow S) (hne : S.Nonempty) :
    ∃ x, IsGLB S x := by
  obtain ⟨x, hx⟩ := IsOrderComplete.isLUB_of_bddAbove
    hne.bddAbove_lowerBounds hb
  exact ⟨x, isLUB_lowerBounds.mp hx⟩

/-- A conditionally complete lattice is order complete. -/
instance (priority := 100) ConditionallyCompleteLattice.toIsOrderComplete
    {X : Type*} [ConditionallyCompleteLattice X] :
    IsOrderComplete X :=
  ⟨fun hb hne ↦ ⟨sSup _, isLUB_csSup hne hb⟩⟩

/-- An order complete lattice carries a canonical `ConditionallyCompleteLattice`
structure. -/
noncomputable def conditionallyCompleteLatticeOfIsOrderComplete
    (X : Type*) [Lattice X] [IsOrderComplete X] [Nonempty X] :
    ConditionallyCompleteLattice X := by
  classical
  letI : SupSet X := ⟨fun S ↦
    if h : BddAbove S ∧ S.Nonempty then
      (IsOrderComplete.isLUB_of_bddAbove h.1 h.2).choose
    else Classical.arbitrary X⟩
  exact conditionallyCompleteLatticeOfLatticeOfsSup X
    fun S hb hne ↦ by
      have : sSup S =
        (IsOrderComplete.isLUB_of_bddAbove hb hne).choose :=
        dif_pos ⟨hb, hne⟩
      rw [this]
      exact (IsOrderComplete.isLUB_of_bddAbove hb hne).choose_spec


/-! ### Sigma order completeness -/

/-- A preorder is **sigma order complete** if every non-empty bounded above
countable subset has a least upper bound. -/
class IsSigmaOrderComplete (X : Type*) [Preorder X] : Prop where
  isLUB_of_bddAbove_countable :
    ∀ {S : Set X}, S.Countable → BddAbove S → S.Nonempty → ∃ x, IsLUB S x

/-- Every non-empty bounded below countable set in a sigma order complete
ordered group has a greatest lower bound. -/
theorem isGLB_of_bddBelow_countable
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [IsSigmaOrderComplete X]
    {S : Set X} (hc : S.Countable) (hb : BddBelow S) (hne : S.Nonempty) :
    ∃ x, IsGLB S x := by
  have hcn : (-S).Countable := by
    have : -S = Neg.neg '' S := by ext; simp [Set.mem_neg]
    rw [this]; exact hc.image _
  obtain ⟨x, hx⟩ := IsSigmaOrderComplete.isLUB_of_bddAbove_countable
    hcn hb.neg hne.neg
  exact ⟨-x, isLUB_neg'.mp (by rwa [neg_neg])⟩

/-! ### Implications between completeness notions -/

/-- Order completeness implies sigma order completeness. -/
instance (priority := 100) IsOrderComplete.toIsSigmaOrderComplete
    {X : Type*} [Preorder X] [IsOrderComplete X] :
    IsSigmaOrderComplete X :=
  ⟨fun _ hb hne ↦ IsOrderComplete.isLUB_of_bddAbove hb hne⟩

section LatticeOrderedGroup

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- Every sigma order complete lattice-ordered group is Archimedean in the
vector-lattice sense. -/
theorem IsVLArchimedean_of_isSigmaOrderComplete
    [IsSigmaOrderComplete X] : IsVLArchimedean X where
  eq_zero_of_nonneg_of_forall_nsmul_le {x y} hx hle := by
    obtain ⟨s, hs⟩ := IsSigmaOrderComplete.isLUB_of_bddAbove_countable
      (Set.countable_range _) ⟨y, by rintro _ ⟨n, rfl⟩; exact hle n⟩
      ⟨0, 0, by simp⟩
    have hub : s - x ∈ upperBounds (Set.range fun n : ℕ ↦ n • x) := by
      rintro _ ⟨n, rfl⟩
      have : (n + 1) • x ≤ s := hs.1 ⟨n + 1, rfl⟩
      rw [succ_nsmul] at this
      exact le_sub_iff_add_le.mpr (add_comm (n • x) x ▸ this)
    have hle0 : x ≤ 0 := by
      have h := sub_nonneg.mpr (hs.2 hub)
      rw [sub_sub_cancel_left] at h
      exact neg_nonneg.mp h
    exact le_antisymm hle0 hx

end LatticeOrderedGroup

/-! ### Characterisations for vector lattices -/

section VectorLattice

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! #### Order completeness equivalences -/

/-- In a vector lattice, order completeness is equivalent to every bounded
above non-empty subset of the positive cone having a supremum. -/
theorem isOrderComplete_iff_pos_bddAbove_isLUB :
    IsOrderComplete X ↔
    (∀ {S : Set X}, S ⊆ {x | 0 ≤ x} → BddAbove S → S.Nonempty →
      ∃ x, IsLUB S x) := sorry

/-! #### Sigma order completeness equivalences -/

/-- In a vector lattice, sigma order completeness is equivalent to every
increasing bounded sequence having a least upper bound. -/
theorem isSigmaOrderComplete_iff_mono_bddAbove_isLUB :
    IsSigmaOrderComplete X ↔
    (∀ {u : ℕ → X}, Monotone u → BddAbove (range u) →
      ∃ x, IsLUB (range u) x) := sorry

/-- In a vector lattice, sigma order completeness is equivalent to every
decreasing bounded sequence having a greatest lower bound. -/
theorem isSigmaOrderComplete_iff_anti_bddBelow_isGLB :
    IsSigmaOrderComplete X ↔
    (∀ {u : ℕ → X}, Antitone u → BddBelow (range u) →
      ∃ x, IsGLB (range u) x) := sorry

/-- In a vector lattice, sigma order completeness is equivalent to every
positive increasing bounded sequence having a least upper bound. -/
theorem isSigmaOrderComplete_iff_pos_mono_bddAbove_isLUB :
    IsSigmaOrderComplete X ↔
    (∀ {u : ℕ → X}, Monotone u → (∀ n, 0 ≤ u n) →
      BddAbove (range u) → ∃ x, IsLUB (range u) x) := sorry

end VectorLattice
