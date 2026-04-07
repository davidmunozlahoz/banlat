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

omit [VectorLattice X] in
/-- In a vector lattice, order completeness is equivalent to every bounded
above non-empty subset of the positive cone having a supremum. -/
theorem isOrderComplete_iff_pos_bddAbove_isLUB :
    IsOrderComplete X ↔
    (∀ {S : Set X}, S ⊆ {x | 0 ≤ x} → BddAbove S → S.Nonempty →
      ∃ x, IsLUB S x) := by
  refine ⟨fun _ _ _ hb hne ↦ IsOrderComplete.isLUB_of_bddAbove hb hne, fun H ↦ ?_⟩
  refine ⟨fun {S} hb hne ↦ ?_⟩
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨b, hb'⟩ := hb
  set T : Set X := (fun s ↦ (s ⊔ s₀) - s₀) '' S with hT_def
  have hTpos : T ⊆ {x | 0 ≤ x} := by
    rintro _ ⟨s, _, rfl⟩
    exact sub_nonneg.mpr le_sup_right
  have hTbdd : BddAbove T := by
    refine ⟨(b ⊔ s₀) - s₀, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact sub_le_sub_right (sup_le_sup_right (hb' hs) _) _
  have hTne : T.Nonempty := ⟨0, s₀, hs₀, by simp⟩
  obtain ⟨y, hy⟩ := H hTpos hTbdd hTne
  refine ⟨y + s₀, ?_, ?_⟩
  · intro s hs
    have h1 : (s ⊔ s₀) - s₀ ≤ y := hy.1 ⟨s, hs, rfl⟩
    have h2 : s ⊔ s₀ ≤ y + s₀ := sub_le_iff_le_add.mp h1
    exact le_sup_left.trans h2
  · intro u hu
    have hu₀ : s₀ ≤ u := hu hs₀
    have huT : u - s₀ ∈ upperBounds T := by
      rintro _ ⟨s, hs, rfl⟩
      exact sub_le_sub_right (sup_le (hu hs) hu₀) _
    exact le_sub_iff_add_le.mp (hy.2 huT)

/-! #### Sigma order completeness equivalences -/

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] in
/-- In a vector lattice, sigma order completeness is equivalent to every
increasing bounded sequence having a least upper bound. -/
theorem isSigmaOrderComplete_iff_mono_bddAbove_isLUB :
    IsSigmaOrderComplete X ↔
    (∀ {u : ℕ → X}, Monotone u → BddAbove (range u) →
      ∃ x, IsLUB (range u) x) := by
  refine ⟨fun _ _ hmono hbdd ↦
    IsSigmaOrderComplete.isLUB_of_bddAbove_countable (countable_range _) hbdd
      (range_nonempty _), fun H ↦ ?_⟩
  refine ⟨fun {S} hc hb hne ↦ ?_⟩
  obtain ⟨f, rfl⟩ := hc.exists_eq_range hne
  let u : ℕ → X := fun n ↦ Nat.rec (f 0) (fun k uk ↦ uk ⊔ f (k+1)) n
  have hmono : Monotone u :=
    monotone_nat_of_le_succ fun _ ↦ le_sup_left
  have hfle : ∀ n, f n ≤ u n := by
    intro n
    cases n with
    | zero => exact le_refl _
    | succ k => exact le_sup_right
  have hu_le : ∀ {v : X}, (∀ k, f k ≤ v) → ∀ n, u n ≤ v := by
    intro v hv n
    induction n with
    | zero => exact hv 0
    | succ k ih => exact sup_le ih (hv (k+1))
  obtain ⟨b, hbf⟩ := hb
  obtain ⟨x, hx⟩ := H hmono
    ⟨b, by rintro _ ⟨n, rfl⟩; exact hu_le (fun k ↦ hbf ⟨k, rfl⟩) n⟩
  refine ⟨x, ?_, fun v hv ↦ hx.2 ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hfle n).trans (hx.1 ⟨n, rfl⟩)
  · rintro _ ⟨n, rfl⟩
    exact hu_le (fun k ↦ hv ⟨k, rfl⟩) n

omit [VectorLattice X] in
/-- In a vector lattice, sigma order completeness is equivalent to every
decreasing bounded sequence having a greatest lower bound. -/
theorem isSigmaOrderComplete_iff_anti_bddBelow_isGLB :
    IsSigmaOrderComplete X ↔
    (∀ {u : ℕ → X}, Antitone u → BddBelow (range u) →
      ∃ x, IsGLB (range u) x) := by
  refine ⟨fun _ _ _ hbdd ↦
    isGLB_of_bddBelow_countable (countable_range _) hbdd (range_nonempty _),
    fun H ↦ isSigmaOrderComplete_iff_mono_bddAbove_isLUB.mpr fun {u} hmono hbdd ↦ ?_⟩
  obtain ⟨b, hb⟩ := hbdd
  obtain ⟨y, hy⟩ := H (u := fun n ↦ -u n)
    (fun _ _ h ↦ neg_le_neg (hmono h))
    ⟨-b, by rintro _ ⟨n, rfl⟩; exact neg_le_neg (hb ⟨n, rfl⟩)⟩
  refine ⟨-y, ?_, fun w hw ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact le_neg.mp (hy.1 ⟨n, rfl⟩)
  · have hlb : -w ∈ lowerBounds (range fun k ↦ -u k) := by
      rintro _ ⟨n, rfl⟩
      exact neg_le_neg (hw ⟨n, rfl⟩)
    exact neg_le.mp (hy.2 hlb)

omit [VectorLattice X] in
/-- In a vector lattice, sigma order completeness is equivalent to every
positive increasing bounded sequence having a least upper bound. -/
theorem isSigmaOrderComplete_iff_pos_mono_bddAbove_isLUB :
    IsSigmaOrderComplete X ↔
    (∀ {u : ℕ → X}, Monotone u → (∀ n, 0 ≤ u n) →
      BddAbove (range u) → ∃ x, IsLUB (range u) x) := by
  refine ⟨fun h _ hmono _ hbdd ↦
    isSigmaOrderComplete_iff_mono_bddAbove_isLUB.mp h hmono hbdd,
    fun H ↦ isSigmaOrderComplete_iff_mono_bddAbove_isLUB.mpr fun {u} hmono hbdd ↦ ?_⟩
  obtain ⟨b, hb⟩ := hbdd
  set v : ℕ → X := fun n ↦ u n - u 0
  have hvmono : Monotone v := fun _ _ hmn ↦ sub_le_sub_right (hmono hmn) _
  have hvpos : ∀ n, 0 ≤ v n := fun n ↦ sub_nonneg.mpr (hmono (Nat.zero_le n))
  have hvbdd : BddAbove (range v) :=
    ⟨b - u 0, by rintro _ ⟨n, rfl⟩; exact sub_le_sub_right (hb ⟨n, rfl⟩) _⟩
  obtain ⟨y, hy⟩ := H hvmono hvpos hvbdd
  refine ⟨y + u 0, ?_, fun w hw ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact sub_le_iff_le_add.mp (hy.1 ⟨n, rfl⟩)
  · have hub : w - u 0 ∈ upperBounds (range v) := by
      rintro _ ⟨n, rfl⟩
      exact sub_le_sub_right (hw ⟨n, rfl⟩) _
    exact le_sub_iff_add_le.mp (hy.2 hub)

end VectorLattice
