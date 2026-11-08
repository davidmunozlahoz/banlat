/-
Authors: Pedro Tradacete
-/

import BanLat.OrderContinuous.OrderIntervalCompactness

/-!
# KB-spaces and their canonical bidual images

A KB-space is a Banach lattice in which every increasing norm-bounded positive net
converges in norm. Such a space has order continuous norm, and its canonical image
in the bidual is a band. Conversely, a band canonical bidual image implies the KB
property.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

universe u

/-- A KB-space is a Banach lattice in which increasing norm-bounded positive nets
converge in norm. Index sets lie in the same universe as the space. -/
class IsKbSpace (X : Type u) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] : Prop where
  tendsto_of_monotone_of_isBounded :
    ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {f : ι → X}, Monotone f → (∀ i, 0 ≤ f i) → Bornology.IsBounded (range f) →
      ∃ x, Tendsto f atTop (𝓝 x)

namespace IsKbSpace

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- Increasing norm-bounded positive sequences in a KB-space converge in norm;
lifting the index type allows the net axiom to apply in any universe. -/
private lemma exists_tendsto_seq [IsKbSpace X] {f : ℕ → X}
    (hf : Monotone f) (hpos : ∀ n, 0 ≤ f n) (hb : Bornology.IsBounded (range f)) :
    ∃ x, Tendsto f atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := tendsto_of_monotone_of_isBounded
    (f := fun n : ULift.{u} ℕ ↦ f n.down) (fun _ _ h ↦ hf h)
    (fun n ↦ hpos n.down) (hb.subset (range_comp_subset_range ULift.down f))
  exact ⟨x, hx.comp (ULift.orderIso (α := ℕ)).symm.tendsto_atTop⟩

/-- Every increasing order-bounded sequence in a KB-space converges in norm to its
supremum, after translation by its first term to obtain a positive sequence. -/
private lemma exists_tendsto_seq_of_bddAbove [IsKbSpace X] {f : ℕ → X}
    (hf : Monotone f) (hb : BddAbove (range f)) :
    ∃ x, IsLUB (range f) x ∧ Tendsto f atTop (𝓝 x) := by
  obtain ⟨b, hb⟩ := hb
  have hpos (n : ℕ) : 0 ≤ f n - f 0 := sub_nonneg.mpr (hf (Nat.zero_le n))
  have hbounded : Bornology.IsBounded (range (fun n ↦ f n - f 0)) :=
    NormedVectorLattice.isBounded_of_bddBelow_bddAbove
      ⟨0, fun _ ⟨n, hn⟩ ↦ hn ▸ hpos n⟩
      ⟨b - f 0, fun _ ⟨n, hn⟩ ↦ hn ▸ sub_le_sub_right (hb (mem_range_self n)) _⟩
  obtain ⟨x, hx⟩ := exists_tendsto_seq (fun _ _ h ↦ sub_le_sub_right (hf h) _)
    hpos hbounded
  have ht : Tendsto f atTop (𝓝 (x + f 0)) := by
    simpa only [sub_add_cancel] using hx.add_const (f 0)
  exact ⟨_, isLUB_of_tendsto_atTop hf ht, ht⟩

/-- A KB-space has order continuous norm. -/
instance (priority := 100) toIsOrderContinuousNorm [IsKbSpace X] :
    IsOrderContinuousNorm X := by
  let : SigmaConditionallyCompleteLattice X :=
    BanachLattice.sigmaConditionallyCompleteLatticeOfMonoBddAboveTendsto
      exists_tendsto_seq_of_bddAbove
  let : IsSigmaOrderContinuousNorm X :=
    BanachLattice.isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
      exists_tendsto_seq_of_bddAbove
  exact BanachLattice.isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice

/-- In a KB-space, a norm-bounded increasing positive net has a supremum in the
canonical bidual image. -/
theorem exists_isLUB_inclusion_range [IsKbSpace X]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f : ι → X} (hf : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (hb : Bornology.IsBounded (range f)) :
    ∃ x : X, IsLUB (range (fun i ↦ BidualSpace.inclusion (f i))) (BidualSpace.inclusion x) := by
  obtain ⟨x, hx⟩ := tendsto_of_monotone_of_isBounded hf hpos hb
  exact ⟨x, isLUB_of_tendsto_atTop ((BidualSpace.inclusionVecLatHom (X := X)).monotone.comp hf)
    ((BidualSpace.inclusion (X := X)).continuous.tendsto x |>.comp hx)⟩

/-- A norm-bounded directed set of positive vectors in a KB-space has a supremum
in the canonical bidual image. -/
theorem exists_isLUB_image_inclusion [IsKbSpace X] {A : Set X}
    (hne : A.Nonempty) (hdir : DirectedOn (· ≤ ·) A) (hpos : ∀ x ∈ A, 0 ≤ x)
    (hb : Bornology.IsBounded A) :
    ∃ x : X, IsLUB (BidualSpace.inclusion '' A) (BidualSpace.inclusion x) := by
  have : Nonempty A := hne.to_subtype
  have : IsDirected A (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a a.property b b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  obtain ⟨x, hx⟩ := exists_isLUB_inclusion_range (f := fun a : A ↦ (a : X))
    (fun _ _ h ↦ h) (fun a ↦ hpos a a.property)
    (by simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using hb)
  exact ⟨x, by simpa only [← image_eq_range] using hx⟩

/-- The canonical bidual image of a KB-space contains every existing supremum of
a nonempty upward directed set of positive vectors in that image. -/
private lemma mem_range_inclusion_of_isLUB [IsKbSpace X]
    {A : Set (BidualSpace X)} (hne : A.Nonempty) (hdir : DirectedOn (· ≤ ·) A)
    (hpos : ∀ a ∈ A, 0 ≤ a) (hsub : A ⊆ range BidualSpace.inclusion)
    {z : BidualSpace X} (hz : IsLUB A z) : z ∈ range BidualSpace.inclusion := by
  let S := BidualSpace.inclusion ⁻¹' A
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨x, rfl⟩ := hsub ha
    exact ⟨x, ha⟩
  have hSdir : DirectedOn (· ≤ ·) S := by
    intro a ha b hb
    obtain ⟨c, hc, hac, hbc⟩ := hdir _ ha _ hb
    obtain ⟨x, rfl⟩ := hsub hc
    exact ⟨x, hc, BidualSpace.inclusion_le_inclusion_iff.mp hac,
      BidualSpace.inclusion_le_inclusion_iff.mp hbc⟩
  have hSpos (x : X) (hx : x ∈ S) : 0 ≤ x :=
    BidualSpace.inclusion_le_inclusion_iff.mp (by simpa using hpos _ hx)
  have hSnorm : Bornology.IsBounded S :=
    (BidualSpace.inclusionLi (X := X)).isometry.antilipschitzWith.isBounded_preimage
      (NormedVectorLattice.isBounded_of_bddBelow_bddAbove ⟨0, hpos⟩ ⟨z, hz.1⟩)
  obtain ⟨x, hx⟩ := exists_isLUB_image_inclusion hS hSdir hSpos hSnorm
  rw [image_preimage_eq_of_subset hsub] at hx
  exact ⟨x, hx.unique hz⟩

/-- The canonical bidual image of a KB-space is a band. -/
theorem exists_band_range_inclusion [IsKbSpace X] :
    ∃ B : Band (BidualSpace X), range BidualSpace.inclusion = (B : Set (BidualSpace X)) := by
  obtain ⟨J, hJ⟩ :=
    BidualSpace.isOrderContinuousNorm_iff_range_inclusion_eq_orderIdeal.mp
      (inferInstance : IsOrderContinuousNorm X)
  refine ⟨Band.ofPosDirectedSSupMem J ?_, hJ⟩
  intro A hA hpos hdir hne z hz
  have hsub : A ⊆ range BidualSpace.inclusion := hJ.symm ▸ hA
  change z ∈ (J : Set (BidualSpace X))
  exact hJ ▸ mem_range_inclusion_of_isLUB hne hdir hpos hsub hz

/-- A nonempty norm-bounded upward directed set of positive continuous functionals
has a supremum, obtained by extending its pointwise supremum on positive vectors. -/
private lemma exists_isLUB_dual_of_isBounded
    {A : Set (StrongDual ℝ X)} (hne : A.Nonempty) (hdir : DirectedOn (· ≤ ·) A)
    (hpos : ∀ φ ∈ A, 0 ≤ φ) (hb : Bornology.IsBounded A) :
    ∃ F : StrongDual ℝ X, IsLUB A F := by
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  let value (x : X) : Set ℝ := (fun f : StrongDual ℝ X ↦ f x) '' A
  let τ (x : X) : ℝ := sSup (value x)
  have hvalue (x : X) : IsLUB (value x) (τ x) := by
    have hne : (value x).Nonempty := hne.image _
    have hbdd : BddAbove (value x) := by
      refine ⟨C * ‖x‖, ?_⟩
      rintro v ⟨f, hf, rfl⟩
      calc
        f x ≤ ‖f x‖ := le_abs_self _
        _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
        _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (hC f hf) (norm_nonneg x)
    exact isLUB_csSup hne hbdd
  have hτ_nn : ∀ x : X, 0 ≤ x → 0 ≤ τ x := by
    intro x hx
    obtain ⟨f, hf⟩ := hne
    change StrongDual ℝ X at f
    have hfx : 0 ≤ f x := (StrongDual.le_iff.mp (hpos f hf)) x hx
    exact hfx.trans ((hvalue x).1 ⟨f, hf, rfl⟩)
  have hτ_add : ∀ x y : X, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y := by
    intro x y hx hy
    apply le_antisymm
    · apply (hvalue (x + y)).2
      rintro v ⟨f, hf, rfl⟩
      change f (x + y) ≤ τ x + τ y
      rw [map_add]
      exact add_le_add ((hvalue x).1 ⟨f, hf, rfl⟩)
        ((hvalue y).1 ⟨f, hf, rfl⟩)
    · have hsum : IsLUB (value x + value y) (τ x + τ y) :=
        (hvalue x).add (hvalue y)
      apply hsum.2
      rintro _ ⟨vx, ⟨f, hf, rfl⟩, vy, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨k, hk, hfk, hgk⟩ := hdir f hf g hg
      change StrongDual ℝ X at k
      have hfx : f x ≤ k x := (StrongDual.le_iff.mp hfk) x hx
      have hgy : g y ≤ k y := (StrongDual.le_iff.mp hgk) y hy
      calc
        f x + g y ≤ k x + k y := add_le_add hfx hgy
        _ = k (x + y) := (map_add k x y).symm
        _ ≤ τ (x + y) := (hvalue (x + y)).1 ⟨k, hk, rfl⟩
  let f : X →ₗ[ℝ] ℝ := Positive.extension hτ_nn hτ_add
  have hfpos : Positive f := Positive.extension_positive hτ_nn hτ_add
  let F : StrongDual ℝ X := ⟨f, Positive.continuous hfpos⟩
  have hFub : F ∈ upperBounds A := by
    intro g hg
    apply StrongDual.le_iff.mpr
    intro x hx
    change StrongDual ℝ X at g
    change g x ≤ f x
    rw [Positive.extension_nonneg hτ_nn hτ_add hx]
    exact (hvalue x).1 ⟨g, hg, rfl⟩
  have hFlub : IsLUB A F := by
    refine ⟨hFub, ?_⟩
    intro G hG
    apply StrongDual.le_iff.mpr
    intro x hx
    change StrongDual ℝ X at G
    change f x ≤ G x
    rw [Positive.extension_nonneg hτ_nn hτ_add hx]
    apply (hvalue x).2
    rintro v ⟨g, hg, rfl⟩
    exact (StrongDual.le_iff.mp (hG hg)) x hx
  exact ⟨F, hFlub⟩

/-- If the canonical bidual image is a band, every increasing norm-bounded positive
net has a supremum in the original space, obtained from its bidual supremum. -/
private lemma exists_isLUB_of_range_inclusion_eq_band
    (B : Band (BidualSpace X))
    (hB : range BidualSpace.inclusion = (B : Set (BidualSpace X)))
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f : ι → X} (hf : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (hb : Bornology.IsBounded (range f)) : ∃ x, IsLUB (range f) x := by
  let j := BidualSpace.inclusion (X := X)
  have hm : Monotone (fun i ↦ j (f i)) :=
    (BidualSpace.inclusionVecLatHom (X := X)).monotone.comp hf
  have hdir : DirectedOn (· ≤ ·) (range (fun i ↦ j (f i))) :=
    directedOn_range.mpr fun i k ↦ (exists_ge_ge i k).imp
      (fun l hl ↦ ⟨hm hl.1, hm hl.2⟩)
  have hb' : Bornology.IsBounded (range (fun i ↦ j (f i))) := by
    simpa only [← range_comp, Function.comp_def] using j.lipschitzWith.isBounded_image hb
  obtain ⟨F, hF⟩ := exists_isLUB_dual_of_isBounded (range_nonempty _) hdir
    (fun _ ⟨i, hi⟩ ↦ hi ▸ BidualSpace.inclusion_nonneg (hpos i)) hb'
  have hFB : F ∈ (B : Set (BidualSpace X)) :=
    B.sSup_mem (S := range (fun i ↦ j (f i)))
    (fun _ ⟨i, hi⟩ ↦ hi ▸ hB ▸ mem_range_self (f i)) (range_nonempty _) hF
  obtain ⟨x, rfl⟩ := hB.symm ▸ hFB
  refine ⟨x, fun _ ⟨i, hi⟩ ↦ hi ▸ BidualSpace.inclusion_le_inclusion_iff.mp
    (hF.1 (mem_range_self i)), fun y hy ↦ BidualSpace.inclusion_le_inclusion_iff.mp ?_⟩
  exact hF.2 fun _ ⟨i, hi⟩ ↦ hi ▸ BidualSpace.inclusion_le_inclusion_iff.mpr
    (hy (mem_range_self i))

/-- A Banach lattice whose canonical bidual image is a band is a KB-space. -/
theorem of_range_inclusion_eq_band
    (h : ∃ B : Band (BidualSpace X),
      range BidualSpace.inclusion = (B : Set (BidualSpace X))) : IsKbSpace X := by
  obtain ⟨B, hB⟩ := h
  let : IsOrderContinuousNorm X :=
    BidualSpace.isOrderContinuousNorm_of_range_inclusion_eq_orderIdeal ⟨B.toOrderIdeal, hB⟩
  refine ⟨fun hf hpos hb ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_isLUB_of_range_inclusion_eq_band B hB hf hpos hb
  exact ⟨x, tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
    (orderConvergesTo_of_monotone_isLUB hf hx)⟩

/-- A Banach lattice is a KB-space exactly when its canonical bidual image is a band. -/
theorem iff_range_inclusion_eq_band :
    IsKbSpace X ↔ ∃ B : Band (BidualSpace X),
      range BidualSpace.inclusion = (B : Set (BidualSpace X)) :=
  ⟨fun _ ↦ exists_band_range_inclusion, of_range_inclusion_eq_band⟩

/-- A Banach lattice with surjective canonical bidual embedding is a KB-space. -/
theorem of_surjective_inclusion (h : Function.Surjective (BidualSpace.inclusion (X := X))) :
    IsKbSpace X :=
  of_range_inclusion_eq_band ⟨⊤, Set.range_eq_univ.mpr h⟩

end IsKbSpace
