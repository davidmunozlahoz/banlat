/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Majorizing
import BanLat.Operators.OrderContinuous

/-!
# Order-continuous extensions from dense sublattices

A positive order-continuous operator on an order-dense majorizing sublattice of an
Archimedean vector lattice extends uniquely to the whole space when its codomain is
order complete. On positive elements the extension is characterized by a least upper bound.
-/

open Set

universe u v

namespace VectorSublattice

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] {Y : VectorSublattice X}

/-- If `Y` is order dense in the Archimedean space `X`, every positive `x` is the supremum
in `X` of the elements of `Y ∩ [0, x]`. -/
private lemma isLUB_positiveBelow [IsVLArchimedean X]
    (hd : Y.IsOrderDense) {x : X} (hx : 0 ≤ x) :
    IsLUB ((fun y : Y ↦ (y : X)) '' {y : Y | 0 ≤ y ∧ (y : X) ≤ x}) x := by
  refine ⟨by rintro _ ⟨y, hy, rfl⟩; exact hy.2, ?_⟩
  intro b hb
  by_contra hxb
  have hgap : 0 < x - (b ⊓ x) := sub_pos.mpr <|
    (inf_le_right : b ⊓ x ≤ x).lt_of_not_ge (fun h ↦ hxb (h.trans inf_le_left))
  obtain ⟨w, hw, hwpos, hwle⟩ := hd hgap
  have hmul : ∀ n : ℕ, n • w ≤ x := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n hn =>
      have hnb : n • w ≤ b := hb ⟨⟨n • w, Y.toSubmodule.nsmul_mem hw n⟩,
        ⟨nsmul_nonneg hwpos.le n, hn⟩, rfl⟩
      rw [succ_nsmul]
      calc n • w + w ≤ b ⊓ x + (x - (b ⊓ x)) := add_le_add (le_inf hnb hn) hwle
        _ = x := by abel
  exact hwpos.not_ge (IsVLArchimedean.le_zero_of_forall_nsmul_le hmul)

variable {Z : Type v} [AddCommGroup Z] [ConditionallyCompleteLattice Z]
  [IsOrderedAddMonoid Z] [VectorLattice Z]

private noncomputable def extensionValue (T : Y →ₗ[ℝ] Z) (x : X) : Z :=
  sSup (T '' {y : Y | 0 ≤ y ∧ (y : X) ≤ x})

private lemma extensionValue_isLUB (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) {x : X} (hx : 0 ≤ x) :
    IsLUB (T '' {y : Y | 0 ≤ y ∧ (y : X) ≤ x}) (extensionValue T x) := by
  -- Majorization supplies an upper bound in Y, where T can be evaluated.
  obtain ⟨b, hb, hxb⟩ := hm x
  apply isLUB_csSup
  · exact ⟨T 0, ⟨0, ⟨le_rfl, hx⟩, rfl⟩⟩
  · refine ⟨T ⟨b, hb⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (Positive.monotone_iff.mpr hT) (hy.2.trans hxb)

private lemma extensionValue_nonneg (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) (x : X) (hx : 0 ≤ x) : 0 ≤ extensionValue T x := by
  simpa only [map_zero] using
    (extensionValue_isLUB hm hT hx).1 ⟨0, ⟨le_rfl, hx⟩, rfl⟩

/-- If an increasing net `aᵢ` in `Y` has supremum `x` in `X` and `y ∈ Y` satisfies
`y ≤ x`, then the net `aᵢ ⊓ y` has supremum `y` in `Y`. -/
private lemma isLUB_inf_in_sublattice {ι : Type u} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {a : ι → Y} {x : X}
    (ha : Monotone a) (hx : IsLUB (range fun i ↦ (a i : X)) x)
    {y : Y} (hy : (y : X) ≤ x) : IsLUB (range fun i ↦ a i ⊓ y) y := by
  refine ⟨by rintro _ ⟨i, rfl⟩; exact inf_le_right, ?_⟩
  intro z hz
  change (y : X) ≤ (z : X)
  have hc := (orderConvergesTo_of_monotone_isLUB
    (show Monotone (fun i ↦ (a i : X)) from ha) hx).inf (orderConvergesTo_const (y : X))
  have hle := hc.le_of_forall_le (fun i ↦ show (a i : X) ⊓ (y : X) ≤ (z : X) from
    hz ⟨i, rfl⟩)
  simpa only [inf_eq_right.mpr hy] using hle

/-- If an increasing positive net in `Y` has supremum `x` in `X`, its image under the
positive order-continuous operator `T` has supremum `extensionValue T x` in `Z`. -/
private lemma extensionValue_isLUB_of_monotone (hm : Y.IsMajorizing)
    {T : Y →ₗ[ℝ] Z} (hT : Positive T) (hc : IsOrderContinuousOp T)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {a : ι → Y} (ha : Monotone a) (ha0 : ∀ i, 0 ≤ a i)
    {x : X} (hx : IsLUB (range fun i ↦ (a i : X)) x) :
    IsLUB (range fun i ↦ T (a i)) (extensionValue T x) := by
  have hx0 : 0 ≤ x := (show (0 : X) ≤ a (Classical.arbitrary ι) from ha0 _).trans
    (hx.1 ⟨_, rfl⟩)
  have hsup := extensionValue_isLUB hm hT hx0
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hsup.1 ⟨a i, ⟨ha0 i, hx.1 ⟨i, rfl⟩⟩, rfl⟩
  · intro b hb
    apply hsup.2
    rintro _ ⟨y, hy, rfl⟩
    have hconv := hc (orderConvergesTo_of_monotone_isLUB
      (fun i j hij ↦ inf_le_inf_right y (ha hij)) (isLUB_inf_in_sublattice ha hx hy.2))
    exact hconv.le_of_forall_le fun i ↦
      ((Positive.monotone_iff.mpr hT) inf_le_left).trans (hb ⟨i, rfl⟩)

-- A directed subset is used as a net with its inherited order.
private lemma extensionValue_isLUB_of_directed (hm : Y.IsMajorizing)
    {T : Y →ₗ[ℝ] Z} (hT : Positive T) (hc : IsOrderContinuousOp T)
    {s : Set Y} (hs : DirectedOn (· ≤ ·) s) (hne : s.Nonempty)
    (hpos : ∀ y ∈ s, 0 ≤ y) {x : X}
    (hx : IsLUB ((fun y : Y ↦ (y : X)) '' s) x) :
    IsLUB (T '' s) (extensionValue T x) := by
  let := hs.isDirectedOrder
  let := hne.to_subtype
  rw [image_eq_range] at hx ⊢
  exact extensionValue_isLUB_of_monotone hm hT hc (a := fun y : s ↦ (y : Y))
    (fun _ _ h ↦ h) (fun y ↦ hpos y y.2) hx

private lemma positiveBelow_directed (x : X) :
    DirectedOn (· ≤ ·) {y : Y | 0 ≤ y ∧ (y : X) ≤ x} := by
  intro a ha b hb
  exact ⟨a ⊔ b, ⟨ha.1.trans le_sup_left, sup_le ha.2 hb.2⟩, le_sup_left, le_sup_right⟩

private lemma isLUB_range_add {E : Type*} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] {ι κ : Type*} {a : ι → E} {b : κ → E} {x y : E}
    (ha : IsLUB (range a) x) (hb : IsLUB (range b) y) :
    IsLUB (range fun p : ι × κ ↦ a p.1 + b p.2) (x + y) := by
  simpa only [← image2_add, image2_range] using ha.add hb

private lemma extensionValue_add [IsVLArchimedean X] (hd : Y.IsOrderDense)
    (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z} (hT : Positive T)
    (hc : IsOrderContinuousOp T) (x y : X) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    extensionValue T (x + y) = extensionValue T x + extensionValue T y := by
  let s := {a : Y | 0 ≤ a ∧ (a : X) ≤ x}
  let t := {b : Y | 0 ≤ b ∧ (b : X) ≤ y}
  let : Nonempty s := ⟨⟨0, le_rfl, hx⟩⟩
  let : Nonempty t := ⟨⟨0, le_rfl, hy⟩⟩
  let := (positiveBelow_directed (Y := Y) x).isDirectedOrder
  let := (positiveBelow_directed (Y := Y) y).isDirectedOrder
  -- The product order allows the two approximating nets to vary independently.
  let : IsDirected (s × t) (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨i, hai, hbi⟩ := directed_of (· ≤ ·) a.1 b.1
    obtain ⟨j, haj, hbj⟩ := directed_of (· ≤ ·) a.2 b.2
    exact ⟨(i, j), ⟨hai, haj⟩, ⟨hbi, hbj⟩⟩⟩
  have hs := isLUB_positiveBelow hd hx
  have ht := isLUB_positiveBelow hd hy
  have hTs := extensionValue_isLUB hm hT hx
  have hTt := extensionValue_isLUB hm hT hy
  rw [image_eq_range] at hs ht hTs hTt
  have hsum := extensionValue_isLUB_of_monotone hm hT hc
    (a := fun p : s × t ↦ p.1.val + p.2.val)
    (fun (a b : s × t) (h : a ≤ b) ↦ add_le_add h.1 h.2)
    (fun p ↦ add_nonneg p.1.2.1 p.2.2.1)
    (isLUB_range_add hs ht)
  exact hsum.unique (by simpa only [map_add] using isLUB_range_add hTs hTt)

private lemma extensionValue_coe (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) {y : Y} (hy : 0 ≤ y) : extensionValue T y = T y := by
  apply (extensionValue_isLUB hm hT hy).unique
  refine ⟨?_, fun b hb ↦ hb ⟨y, ⟨hy, le_rfl⟩, rfl⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (Positive.monotone_iff.mpr hT) hz.2

private lemma exists_positive_extension_value [IsVLArchimedean X]
    (hd : Y.IsOrderDense) (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) (hc : IsOrderContinuousOp T) :
    ∃ S : X →ₗ[ℝ] Z, Positive S ∧ (∀ y : Y, S y = T y) ∧
      ∀ x, 0 ≤ x → S x = extensionValue T x := by
  let : IsVLArchimedean Z := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  have hnn := extensionValue_nonneg hm hT
  have hadd := extensionValue_add hd hm hT hc
  -- Positivity and additivity on the cone supply the real-linear extension.
  let S := Positive.extension hnn hadd
  refine ⟨S, Positive.extension_positive hnn hadd, ?_,
    fun _ hx ↦ Positive.extension_nonneg hnn hadd hx⟩
  intro y
  change extensionValue T ((y : X)⁺) - extensionValue T ((y : X)⁻) = T y
  change extensionValue T (y⁺ : Y) - extensionValue T (y⁻ : Y) = T y
  rw [extensionValue_coe hm hT (posPart_nonneg y),
    extensionValue_coe hm hT (negPart_nonneg y), ← map_sub, posPart_sub_negPart]

/-- For order-dense `Y`, the union of `Y ∩ [0, a i]` along an increasing positive net
with supremum `x` in `X` is nonempty, directed, and has supremum `x` in `X`. -/
private lemma positiveBelow_union [IsVLArchimedean X] (hd : Y.IsOrderDense)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {a : ι → X} (ha : Monotone a) (ha0 : ∀ i, 0 ≤ a i)
    {x : X} (hx : IsLUB (range a) x) :
    let s := {y : Y | 0 ≤ y ∧ ∃ i, (y : X) ≤ a i}
    s.Nonempty ∧ DirectedOn (· ≤ ·) s ∧ IsLUB ((fun y : Y ↦ (y : X)) '' s) x := by
  refine ⟨⟨0, le_rfl, Classical.arbitrary ι, ha0 _⟩, ?_, ?_⟩
  · rintro y ⟨hy0, i, hyi⟩ z ⟨hz0, j, hzj⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨y ⊔ z, ⟨hy0.trans le_sup_left, k,
      sup_le (hyi.trans (ha hik)) (hzj.trans (ha hjk))⟩, le_sup_left, le_sup_right⟩
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨y, ⟨_, i, hyi⟩, rfl⟩
      exact hyi.trans (hx.1 ⟨i, rfl⟩)
    · intro b hb
      apply hx.2
      rintro _ ⟨i, rfl⟩
      apply (isLUB_positiveBelow hd (ha0 i)).2
      rintro _ ⟨y, hy, rfl⟩
      exact hb ⟨y, ⟨hy.1, i, hy.2⟩, rfl⟩

/-- The positive extension given by the supremum formula sends an increasing positive net
with supremum `x` in `X` to a net with supremum `S x` in `Z`. -/
private lemma extension_preserves_isLUB [IsVLArchimedean X]
    (hd : Y.IsOrderDense) (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) (hc : IsOrderContinuousOp T) {S : X →ₗ[ℝ] Z}
    (hS : Positive S) (hext : ∀ y : Y, S y = T y)
    (hvalue : ∀ x, 0 ≤ x → S x = extensionValue T x)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {a : ι → X} (ha : Monotone a) (ha0 : ∀ i, 0 ≤ a i)
    {x : X} (hx : IsLUB (range a) x) : IsLUB (range fun i ↦ S (a i)) (S x) := by
  obtain ⟨hne, hdir, hlub⟩ := positiveBelow_union hd ha ha0 hx
  have hx0 := (ha0 (Classical.arbitrary ι)).trans (hx.1 ⟨_, rfl⟩)
  have hsup := extensionValue_isLUB_of_directed hm hT hc hdir hne (fun _ hy ↦ hy.1) hlub
  rw [← hvalue x hx0] at hsup
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (Positive.monotone_iff.mpr hS) (hx.1 ⟨i, rfl⟩)
  · intro b hb
    apply hsup.2
    rintro _ ⟨y, ⟨_, i, hyi⟩, rfl⟩
    rw [← hext y]
    exact ((Positive.monotone_iff.mpr hS) hyi).trans (hb ⟨i, rfl⟩)

omit [VectorLattice X] in
/-- If a decreasing net has infimum zero in `X`, then for each fixed `i` the tail differences
`a i - a j`, with `i ≤ j`, have supremum `a i` in `X`. -/
private lemma isLUB_sub_tail {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {a : ι → X} (ha : Antitone a) (hglb : IsGLB (range a) 0) (i : ι) :
    IsLUB (range fun j : {j : ι // i ≤ j} ↦ a i - a j) (a i) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact sub_le_self _ (hglb.1 ⟨j, rfl⟩)
  · intro b hb
    apply sub_nonpos.mp
    apply hglb.2
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact (sub_le_comm.mp (hb ⟨⟨k, hik⟩, rfl⟩)).trans (ha hjk)

private lemma orderContinuous_of_preserves_positive_isLUB {S : X →ₗ[ℝ] Z}
    (hS : Positive S)
    (hlub : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {a : ι → X}, Monotone a → (∀ i, 0 ≤ a i) →
      ∀ {x}, IsLUB (range a) x → IsLUB (range fun i ↦ S (a i)) (S x)) :
    IsOrderContinuousOp S := by
  apply ((OrderContinuousOp.characterization
    (⟨S, hS.isOrderBounded⟩ : OrderBoundedHom X Z)).out 1 2).mpr
  intro ι _ _ _ a ha ha0 hglb
  -- On a tail, subtracting a decreasing zero net gives an increasing positive net.
  let i : ι := Classical.arbitrary ι
  let κ := {j : ι // i ≤ j}
  let : Nonempty κ := ⟨⟨i, le_rfl⟩⟩
  let : IsDirected κ (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j.val k.val
    exact ⟨⟨l, j.2.trans hjl⟩, hjl, hkl⟩⟩
  have hsup := hlub (a := fun j : κ ↦ a i - a j)
    (fun (j k : κ) (h : j ≤ k) ↦ sub_le_sub_left (ha h) _)
    (fun j ↦ sub_nonneg.mpr (ha j.2)) (isLUB_sub_tail ha hglb i)
  refine ⟨by rintro _ ⟨j, rfl⟩; exact abs_nonneg _, ?_⟩
  intro b hb
  have hupper : S (a i) - b ∈ upperBounds (range fun j : κ ↦ S (a i - a j)) := by
    rintro _ ⟨j, rfl⟩
    have hbj := hb ⟨j.val, rfl⟩
    change b ≤ |S (a j)| at hbj
    rw [abs_of_nonneg (hS _ (ha0 j))] at hbj
    change S (a i - a j) ≤ S (a i) - b
    rw [map_sub]
    exact sub_le_sub_left hbj _
  exact (le_sub_self_iff _).mp (hsup.2 hupper)

/-- Every order-continuous linear extension of `T` has, at each positive `x`, the value
given by the supremum in `Z` of `T y` over `y ∈ Y ∩ [0, x]`. -/
private lemma extension_eq_value [IsVLArchimedean X]
    (hd : Y.IsOrderDense) (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) {R : X →ₗ[ℝ] Z} (hR : IsOrderContinuousOp R)
    (hext : ∀ y : Y, R y = T y) {x : X} (hx : 0 ≤ x) :
    R x = extensionValue T x := by
  let s := {y : Y | 0 ≤ y ∧ (y : X) ≤ x}
  let : Nonempty s := ⟨⟨0, le_rfl, hx⟩⟩
  let := (positiveBelow_directed (Y := Y) x).isDirectedOrder
  have hlub := isLUB_positiveBelow hd hx
  have hTlub := extensionValue_isLUB hm hT hx
  rw [image_eq_range] at hlub hTlub
  have hRc := hR (orderConvergesTo_of_monotone_isLUB
    (show Monotone (fun y : s ↦ (y.val : X)) from fun _ _ h ↦ h) hlub)
  have hTc := orderConvergesTo_of_monotone_isLUB
    (show Monotone (fun y : s ↦ T y.val) from fun _ _ h ↦
      (Positive.monotone_iff.mpr hT) h) hTlub
  exact le_antisymm (hRc.le hTc (fun y ↦ (hext y.val).le))
    (hTc.le hRc (fun y ↦ (hext y.val).ge))

/-- Veksler’s extension theorem: a positive order-continuous operator from an order-dense
majorizing sublattice of an Archimedean vector lattice into an order-complete vector lattice
has a positive order-continuous extension to the whole space. Its values at positive `x`
are the suprema in `Z` of `T y` over `y ∈ Y ∩ [0, x]`, and it is unique among all
order-continuous linear extensions. -/
theorem exists_positive_orderContinuous_extension [IsVLArchimedean X]
    (hd : Y.IsOrderDense) (hm : Y.IsMajorizing) {T : Y →ₗ[ℝ] Z}
    (hT : Positive T) (hc : IsOrderContinuousOp T) :
    ∃ S : X →ₗ[ℝ] Z, Positive S ∧ IsOrderContinuousOp S ∧
      (∀ y : Y, S y = T y) ∧
      (∀ x, 0 ≤ x → IsLUB (T '' {y : Y | 0 ≤ y ∧ (y : X) ≤ x}) (S x)) ∧
      ∀ R : X →ₗ[ℝ] Z, IsOrderContinuousOp R → (∀ y : Y, R y = T y) → R = S := by
  obtain ⟨S, hS, hext, hvalue⟩ := exists_positive_extension_value hd hm hT hc
  have hSc : IsOrderContinuousOp S := orderContinuous_of_preserves_positive_isLUB hS (by
    intro ι _ _ _ a ha ha0 x hx
    exact extension_preserves_isLUB hd hm hT hc hS hext hvalue ha ha0 hx)
  refine ⟨S, hS, hSc, hext, ?_, ?_⟩
  · intro x hx
    rw [hvalue x hx]
    exact extensionValue_isLUB hm hT hx
  · intro R hR hRe
    have hpos : ∀ z, 0 ≤ z → R z = S z := fun z hz ↦
      (extension_eq_value hd hm hT hR hRe hz).trans (hvalue z hz).symm
    ext x
    rw [← posPart_sub_negPart x, map_sub, map_sub,
      hpos _ (posPart_nonneg x), hpos _ (negPart_nonneg x)]

end VectorSublattice
