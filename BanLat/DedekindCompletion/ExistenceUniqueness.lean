/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.Construction
import BanLat.Majorizing
import BanLat.Operators.Hom
import BanLat.OrderComplete

/-!
# Existence and uniqueness of Dedekind completion

Given an Archimedean vector lattice, there is a Dedekind complete vector lattice which contains
the original as an order-dense majorizing sublattice. This embedding is constructed via Dedekind
cuts.
Any two such completions are vector-lattice isomorphic by an equivalence
that agrees with their embeddings of the original lattice. Conversely, a vector lattice that
admits a Dedekind completion is Archimedean.
-/

noncomputable section

open Set

universe u

/-- A conditionally complete vector lattice containing the original lattice
as an order-dense majorizing vector sublattice. -/
structure DedekindCompletion (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] where
  /-- The underlying type of the completion. -/
  carrier : Type u
  /-- The additive group structure on the completion. -/
  [group : AddCommGroup carrier]
  /-- The conditionally complete lattice structure on the completion. -/
  [lattice : ConditionallyCompleteLattice carrier]
  /-- Addition is compatible with the order. -/
  [ordered : IsOrderedAddMonoid carrier]
  /-- The real vector-lattice structure on the completion. -/
  [vector : VectorLattice carrier]
  /-- The vector-lattice embedding of the original lattice. -/
  inclusion : VecLatHom X carrier
  /-- The inclusion is injective. -/
  injective : Function.Injective inclusion
  /-- The image of the inclusion is order dense. -/
  dense : inclusion.range.IsOrderDense
  /-- The image of the inclusion is majorizing. -/
  majorizing : inclusion.range.IsMajorizing

attribute [instance] DedekindCompletion.group DedekindCompletion.lattice
  DedekindCompletion.ordered DedekindCompletion.vector

namespace DedekindCompletion

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- A vector lattice that admits a Dedekind completion is Archimedean. -/
theorem isVLArchimedean (D : DedekindCompletion X) : IsVLArchimedean X := by
  have : IsVLArchimedean D.carrier := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  refine ⟨fun {x y} h ↦ D.inclusion.le_of_map_le D.injective ?_⟩
  rw [map_zero]
  exact IsVLArchimedean.le_zero_of_forall_nsmul_le fun n ↦ by
    simpa only [map_nsmul] using D.inclusion.monotone (h n)

/-- The bounded-cut completion is Archimedean by conditional completeness. -/
instance [IsVLArchimedean X] : IsVLArchimedean (BoundedCut X) :=
  IsVLArchimedean_of_sigmaConditionallyCompleteLattice

/-- The Dedekind completion of an Archimedean vector lattice, constructed from bounded cuts. -/
def ofBoundedCuts [IsVLArchimedean X] : DedekindCompletion X where
  carrier := BoundedCut X
  inclusion := BoundedCut.principalHom
  injective := BoundedCut.principal_injective
  dense := BoundedCut.principal_orderDense
  majorizing A :=
    let ⟨x, hx⟩ := BoundedCut.majorizing A
    ⟨_, ⟨x, rfl⟩, hx⟩

end DedekindCompletion

/-! ### Uniqueness

Suprema of embedded elements define a canonical order isomorphism between
two order-dense majorizing completions. This isomorphism preserves addition
and real scalar multiplication, giving a vector-lattice equivalence.
-/

section Uniqueness

open scoped Pointwise

namespace DedekindCompletion

variable {X Y Z : Type u}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid Y]
  [VectorLattice Y]
  [AddCommGroup Z] [ConditionallyCompleteLattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z]

/-- Every element is the supremum of the embedded elements below it. -/
private lemma isLUB_image_below (j : VecLatHom X Y)
    (hd : j.range.IsOrderDense)
    (hm : j.range.IsMajorizing) (y : Y) :
    IsLUB (j '' {x : X | j x ≤ y}) y := by
  rw [show {x : X | j x ≤ y} = j ⁻¹' Iic y from rfl, image_preimage_eq_range_inter]
  exact j.range.isLUB_inter_Iic hd hm y

/-- Images in the target completion of original elements lying below `y` in the source. -/
private def lowerImage (j : VecLatHom X Y) (k : VecLatHom X Z) (y : Y) : Set Z :=
  {z | ∃ x : X, k x = z ∧ j x ≤ y}

/-- Majorization ensures that the set of lower images is nonempty. -/
private lemma lowerImage_nonempty (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hm : j.range.IsMajorizing) (y : Y) :
    (lowerImage j k y).Nonempty := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hm (-y)
  refine ⟨k (-x), -x, rfl, ?_⟩
  rw [map_neg]
  exact neg_le.mp hx

/-- A source majorant of `y` bounds all lower images from above. -/
private lemma lowerImage_bddAbove (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : j.range.IsMajorizing) (y : Y) :
    BddAbove (lowerImage j k y) := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hm y
  refine ⟨k x, ?_⟩
  rintro _ ⟨a, rfl, ha⟩
  exact k.monotone (j.le_of_map_le hj (ha.trans hx))

/-- The canonical candidate map between two order completions. -/
private def completionMap (j : VecLatHom X Y) (k : VecLatHom X Z) (y : Y) : Z :=
  sSup (lowerImage j k y)

/-- The completion map is the least upper bound of the lower images. -/
private lemma completionMap_isLUB (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : j.range.IsMajorizing) (y : Y) :
    IsLUB (lowerImage j k y) (completionMap j k y) :=
  isLUB_csSup (lowerImage_nonempty j k hm y)
    (lowerImage_bddAbove j k hj hm y)

/-- The completion map sends each embedded original element to its target image. -/
private lemma completionMap_principal (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : j.range.IsMajorizing) (x : X) :
    completionMap j k (j x) = k x := by
  apply IsLUB.unique (completionMap_isLUB j k hj hm (j x))
  constructor
  · rintro _ ⟨a, rfl, ha⟩
    exact k.monotone (j.le_of_map_le hj ha)
  · intro z hz
    exact hz ⟨x, rfl, le_rfl⟩

/-- The completion map is monotone. -/
private lemma completionMap_mono (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : j.range.IsMajorizing) :
    Monotone (completionMap j k) := by
  intro y₁ y₂ hle
  apply (completionMap_isLUB j k hj hm y₁).2
  rintro _ ⟨x, rfl, hx⟩
  exact (completionMap_isLUB j k hj hm y₂).1 ⟨x, rfl, hx.trans hle⟩

/-- The completion map lies below `k x` exactly when its argument lies below `j x`. -/
private lemma completionMap_le_principal (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hd : j.range.IsOrderDense)
    (hm : j.range.IsMajorizing) (y : Y) (x : X) :
    completionMap j k y ≤ k x ↔ y ≤ j x := by
  constructor
  · intro h
    apply (j.range.isLUB_inter_Iic hd hm y).2
    rintro _ ⟨⟨a, rfl⟩, ha⟩
    have hka : k a ≤ k x :=
      ((completionMap_isLUB j k hj hm y).1 ⟨a, rfl, ha⟩).trans h
    exact j.monotone (k.le_of_map_le hk hka)
  · intro h
    apply (completionMap_isLUB j k hj hm y).2
    rintro _ ⟨a, rfl, ha⟩
    exact k.monotone (j.le_of_map_le hj (ha.trans h))

/-- Completion maps in opposite directions are inverse to each other. -/
private lemma completionMap_left_inv (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) (y : Y) :
    completionMap k j (completionMap j k y) = y := by
  have hchar (x : X) :
      completionMap k j (completionMap j k y) ≤ j x ↔ y ≤ j x :=
    (completionMap_le_principal k j hk hj hdZ hmZ (completionMap j k y) x).trans
      (completionMap_le_principal j k hj hk hdY hmY y x)
  apply le_antisymm
  · apply (j.range.isGLB_inter_Ici hdY hmY y).2
    rintro _ ⟨⟨x, rfl⟩, hyx⟩
    exact (hchar x).2 hyx
  · apply (j.range.isGLB_inter_Ici hdY hmY
      (completionMap k j (completionMap j k y))).2
    rintro _ ⟨⟨x, rfl⟩, hgx⟩
    exact (hchar x).1 hgx

/-- The underlying order isomorphism between two order-dense majorizing
conditionally complete vector lattices extending the same vector lattice. -/
noncomputable def completionOrderIso (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) : Y ≃o Z where
  toFun := completionMap j k
  invFun := completionMap k j
  left_inv := completionMap_left_inv j k hj hk hdY hdZ hmY hmZ
  right_inv := completionMap_left_inv k j hk hj hdZ hdY hmZ hmY
  map_rel_iff' := by
    intro y₁ y₂
    change completionMap j k y₁ ≤ completionMap j k y₂ ↔ y₁ ≤ y₂
    constructor
    · intro h
      have h' := completionMap_mono k j hk hmZ h
      rw [completionMap_left_inv j k hj hk hdY hdZ hmY hmZ y₁,
        completionMap_left_inv j k hj hk hdY hdZ hmY hmZ y₂] at h'
      exact h'
    · intro h
      exact completionMap_mono j k hj hmY h

/-- The canonical order isomorphism agrees with the embeddings of the original lattice. -/
theorem completionOrderIso_apply_principal (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) (x : X) :
    completionOrderIso j k hj hk hdY hdZ hmY hmZ (j x) = k x :=
  completionMap_principal j k hj hmY x

/-- The canonical order isomorphism maps sums of embedded sets to their target sums. -/
private lemma image_add_principals (e : Y ≃o Z)
    (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hfix : ∀ x : X, e (j x) = k x) (S T : Set X) :
    e '' (j '' S + j '' T) = k '' S + k '' T := by
  ext z
  constructor
  · rintro ⟨w, ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    have hz : k x + k y ∈ k '' S + k '' T :=
      Set.add_mem_add ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    change e (j x + j y) ∈ k '' S + k '' T
    rw [← map_add j x y, hfix, map_add]
    exact hz
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨j x + j y, Set.add_mem_add ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, ?_⟩
    rw [← map_add j x y, hfix, map_add]

/-- The canonical order isomorphism maps an embedded set to its target image. -/
private lemma image_principals (e : Y ≃o Z)
    (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hfix : ∀ x : X, e (j x) = k x) (S : Set X) :
    e '' (j '' S) = k '' S := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hfix x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨j x, ⟨x, hx, rfl⟩, hfix x⟩

/-- The canonical order isomorphism is additive. -/
private lemma completionOrderIso_map_add (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) (y₁ y₂ : Y) :
    completionOrderIso j k hj hk hdY hdZ hmY hmZ (y₁ + y₂) =
      completionOrderIso j k hj hk hdY hdZ hmY hmZ y₁ +
        completionOrderIso j k hj hk hdY hdZ hmY hmZ y₂ := by
  let e := completionOrderIso j k hj hk hdY hdZ hmY hmZ
  let S : Set X := {x | j x ≤ y₁}
  let T : Set X := {x | j x ≤ y₂}
  have hfix : ∀ x : X, e (j x) = k x :=
    completionOrderIso_apply_principal j k hj hk hdY hdZ hmY hmZ
  have hS : IsLUB (j '' S) y₁ := isLUB_image_below j hdY hmY y₁
  have hT : IsLUB (j '' T) y₂ := isLUB_image_below j hdY hmY y₂
  have hsum : IsLUB (j '' S + j '' T) (y₁ + y₂) := hS.add hT
  have hsumMap : IsLUB (k '' S + k '' T) (e (y₁ + y₂)) := by
    rw [← image_add_principals e j k hfix S T]
    exact e.isLUB_image'.mpr hsum
  have hS' : IsLUB (k '' S) (e y₁) := by
    rw [← image_principals e j k hfix S]
    exact e.isLUB_image'.mpr hS
  have hT' : IsLUB (k '' T) (e y₂) := by
    rw [← image_principals e j k hfix T]
    exact e.isLUB_image'.mpr hT
  exact hsumMap.unique (hS'.add hT')

/-- The canonical order isomorphism maps scalar images of embedded sets to target images. -/
private lemma image_smul_principals (e : Y ≃o Z)
    (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hfix : ∀ x : X, e (j x) = k x) (r : ℝ) (S : Set X) :
    e '' ((fun y : Y ↦ r • y) '' (j '' S)) =
      (fun z : Z ↦ r • z) '' (k '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨k x, ⟨x, hx, rfl⟩, ?_⟩
    symm
    change e (r • j x) = r • k x
    rw [← map_smul j r x, hfix, map_smul]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨r • j x, ⟨j x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    change e (r • j x) = r • k x
    rw [← map_smul j r x, hfix, map_smul]

/-- The canonical order isomorphism preserves multiplication by nonnegative reals. -/
private lemma completionOrderIso_map_smul_nonneg (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing)
    (r : ℝ) (hr : 0 ≤ r) (y : Y) :
    completionOrderIso j k hj hk hdY hdZ hmY hmZ (r • y) =
      r • completionOrderIso j k hj hk hdY hdZ hmY hmZ y := by
  let e := completionOrderIso j k hj hk hdY hdZ hmY hmZ
  let S : Set X := {x | j x ≤ y}
  have hfix : ∀ x : X, e (j x) = k x :=
    completionOrderIso_apply_principal j k hj hk hdY hdZ hmY hmZ
  have hS : IsLUB (j '' S) y := isLUB_image_below j hdY hmY y
  have hS' : IsLUB (k '' S) (e y) := by
    rw [← image_principals e j k hfix S]
    exact e.isLUB_image'.mpr hS
  have hscaled : IsLUB ((fun z : Z ↦ r • z) '' (k '' S)) (e (r • y)) := by
    rw [← image_smul_principals e j k hfix r S]
    exact e.isLUB_image'.mpr (isLUB_smul_of_nonneg hr hS)
  exact hscaled.unique (isLUB_smul_of_nonneg hr hS')

/-- Additivity upgrades the canonical order isomorphism to an additive equivalence. -/
private noncomputable def completionAddEquiv (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) : Y ≃+ Z :=
  { (completionOrderIso j k hj hk hdY hdZ hmY hmZ).toEquiv with
    map_add' := completionOrderIso_map_add j k hj hk hdY hdZ hmY hmZ }

/-- The canonical order isomorphism preserves real scalar multiplication. -/
private lemma completionOrderIso_map_smul (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) (r : ℝ) (y : Y) :
    completionOrderIso j k hj hk hdY hdZ hmY hmZ (r • y) =
      r • completionOrderIso j k hj hk hdY hdZ hmY hmZ y := by
  by_cases hr : 0 ≤ r
  · exact completionOrderIso_map_smul_nonneg j k hj hk hdY hdZ hmY hmZ r hr y
  · have hneg : 0 ≤ -r := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hr))
    calc
      completionOrderIso j k hj hk hdY hdZ hmY hmZ (r • y) =
          completionOrderIso j k hj hk hdY hdZ hmY hmZ (-((-r) • y)) := by
        simp only [neg_smul, neg_neg]
      _ = -completionOrderIso j k hj hk hdY hdZ hmY hmZ ((-r) • y) := by
        exact (completionAddEquiv j k hj hk hdY hdZ hmY hmZ).map_neg _
      _ = -((-r) • completionOrderIso j k hj hk hdY hdZ hmY hmZ y) := by
        rw [completionOrderIso_map_smul_nonneg j k hj hk hdY hdZ hmY hmZ (-r) hneg y]
      _ = r • completionOrderIso j k hj hk hdY hdZ hmY hmZ y := by
        simp only [neg_smul, neg_neg]

/-- The canonical vector-lattice equivalence between two Dedekind completions. -/
noncomputable def completionVecLatEquiv (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) : VecLatEquiv Y Z := by
  let e := completionOrderIso j k hj hk hdY hdZ hmY hmZ
  let eLinear : Y ≃ₗ[ℝ] Z :=
    { completionAddEquiv j k hj hk hdY hdZ hmY hmZ with
      map_smul' := by
        intro r y
        exact completionOrderIso_map_smul j k hj hk hdY hdZ hmY hmZ r y }
  exact {
    eLinear with
    map_sup' := by
      intro y₁ y₂
      exact e.map_sup y₁ y₂
    map_inf' := by
      intro y₁ y₂
      exact e.map_inf y₁ y₂
  }

/-- The canonical vector-lattice equivalence agrees with the original embeddings. -/
theorem completionVecLatEquiv_apply_principal (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : j.range.IsOrderDense) (hdZ : k.range.IsOrderDense)
    (hmY : j.range.IsMajorizing)
    (hmZ : k.range.IsMajorizing) (x : X) :
    completionVecLatEquiv j k hj hk hdY hdZ hmY hmZ (j x) = k x :=
  completionOrderIso_apply_principal j k hj hk hdY hdZ hmY hmZ x

end DedekindCompletion

end Uniqueness

namespace DedekindCompletion

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- The canonical vector-lattice equivalence between two Dedekind completions. -/
def equiv (D D' : DedekindCompletion X) : VecLatEquiv D.carrier D'.carrier :=
  completionVecLatEquiv D.inclusion D'.inclusion
    D.injective D'.injective D.dense D'.dense D.majorizing D'.majorizing

/-- The canonical equivalence agrees with the embeddings of the original lattice. -/
@[simp]
theorem equiv_apply_inclusion (D D' : DedekindCompletion X) (x : X) :
    D.equiv D' (D.inclusion x) = D'.inclusion x :=
  completionVecLatEquiv_apply_principal D.inclusion D'.inclusion
    D.injective D'.injective D.dense D'.dense D.majorizing D'.majorizing x

end DedekindCompletion
end
