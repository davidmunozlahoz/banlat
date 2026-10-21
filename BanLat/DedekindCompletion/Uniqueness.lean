/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.OrderDense

/-!
# Uniqueness of Dedekind completion

Suprema of embedded elements define a canonical order isomorphism between
two order-dense majorizing completions. This isomorphism preserves addition
and real scalar multiplication, giving a vector-lattice equivalence.
-/

noncomputable section
open Set
open scoped Pointwise

namespace DedekindCompletion

universe u

variable {X Y Z : Type u}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid Y]
  [VectorLattice Y]
  [AddCommGroup Z] [ConditionallyCompleteLattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z]

/-- Images in the target completion of original elements lying below `y` in the source. -/
private def lowerImage (j : VecLatHom X Y) (k : VecLatHom X Z) (y : Y) : Set Z :=
  {z | ∃ x : X, k x = z ∧ j x ≤ y}

/-- Majorization ensures that the set of lower images is nonempty. -/
private lemma lowerImage_nonempty (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) :
    (lowerImage j k y).Nonempty := by
  obtain ⟨x, hx⟩ := hm (-y)
  refine ⟨k (-x), -x, rfl, ?_⟩
  simpa only [map_neg, neg_le] using hx

/-- A source majorant of `y` bounds all lower images from above. -/
private lemma lowerImage_bddAbove (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) :
    BddAbove (lowerImage j k y) := by
  obtain ⟨x, hx⟩ := hm y
  refine ⟨k x, ?_⟩
  rintro _ ⟨a, rfl, ha⟩
  exact k.monotone (j.le_of_map_le hj (ha.trans hx))

/-- The canonical candidate map between two order completions. -/
private def completionMap (j : VecLatHom X Y) (k : VecLatHom X Z) (y : Y) : Z :=
  sSup (lowerImage j k y)

/-- The completion map is the least upper bound of the lower images. -/
private lemma completionMap_isLUB (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) :
    IsLUB (lowerImage j k y) (completionMap j k y) :=
  isLUB_csSup (lowerImage_nonempty j k hm y)
    (lowerImage_bddAbove j k hj hm y)

/-- The completion map sends each embedded original element to its target image. -/
private lemma completionMap_principal (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j)
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (x : X) :
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
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) :
    Monotone (completionMap j k) := by
  intro y₁ y₂ hle
  apply (completionMap_isLUB j k hj hm y₁).2
  rintro _ ⟨x, rfl, hx⟩
  exact (completionMap_isLUB j k hj hm y₂).1 ⟨x, rfl, hx.trans hle⟩

/-- The completion map lies below `k x` exactly when its argument lies below `j x`. -/
private lemma completionMap_le_principal (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hd : IsOrderDense (range j))
    (hm : ∀ y : Y, ∃ x : X, y ≤ j x) (y : Y) (x : X) :
    completionMap j k y ≤ k x ↔ y ≤ j x := by
  constructor
  · intro h
    apply (isLUB_range_below j hd hm y).2
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) (y : Y) :
    completionMap k j (completionMap j k y) = y := by
  have hchar (x : X) :
      completionMap k j (completionMap j k y) ≤ j x ↔ y ≤ j x :=
    (completionMap_le_principal k j hk hj hdZ hmZ (completionMap j k y) x).trans
      (completionMap_le_principal j k hj hk hdY hmY y x)
  apply le_antisymm
  · apply (isGLB_range_above j hdY hmY y).2
    rintro _ ⟨⟨x, rfl⟩, hyx⟩
    exact (hchar x).2 hyx
  · apply (isGLB_range_above j hdY hmY (completionMap k j (completionMap j k y))).2
    rintro _ ⟨⟨x, rfl⟩, hgx⟩
    exact (hchar x).1 hgx

/-- The underlying order isomorphism between two order-dense majorizing
conditionally complete vector lattices extending the same vector lattice. -/
noncomputable def completionOrderIso (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) : Y ≃o Z where
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) (x : X) :
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) (y₁ y₂ : Y) :
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x)
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) : Y ≃+ Z :=
  { (completionOrderIso j k hj hk hdY hdZ hmY hmZ).toEquiv with
    map_add' := completionOrderIso_map_add j k hj hk hdY hdZ hmY hmZ }

/-- The canonical order isomorphism preserves real scalar multiplication. -/
private lemma completionOrderIso_map_smul (j : VecLatHom X Y) (k : VecLatHom X Z)
    (hj : Function.Injective j) (hk : Function.Injective k)
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) (r : ℝ) (y : Y) :
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) : VecLatEquiv Y Z := by
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
    (hdY : IsOrderDense (range j)) (hdZ : IsOrderDense (range k))
    (hmY : ∀ y : Y, ∃ x : X, y ≤ j x)
    (hmZ : ∀ z : Z, ∃ x : X, z ≤ k x) (x : X) :
    completionVecLatEquiv j k hj hk hdY hdZ hmY hmZ (j x) = k x :=
  completionOrderIso_apply_principal j k hj hk hdY hdZ hmY hmZ x

end DedekindCompletion
end
