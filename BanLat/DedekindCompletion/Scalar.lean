/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.Algebra
import BanLat.Operators.Hom

/-!
# Real scalar multiplication on bounded cuts

Positive scalars transport cuts along order automorphisms. Extending this
action to zero and negative scalars gives a real vector lattice, with the
original lattice embedded by principal cuts.
-/

noncomputable section
open Set
open scoped Pointwise

namespace DedekindCompletion

universe u

variable {X : Type u} [Lattice X]

namespace BoundedCut

/-- Transport a bounded cut along an order automorphism. -/
private def mapOrderIso (e : X ≃o X) (A : BoundedCut X) : BoundedCut X :=
  ⟨{
    extent := e '' A.left
    intent := e '' A.right
    upperPolar_extent := e.upperBounds_image.trans
      (congrArg (e '' ·) (DedekindCut.upperBounds_left A.1))
    lowerPolar_intent := e.lowerBounds_image.trans
      (congrArg (e '' ·) (DedekindCut.lowerBounds_right A.1))
  }, A.left_nonempty.image e, A.right_nonempty.image e⟩

/-- The lower part of a transported cut is the image of its lower part. -/
@[simp] private lemma mapOrderIso_left (e : X ≃o X) (A : BoundedCut X) :
    (mapOrderIso e A).left = e '' A.left := rfl

/-- The upper part of a transported cut is the image of its upper part. -/
@[simp] private lemma mapOrderIso_right (e : X ≃o X) (A : BoundedCut X) :
    (mapOrderIso e A).right = e '' A.right := rfl

/-- An order automorphism sends a principal cut to the cut of the image. -/
private lemma mapOrderIso_principal (e : X ≃o X) (x : X) :
    mapOrderIso e (principal x) = principal (e x) := by
  apply Subtype.ext
  apply DedekindCut.ext
  ext z
  change z ∈ e '' Iic x ↔ z ∈ Iic (e x)
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact e.monotone hy
  · intro hz
    exact ⟨e.symm z, e.le_iff_le.mp (by simpa using hz), e.apply_symm_apply z⟩

/-- Transporting a cut successively along two order automorphisms composes them. -/
private lemma mapOrderIso_comp (e f : X ≃o X) (A : BoundedCut X) :
    mapOrderIso f (mapOrderIso e A) = mapOrderIso (e.trans f) A := by
  apply Subtype.ext
  apply DedekindCut.ext
  ext z
  change z ∈ f '' (e '' A.left) ↔ z ∈ (e.trans f) '' A.left
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

/-- Transport along the identity order automorphism fixes a cut. -/
private lemma mapOrderIso_refl (A : BoundedCut X) :
    mapOrderIso (OrderIso.refl X) A = A := by
  apply Subtype.ext
  apply DedekindCut.ext
  ext z
  change z ∈ (OrderIso.refl X) '' A.left ↔ z ∈ A.left
  simp

/-- Transport along an order automorphism preserves the order of cuts. -/
private lemma mapOrderIso_mono (e : X ≃o X) : Monotone (mapOrderIso e) := by
  intro A B hAB
  change e '' A.left ⊆ e '' B.left
  exact Set.image_mono hAB

variable [AddCommGroup X] [IsOrderedAddMonoid X]

omit [IsOrderedAddMonoid X] in
/-- An additive order automorphism maps a pointwise set sum to the sum of the images. -/
private lemma image_add_iso (e : X ≃o X)
    (hadd : ∀ x y : X, e (x + y) = e x + e y) (S T : Set X) :
    e '' (S + T) = e '' S + e '' T := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    rw [hadd]
    exact Set.add_mem_add ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨x + y, Set.add_mem_add hx hy, ?_⟩
    exact hadd x y

/-- An additive order automorphism preserves cut addition. -/
private lemma mapOrderIso_add (e : X ≃o X)
    (hadd : ∀ x y : X, e (x + y) = e x + e y)
    (A B : BoundedCut X) :
    mapOrderIso e (A + B) = mapOrderIso e A + mapOrderIso e B := by
  apply Subtype.ext
  apply DedekindCut.ext'
  change e '' upperBounds (A.left + B.left) =
    upperBounds (e '' A.left + e '' B.left)
  rw [← OrderIso.upperBounds_image, image_add_iso e hadd]

variable [VectorLattice X]

/-- Transport a bounded cut by multiplication with a positive real scalar. -/
private def posSmulCut (r : ℝ) (hr : 0 < r) (A : BoundedCut X) : BoundedCut X :=
  mapOrderIso (OrderIso.smulRight hr) A

/-- The lower part of a positively scaled cut is the image of its lower part. -/
@[simp] private lemma posSmulCut_left (r : ℝ) (hr : 0 < r) (A : BoundedCut X) :
    (posSmulCut r hr A).left = (fun x ↦ r • x) '' A.left := rfl

/-- Positive scalar multiplication sends a principal cut to the scaled principal cut. -/
private lemma posSmulCut_principal (r : ℝ) (hr : 0 < r) (x : X) :
    posSmulCut r hr (principal x) = principal (r • x) :=
  mapOrderIso_principal (OrderIso.smulRight hr) x

/-- Successive positive scalings multiply their scalars. -/
private lemma posSmulCut_mul (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (A : BoundedCut X) :
    posSmulCut r hr (posSmulCut s hs A) =
      posSmulCut (r * s) (mul_pos hr hs) A := by
  change mapOrderIso (OrderIso.smulRight hr)
    (mapOrderIso (OrderIso.smulRight hs) A) =
      mapOrderIso (OrderIso.smulRight (mul_pos hr hs)) A
  rw [mapOrderIso_comp]
  congr 1
  ext x
  change r • (s • x) = (r * s) • x
  rw [mul_smul]

/-- Scaling a cut by one leaves it unchanged. -/
private lemma posSmulCut_one (A : BoundedCut X) :
    posSmulCut 1 (by norm_num) A = A := by
  change mapOrderIso (OrderIso.smulRight (by norm_num : (0 : ℝ) < 1)) A = A
  have h : (OrderIso.smulRight (β := X) (by norm_num : (0 : ℝ) < 1)) = OrderIso.refl X := by
    ext x
    change (1 : ℝ) • x = x
    exact one_smul ℝ x
  rw [h, mapOrderIso_refl]

/-- Positive scalar multiplication distributes over cut addition. -/
private lemma posSmulCut_add (r : ℝ) (hr : 0 < r)
    (A B : BoundedCut X) :
    posSmulCut r hr (A + B) = posSmulCut r hr A + posSmulCut r hr B :=
  mapOrderIso_add (OrderIso.smulRight hr) (fun x y ↦ smul_add r x y) A B

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] in
/-- The lower part of a cut is closed under binary suprema. -/
private lemma left_sup_mem (A : BoundedCut X) {x y : X}
    (hx : x ∈ A.left) (hy : y ∈ A.left) : x ⊔ y ∈ A.left := by
  change x ⊔ y ∈ A.1.left
  rw [← DedekindCut.lowerBounds_right]
  intro z hz
  exact sup_le (A.1.rel_extent_intent hx hz) (A.1.rel_extent_intent hy hz)

/-- For positive scalars, scalar addition holds on cuts. -/
private lemma posSmulCut_add_scalar (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (A : BoundedCut X) :
    posSmulCut (r + s) (add_pos hr hs) A =
      posSmulCut r hr A + posSmulCut s hs A := by
  apply le_antisymm
  · change (fun x : X ↦ (r + s) • x) '' A.left ⊆
      (Concept.ofObjects (· ≤ ·)
        ((fun x : X ↦ r • x) '' A.left + (fun x : X ↦ s • x) '' A.left)).extent
    rintro z ⟨x, hx, rfl⟩
    change (r + s) • x ∈ lowerBounds
      (upperBounds ((fun x : X ↦ r • x) '' A.left +
        (fun x : X ↦ s • x) '' A.left))
    intro y hy
    rw [add_smul]
    exact hy (Set.add_mem_add ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩)
  · change Concept.ofObjects (· ≤ ·)
      ((fun x : X ↦ r • x) '' A.left + (fun x : X ↦ s • x) '' A.left) ≤
        (posSmulCut (r + s) (add_pos hr hs) A).1
    apply Concept.ofObjects_le_iff.mpr
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    let c := x ⊔ y
    have hc : c ∈ A.left := left_sup_mem A hx hy
    have hle : r • x + s • y ≤ (r + s) • c := by
      rw [add_smul]
      exact add_le_add
        (smul_le_smul_of_nonneg_left le_sup_left hr.le)
        (smul_le_smul_of_nonneg_left le_sup_right hs.le)
    exact (posSmulCut (r + s) (add_pos hr hs) A).1.isLowerSet_extent_le
      hle ⟨c, hc, rfl⟩

variable [IsVLArchimedean X]

/-- Real scalar multiplication on bounded cuts, extended from positive scalars
using the cut group structure. -/
private def smulCut (r : ℝ) (A : BoundedCut X) : BoundedCut X :=
  if hr : 0 < r then posSmulCut r hr A
  else if hr : r < 0 then -posSmulCut (-r) (neg_pos.mpr hr) A
  else 0

omit [IsVLArchimedean X] in
/-- The scalar action agrees with positive scaling for a positive scalar. -/
private lemma smulCut_of_pos {r : ℝ} (hr : 0 < r) (A : BoundedCut X) :
    smulCut r A = posSmulCut r hr A := by
  simp only [smulCut, dif_pos hr]

omit [IsVLArchimedean X] in
/-- A negative scalar acts by reflecting the cut scaled by its opposite. -/
private lemma smulCut_of_neg {r : ℝ} (hr : r < 0) (A : BoundedCut X) :
    smulCut r A = -posSmulCut (-r) (neg_pos.mpr hr) A := by
  have hn : ¬ 0 < r := not_lt.mpr hr.le
  simp only [smulCut, dif_neg hn, dif_pos hr]

omit [IsVLArchimedean X] in
/-- Zero scalar multiplication gives the zero cut. -/
@[simp] private lemma smulCut_zero_scalar (A : BoundedCut X) : smulCut 0 A = 0 := by
  simp [smulCut]

/-- Negating a scalar negates its action on a cut. -/
private lemma smulCut_neg_scalar (r : ℝ) (A : BoundedCut X) :
    smulCut (-r) A = -smulCut r A := by
  rcases lt_trichotomy r 0 with hneg | hzero | hpos
  · have hpos' : 0 < -r := neg_pos.mpr hneg
    rw [smulCut_of_pos hpos', smulCut_of_neg hneg]
    simp only [neg_neg]
  · subst r
    simp
  · have hneg' : -r < 0 := neg_neg_iff_pos.mpr hpos
    rw [smulCut_of_neg hneg', smulCut_of_pos hpos]
    simp only [neg_neg]

omit [IsVLArchimedean X] in
/-- Positive scalar multiplication fixes the zero cut. -/
private lemma posSmulCut_zero (r : ℝ) (hr : 0 < r) :
    posSmulCut r hr (0 : BoundedCut X) = 0 :=
  (posSmulCut_principal r hr 0).trans (congrArg principal (smul_zero r))

omit [IsVLArchimedean X] in
/-- Positive scalar multiplication commutes with reflection of cuts. -/
private lemma posSmulCut_neg (r : ℝ) (hr : 0 < r) (A : BoundedCut X) :
    posSmulCut r hr (-A) = -posSmulCut r hr A := by
  apply Subtype.ext
  apply DedekindCut.ext
  ext z
  change z ∈ (fun x : X ↦ r • x) '' (-A.right) ↔
    z ∈ -((fun x : X ↦ r • x) '' A.right)
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_neg] at hx ⊢
    refine ⟨-x, hx, ?_⟩
    simp only [smul_neg]
  · intro hz
    rw [Set.mem_neg] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨-x, ?_, ?_⟩
    · rw [Set.mem_neg]
      simpa using hx
    · change r • (-x) = z
      change r • x = -z at hzx
      rw [smul_neg, hzx, neg_neg]

/-- Scalar multiplication distributes over cut addition. -/
private lemma smulCut_add (r : ℝ) (A B : BoundedCut X) :
    smulCut r (A + B) = smulCut r A + smulCut r B := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [smulCut_of_neg hr, smulCut_of_neg hr, smulCut_of_neg hr,
      posSmulCut_add]
    exact neg_add _ _
  · subst r
    simp
  · rw [smulCut_of_pos hr, smulCut_of_pos hr, smulCut_of_pos hr,
      posSmulCut_add]

omit [IsVLArchimedean X] in
/-- Positive scaling after arbitrary scalar multiplication multiplies the scalars. -/
private lemma posSmulCut_smulCut (r s : ℝ) (hr : 0 < r)
    (A : BoundedCut X) :
    posSmulCut r hr (smulCut s A) = smulCut (r * s) A := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have hrs : r * s < 0 := mul_neg_of_pos_of_neg hr hs
    rw [smulCut_of_neg hs, posSmulCut_neg, smulCut_of_neg hrs]
    simpa only [mul_neg] using
      congrArg Neg.neg (posSmulCut_mul r (-s) hr (neg_pos.mpr hs) A)
  · subst s
    simp [posSmulCut_zero]
  · have hrs : 0 < r * s := mul_pos hr hs
    rw [smulCut_of_pos hs, smulCut_of_pos hrs]
    exact posSmulCut_mul r s hr hs A

/-- Successive scalar multiplications multiply their scalars. -/
private lemma smulCut_mul (r s : ℝ) (A : BoundedCut X) :
    smulCut r (smulCut s A) = smulCut (r * s) A := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [smulCut_of_neg hr]
    have h := posSmulCut_smulCut (-r) s (neg_pos.mpr hr) A
    rw [h]
    have hscale : r * s = -((-r) * s) := by ring
    rw [hscale, smulCut_neg_scalar]
  · subst r
    simp
  · rw [smulCut_of_pos hr]
    exact posSmulCut_smulCut r s hr A

/-- The difference of two positive scalings equals scaling by the scalar difference. -/
private lemma posSmulCut_sub_scalar (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (A : BoundedCut X) :
    smulCut (r - t) A = posSmulCut r hr A - posSmulCut t ht A := by
  rcases lt_trichotomy (r - t) 0 with hneg | hzero | hpos
  · have hp : 0 < t - r := by linarith
    have hsum : (t - r) + r = t := by ring
    have hid : posSmulCut t ht A =
        posSmulCut (t - r) hp A + posSmulCut r hr A := by
      simpa only [hsum] using posSmulCut_add_scalar (t - r) r hp hr A
    rw [smulCut_of_neg hneg]
    have hleft : posSmulCut (-(r - t)) (neg_pos.mpr hneg) A =
        posSmulCut (t - r) hp A := by
      congr 1
      ring
    rw [hleft]
    rw [hid]
    abel
  · have heq : r = t := by linarith
    subst t
    simp
  · have hsum : (r - t) + t = r := by ring
    have hid : posSmulCut r hr A =
        posSmulCut (r - t) hpos A + posSmulCut t ht A := by
      simpa only [hsum] using posSmulCut_add_scalar (r - t) t hpos ht A
    rw [smulCut_of_pos hpos, hid]
    abel

/-- Scalar addition holds when the first scalar is positive and the second negative. -/
private lemma smulCut_add_pos_neg (r s : ℝ) (hr : 0 < r) (hs : s < 0)
    (A : BoundedCut X) :
    smulCut (r + s) A = smulCut r A + smulCut s A := by
  have h := posSmulCut_sub_scalar r (-s) hr (neg_pos.mpr hs) A
  rw [smulCut_of_pos hr, smulCut_of_neg hs]
  simpa only [sub_eq_add_neg, neg_neg] using h

/-- Scalar addition holds for arbitrary real scalars. -/
private lemma smulCut_add_scalar (r s : ℝ) (A : BoundedCut X) :
    smulCut (r + s) A = smulCut r A + smulCut s A := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rcases lt_trichotomy s 0 with hs | hs | hs
    · have hrs : r + s < 0 := add_neg hr hs
      rw [smulCut_of_neg hrs, smulCut_of_neg hr, smulCut_of_neg hs]
      have h := posSmulCut_add_scalar (-r) (-s) (neg_pos.mpr hr) (neg_pos.mpr hs) A
      have heq : (-r) + (-s) = -(r + s) := by ring
      have hsum : posSmulCut (-(r + s)) (neg_pos.mpr hrs) A =
          posSmulCut (-r) (neg_pos.mpr hr) A +
            posSmulCut (-s) (neg_pos.mpr hs) A := by
        simpa only [heq] using h
      rw [hsum, neg_add]
    · subst s
      simp
    · calc
        smulCut (r + s) A = smulCut (s + r) A := by rw [add_comm]
        _ = smulCut s A + smulCut r A := smulCut_add_pos_neg s r hs hr A
        _ = smulCut r A + smulCut s A := by rw [add_comm]
  · subst r
    simp
  · rcases lt_trichotomy s 0 with hs | hs | hs
    · exact smulCut_add_pos_neg r s hr hs A
    · subst s
      simp
    · have hrs : 0 < r + s := add_pos hr hs
      rw [smulCut_of_pos hrs, smulCut_of_pos hr, smulCut_of_pos hs]
      exact posSmulCut_add_scalar r s hr hs A

omit [IsVLArchimedean X] in
/-- Multiplication by the scalar one fixes every cut. -/
private lemma smulCut_one (A : BoundedCut X) : smulCut 1 A = A := by
  rw [smulCut_of_pos (by norm_num : (0 : ℝ) < 1)]
  exact posSmulCut_one A

/-- Every scalar sends the zero cut to zero. -/
private lemma smulCut_zero (r : ℝ) : smulCut r (0 : BoundedCut X) = 0 := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [smulCut_of_neg hr, posSmulCut_zero]
    simp
  · subst r
    simp
  · rw [smulCut_of_pos hr, posSmulCut_zero]

/-- Bounded cuts of an Archimedean vector lattice form a real module. -/
noncomputable instance : Module ℝ (BoundedCut X) where
  smul := smulCut
  one_smul := smulCut_one
  mul_smul := fun r s A ↦ (smulCut_mul r s A).symm
  smul_add := smulCut_add
  add_smul := smulCut_add_scalar
  zero_smul := smulCut_zero_scalar
  smul_zero := smulCut_zero

/-- Nonnegative real scalars act monotonically on bounded cuts. -/
noncomputable instance : PosSMulMono ℝ (BoundedCut X) where
  smul_le_smul_of_nonneg_left := by
    intro r hr A B hAB
    by_cases hpos : 0 < r
    · change smulCut r A ≤ smulCut r B
      rw [smulCut_of_pos hpos, smulCut_of_pos hpos]
      exact mapOrderIso_mono ((OrderIso.smulRight (β := X) (a := r) hpos)) hAB
    · have hz : r = 0 := le_antisymm (le_of_not_gt hpos) hr
      subst r
      change smulCut 0 A ≤ smulCut 0 B
      simp only [smulCut_zero_scalar, le_refl]

/-- The bounded-cut completion is a real vector lattice. -/
noncomputable instance : VectorLattice (BoundedCut X) where
  __ := (inferInstance : Module ℝ (BoundedCut X))
  __ := (inferInstance : PosSMulMono ℝ (BoundedCut X))

/-- Principal cuts preserve real scalar multiplication. -/
theorem principal_smul (r : ℝ) (x : X) :
    principal (r • x) = r • (principal x : BoundedCut X) := by
  change principal (r • x) = smulCut r (principal x)
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [smulCut_of_neg hr, posSmulCut_principal]
    change principal (r • x) = negCut (principal ((-r) • x))
    rw [negCut_principal]
    congr 1
    simp only [neg_smul, neg_neg]
  · subst r
    simp only [zero_smul, smulCut_zero_scalar]
    rfl
  · rw [smulCut_of_pos hr, posSmulCut_principal]

/-- The canonical vector-lattice embedding into bounded Dedekind cuts. -/
noncomputable def principalHom : VecLatHom X (BoundedCut X) where
  toFun := principal
  map_add' := fun x y ↦ (principal_add x y).symm
  map_smul' := by
    intro r x
    simpa only [RingHom.id_apply] using principal_smul r x
  map_sup' := principal_sup
  map_inf' := principal_inf

end BoundedCut
end DedekindCompletion
end
