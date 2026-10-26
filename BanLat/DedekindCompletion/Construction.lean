/-
Authors: Pedro Tradacete
-/

import Mathlib.Order.Completion
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import BanLat.Basic
import BanLat.Operators.Hom
import BanLat.OrderDense

/-!
# Construction of the Dedekind completion

We construct the Dedekind completion of an Archimedean vector lattice `X` as the type
`BoundedCut X` of Dedekind cuts of `X` whose lower and upper parts are both nonempty, ordered by
inclusion of lower parts. Finite suprema and infima are inherited from Mathlib's `DedekindCut`,
making `BoundedCut X` a conditionally complete lattice. The sum of two cuts is the cut generated
by the pointwise sum of their lower parts, the zero is the principal cut of `0`, and the negative
of a cut has the negated upper part as its lower part. A positive scalar acts by scaling the lower
part. With these operations `BoundedCut X` is a vector lattice, and
`principalHom` embeds `X` into it sending each element to the principal cut it generates.
-/

open Set

namespace DedekindCompletion

universe u

variable {X : Type u} [PartialOrder X]

/-- We define bounded cuts as those Dedekind cuts whose left and right parts are both non-empty.
This guarantees that the left part is bounded from above and the right part is bounded from
below. -/
abbrev BoundedCut (X : Type u) [PartialOrder X] :=
  {A : DedekindCut X // A.left.Nonempty ∧ A.right.Nonempty}

namespace BoundedCut

/-- The lower part of a bounded cut. -/
def left (A : BoundedCut X) : Set X := A.1.left

/-- The upper part of a bounded cut. -/
def right (A : BoundedCut X) : Set X := A.1.right

/-- The lower part of a bounded cut is nonempty. -/
theorem left_nonempty (A : BoundedCut X) : A.left.Nonempty := A.2.1

/-- The upper part of a bounded cut is nonempty. -/
theorem right_nonempty (A : BoundedCut X) : A.right.Nonempty := A.2.2

/-- The principal bounded cut of an element of the original partially ordered set. -/
def principal (x : X) : BoundedCut X :=
  ⟨DedekindCut.principal x,
    ⟨x, by simp⟩, ⟨x, by simp⟩⟩

/-- The lower part of a principal cut is the corresponding lower interval. -/
@[simp]
theorem left_principal (x : X) : (principal x).left = Iic x := rfl

/-- The upper part of a principal cut is the corresponding upper interval. -/
@[simp]
theorem right_principal (x : X) : (principal x).right = Ici x := rfl

/-- Principal cuts preserve and reflect order. -/
@[simp]
theorem principal_le_principal {x y : X} :
    principal x ≤ principal y ↔ x ≤ y := DedekindCut.principal_le_principal

/-- Distinct elements give distinct principal cuts. -/
theorem principal_injective : Function.Injective (principal : X → BoundedCut X) := by
  intro x y h
  exact DedekindCut.principal_inj.mp (congrArg Subtype.val h)

/-- A principal cut lies below a cut exactly when its generator is in the lower part. -/
theorem principal_le_iff (A : BoundedCut X) (x : X) :
    principal x ≤ A ↔ x ∈ A.left :=
  DedekindCut.principal_le_iff

/-- A cut lies below a principal cut exactly when its generator is in the upper part. -/
theorem le_principal_iff (A : BoundedCut X) (x : X) :
    A ≤ principal x ↔ x ∈ A.right :=
  DedekindCut.le_principal_iff

/-- Principal cuts below a bounded cut have that cut as their least upper bound. -/
theorem isLUB_principals (A : BoundedCut X) :
    IsLUB ((principal : X → BoundedCut X) '' A.left) A := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact (principal_le_iff A x).mpr hx
  · intro B hB
    change A.1.left ⊆ B.1.left
    intro x hx
    exact (principal_le_iff B x).mp (hB ⟨x, hx, rfl⟩)

/-- Every bounded cut lies below a principal cut. -/
theorem majorizing (A : BoundedCut X) : ∃ x : X, A ≤ principal x := by
  obtain ⟨x, hx⟩ := A.right_nonempty
  exact ⟨x, (le_principal_iff A x).mpr hx⟩

/-- Every bounded cut lies above a principal cut. -/
theorem minorizing (A : BoundedCut X) : ∃ x : X, principal x ≤ A := by
  obtain ⟨x, hx⟩ := A.left_nonempty
  exact ⟨x, (principal_le_iff A x).mpr hx⟩

end BoundedCut

section Lattice

variable {X : Type u} [Lattice X]

namespace BoundedCut

/-- The supremum of two bounded cuts is bounded. -/
private def supCut (A B : BoundedCut X) : BoundedCut X := by
  refine ⟨A.1 ⊔ B.1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := A.left_nonempty
    exact ⟨x, (le_sup_left : A.1 ≤ A.1 ⊔ B.1) hx⟩
  · obtain ⟨x, hx⟩ := A.right_nonempty
    obtain ⟨y, hy⟩ := B.right_nonempty
    have hA : A.1 ≤ DedekindCut.principal (x ⊔ y) :=
      (show A.1 ≤ DedekindCut.principal x from (le_principal_iff A x).mpr hx).trans
        (DedekindCut.principal_le_principal.mpr le_sup_left)
    have hB : B.1 ≤ DedekindCut.principal (x ⊔ y) :=
      (show B.1 ≤ DedekindCut.principal y from (le_principal_iff B y).mpr hy).trans
        (DedekindCut.principal_le_principal.mpr le_sup_right)
    have h := sup_le hA hB
    refine ⟨x ⊔ y, ?_⟩
    rw [← DedekindCut.upperBounds_left]
    exact h

/-- The infimum of two bounded cuts is bounded. -/
private def infCut (A B : BoundedCut X) : BoundedCut X := by
  refine ⟨A.1 ⊓ B.1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := A.left_nonempty
    obtain ⟨y, hy⟩ := B.left_nonempty
    have hA : DedekindCut.principal (x ⊓ y) ≤ A.1 :=
      (DedekindCut.principal_le_principal.mpr inf_le_left).trans
        (show DedekindCut.principal x ≤ A.1 from (principal_le_iff A x).mpr hx)
    have hB : DedekindCut.principal (x ⊓ y) ≤ B.1 :=
      (DedekindCut.principal_le_principal.mpr inf_le_right).trans
        (show DedekindCut.principal y ≤ B.1 from (principal_le_iff B y).mpr hy)
    refine ⟨x ⊓ y, ?_⟩
    have hxmem : x ⊓ y ∈ (DedekindCut.principal (x ⊓ y)).left := by simp
    exact (le_inf hA hB) hxmem
  · obtain ⟨x, hx⟩ := A.right_nonempty
    refine ⟨x, ?_⟩
    change x ∈ A.1.right at hx
    rw [← DedekindCut.upperBounds_left] at hx ⊢
    intro z hz
    exact hx ((inf_le_left : A.1 ⊓ B.1 ≤ A.1) hz)

/-- Bounded cuts inherit the lattice operations on Dedekind cuts. -/
noncomputable instance : Lattice (BoundedCut X) where
  __ := (inferInstance : PartialOrder (BoundedCut X))
  sup := supCut
  inf := infCut
  le_sup_left := fun A B ↦ le_sup_left (a := A.1) (b := B.1)
  le_sup_right := fun A B ↦ le_sup_right (a := A.1) (b := B.1)
  sup_le := fun A B C hA hB ↦ (sup_le hA hB : A.1 ⊔ B.1 ≤ C.1)
  inf_le_left := fun A B ↦ inf_le_left (a := A.1) (b := B.1)
  inf_le_right := fun A B ↦ inf_le_right (a := A.1) (b := B.1)
  le_inf := fun A B C hA hB ↦ (le_inf hA hB : A.1 ≤ B.1 ⊓ C.1)

/-- Principal cuts preserve finite suprema. -/
theorem principal_sup (x y : X) :
    principal (x ⊔ y) = principal x ⊔ principal y :=
  Subtype.ext (DedekindCut.ext' (Set.ext fun _ ↦ sup_le_iff))

/-- Principal cuts preserve finite infima. -/
theorem principal_inf (x y : X) :
    principal (x ⊓ y) = principal x ⊓ principal y :=
  Subtype.ext (DedekindCut.ext (Set.ext fun _ ↦ le_inf_iff))

end BoundedCut
end Lattice

section ConditionalCompleteness

variable {X : Type u} [Lattice X] [Nonempty X]

namespace BoundedCut

/-- The supremum of a nonempty bounded-above family of bounded cuts is a bounded cut. -/
private noncomputable def boundedSup (S : Set (BoundedCut X))
    (hne : S.Nonempty) (hb : BddAbove S) : BoundedCut X := by
  let U : Set (DedekindCut X) := Subtype.val '' S
  have hU_ne : U.Nonempty := by
    obtain ⟨A, hA⟩ := hne
    exact ⟨A.1, A, hA, rfl⟩
  have hU_bdd : BddAbove U := by
    obtain ⟨B, hB⟩ := hb
    refine ⟨B.1, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    exact hB hA
  refine ⟨sSup U, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := hne
    obtain ⟨x, hx⟩ := A.left_nonempty
    refine ⟨x, ?_⟩
    exact (le_csSup hU_bdd ⟨A, hA, rfl⟩) hx
  · obtain ⟨B, hB⟩ := hb
    obtain ⟨x, hx⟩ := B.right_nonempty
    refine ⟨x, ?_⟩
    have hsup : sSup U ≤ B.1 := csSup_le hU_ne (by
      rintro _ ⟨A, hA, rfl⟩
      exact hB hA)
    have hBx : B.1 ≤ DedekindCut.principal x :=
      (le_principal_iff B x).mpr hx
    have h : sSup U ≤ DedekindCut.principal x := hsup.trans hBx
    change x ∈ (sSup U).right
    rw [← DedekindCut.upperBounds_left]
    exact h

omit [Nonempty X] in
/-- The bounded supremum is the least upper bound of the family. -/
private lemma boundedSup_isLUB (S : Set (BoundedCut X))
    (hne : S.Nonempty) (hb : BddAbove S) : IsLUB S (boundedSup S hne hb) := by
  have hU_bdd : BddAbove (Subtype.val '' S : Set (DedekindCut X)) := by
    obtain ⟨B, hB⟩ := hb
    refine ⟨B.1, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    exact hB hA
  constructor
  · intro A hA
    change A.1 ≤ sSup (Subtype.val '' S)
    exact le_csSup hU_bdd ⟨A, hA, rfl⟩
  · intro B hB
    change sSup (Subtype.val '' S) ≤ B.1
    apply csSup_le
    · obtain ⟨A, hA⟩ := hne
      exact ⟨A.1, A, hA, rfl⟩
    · rintro _ ⟨A, hA, rfl⟩
      exact hB hA

open Classical in
/-- A bounded nonempty family of cuts has its supremum in the ambient cut lattice. -/
noncomputable instance : SupSet (BoundedCut X) where
  sSup S := if h : S.Nonempty ∧ BddAbove S then boundedSup S h.1 h.2
    else principal (Classical.choice ‹Nonempty X›)

/-- Bounded cuts form a conditionally complete lattice. -/
noncomputable instance : ConditionallyCompleteLattice (BoundedCut X) :=
  conditionallyCompleteLatticeOfLatticeOfsSup (BoundedCut X) (by
    classical
    intro S hb hne
    change IsLUB S (if h : S.Nonempty ∧ BddAbove S then boundedSup S h.1 h.2
      else principal (Classical.choice ‹Nonempty X›))
    simp only [dif_pos (⟨hne, hb⟩ : S.Nonempty ∧ BddAbove S)]
    exact boundedSup_isLUB S hne hb)

end BoundedCut
end ConditionalCompleteness

noncomputable section AdditiveGroup

open scoped Pointwise

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

namespace BoundedCut

/-- The cut generated by a set, as the infimum of all cuts whose left part contains `S`. -/
private def closure (S : Set X) : DedekindCut X :=
  Concept.ofObjects (· ≤ ·) S

/-- Closing the first summand does not change the closed sum. -/
private lemma closure_add_left (S T : Set X) :
    closure ((closure S).left + T) = closure (S + T) := by
  apply DedekindCut.ext'
  change upperBounds ((closure S).left + T) = upperBounds (S + T)
  ext z
  constructor
  · intro hz
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hz (Set.add_mem_add (subset_lowerBounds_upperBounds S hx) hy)
  · intro hz
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hub : z - y ∈ upperBounds S := by
      intro s hs
      apply le_sub_iff_add_le.mpr
      exact hz (Set.add_mem_add hs hy)
    exact le_sub_iff_add_le.mp (hx hub)

/-- Closing the second summand does not change the closed sum. -/
private lemma closure_add_right (S T : Set X) :
    closure (S + (closure T).left) = closure (S + T) := by
  simpa only [add_comm] using closure_add_left T S

omit [AddCommGroup X] [IsOrderedAddMonoid X] in
/-- Order closure is monotone under set inclusion. -/
private lemma closure_mono {S T : Set X} (h : S ⊆ T) : closure S ≤ closure T := by
  change (closure S).left ⊆ (closure T).left
  intro x hx
  change x ∈ lowerBounds (upperBounds T)
  intro y hy
  exact hx (fun z hz ↦ hy (h hz))

/-- Define addition of bounded cuts as the closure of the pointwise sum of their lower parts. -/
def addCut (A B : BoundedCut X) : BoundedCut X := by
  let S : Set X := A.left + B.left
  refine ⟨closure S, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := A.left_nonempty
    obtain ⟨b, hb⟩ := B.left_nonempty
    exact ⟨a + b, subset_lowerBounds_upperBounds S (Set.add_mem_add ha hb)⟩
  · obtain ⟨a, ha⟩ := A.right_nonempty
    obtain ⟨b, hb⟩ := B.right_nonempty
    refine ⟨a + b, ?_⟩
    change a + b ∈ upperBounds S
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact add_le_add (A.1.rel_extent_intent hx ha) (B.1.rel_extent_intent hy hb)

/-- Cut addition is commutative. -/
private lemma addCut_comm (A B : BoundedCut X) : addCut A B = addCut B A :=
  Subtype.ext (congrArg closure (add_comm A.left B.left))

/-- Cut addition is associative. -/
private lemma addCut_assoc (A B C : BoundedCut X) :
    addCut (addCut A B) C = addCut A (addCut B C) := by
  apply Subtype.ext
  change closure ((closure (A.left + B.left)).left + C.left) =
    closure (A.left + (closure (B.left + C.left)).left)
  rw [closure_add_left, closure_add_right, add_assoc]

/-- Cut addition is monotone in its first argument. -/
private lemma addCut_mono_left {A B : BoundedCut X} (h : A ≤ B)
    (C : BoundedCut X) : addCut A C ≤ addCut B C := by
  change closure (A.left + C.left) ≤ closure (B.left + C.left)
  apply closure_mono
  rintro _ ⟨a, ha, c, hc, rfl⟩
  exact Set.add_mem_add (h ha) hc

/-- The principal zero cut is the neutral element for cut addition. -/
private lemma addCut_zero (A : BoundedCut X) : addCut A (principal 0) = A := by
  apply Subtype.ext
  change closure (A.left + (principal (0 : X)).left) = A.1
  have h : A.left + (principal (0 : X)).left = A.left := by
    ext z
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      have hy0 : y ≤ 0 := by simpa using hy
      exact A.1.isLowerSet_extent_le (by simpa using add_le_add_left hy0 x) hx
    · intro hz
      convert Set.add_mem_add hz (show (0 : X) ∈ (principal 0).left by simp) using 1
      simp
  rw [h]
  exact Concept.ofObjects_extent (c := A.1)

/-- The principal zero cut is a left identity for cut addition. -/
private lemma zero_addCut (A : BoundedCut X) : addCut (principal 0) A = A := by
  rw [addCut_comm, addCut_zero]

/-- Addition of principal cuts agrees with addition in the original group. -/
theorem principal_add (x y : X) :
    addCut (principal x) (principal y) = principal (x + y) := by
  apply Subtype.ext
  change closure (Iic x + Iic y) = DedekindCut.principal (x + y)
  have h : Iic x + Iic y = Iic (x + y) := by
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact add_le_add ha hb
    · intro hz
      refine ⟨x, le_rfl, z - x, ?_, by abel_nf⟩
      exact sub_le_iff_le_add.mpr (by simpa only [mem_Iic, add_comm] using hz)
  rw [h]
  exact Concept.ofObjects_extent (c := DedekindCut.principal (x + y))

/-- Addition of bounded cuts is induced by addition of cuts. -/
noncomputable instance : Add (BoundedCut X) := ⟨addCut⟩

/-- The principal zero cut is the zero of the completion. -/
noncomputable instance : Zero (BoundedCut X) := ⟨principal 0⟩

/-- Bounded cuts form an additive commutative monoid. -/
noncomputable instance : AddCommMonoid (BoundedCut X) where
  add := addCut
  zero := principal 0
  nsmul := nsmulRec
  add_assoc := addCut_assoc
  zero_add := zero_addCut
  add_zero := addCut_zero
  add_comm := addCut_comm

/-- Cut addition preserves the order. -/
noncomputable instance : IsOrderedAddMonoid (BoundedCut X) where
  add_le_add_left := by
    intro A B h C
    exact addCut_mono_left h C

/-- The upper bounds of the negated upper part form the negated lower part. -/
private lemma upperBounds_neg_right (A : BoundedCut X) :
    upperBounds (-A.right) = -A.left := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_neg]
    change -z ∈ A.1.left
    rw [← DedekindCut.lowerBounds_right]
    intro y hy
    have hny : -y ∈ -A.right := by
      rw [Set.mem_neg]
      simpa only [right, neg_neg] using hy
    simpa only [neg_neg] using (neg_le_neg (hz hny))
  · intro hz
    rw [Set.mem_neg] at hz
    change -z ∈ A.1.left at hz
    intro w hw
    rw [Set.mem_neg] at hw
    have h : -z ≤ -w := A.1.rel_extent_intent hz hw
    simpa using (neg_le_neg h)

/-- The lower bounds of the negated lower part form the negated upper part. -/
private lemma lowerBounds_neg_left (A : BoundedCut X) :
    lowerBounds (-A.left) = -A.right := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_neg]
    change -z ∈ A.1.right
    rw [← DedekindCut.upperBounds_left]
    intro y hy
    have hny : -y ∈ -A.left := by
      rw [Set.mem_neg]
      simpa only [left, neg_neg] using hy
    simpa only [neg_neg] using (neg_le_neg (hz hny))
  · intro hz
    rw [Set.mem_neg] at hz
    change -z ∈ A.1.right at hz
    intro w hw
    rw [Set.mem_neg] at hw
    have h : -w ≤ -z := A.1.rel_extent_intent hw hz
    simpa using (neg_le_neg h)

/-- Negation exchanges the upper and lower parts of a bounded cut. -/
def negCut (A : BoundedCut X) : BoundedCut X := by
  refine ⟨{
    extent := -A.right
    intent := -A.left
    upperPolar_extent := upperBounds_neg_right A
    lowerPolar_intent := lowerBounds_neg_left A
  }, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := A.right_nonempty
    exact ⟨-x, Set.mem_neg.mpr (by simpa using hx)⟩
  · obtain ⟨x, hx⟩ := A.left_nonempty
    exact ⟨-x, Set.mem_neg.mpr (by simpa using hx)⟩

/-- The lower part of a reflected cut is the negative of the upper part. -/
@[simp]
theorem negCut_left (A : BoundedCut X) :
    (negCut A).left = -A.right := rfl

/-- The upper part of a reflected cut is the negative of the lower part. -/
@[simp]
theorem negCut_right (A : BoundedCut X) :
    (negCut A).right = -A.left := rfl

/-- Reflection of principal cuts agrees with negation of their generators. -/
theorem negCut_principal (x : X) :
    negCut (principal x) = principal (-x) := by
  apply Subtype.ext
  apply DedekindCut.ext
  ext z
  change z ∈ -(Ici x) ↔ z ∈ Iic (-x)
  rw [Set.mem_neg]
  simp only [mem_Ici, mem_Iic]
  constructor <;> intro h <;> simpa using (neg_le_neg h)

/-- Negation of cuts reflects their upper and lower parts. -/
noncomputable instance : Neg (BoundedCut X) := ⟨negCut⟩

/-- In an Archimedean ordered group, adding a cut to its reflection gives the zero cut. -/
private lemma addCut_negCut [IsVLArchimedean X] (A : BoundedCut X) :
    addCut A (negCut A) = principal 0 := by
  apply Subtype.ext
  apply DedekindCut.ext'
  change upperBounds (A.left + (-A.right)) = Ici (0 : X)
  ext z
  constructor
  · intro hz
    have hshift : ∀ x ∈ A.left, x + z⁻ ∈ A.left := by
      intro x hx
      change x + z⁻ ∈ A.1.left
      rw [← DedekindCut.lowerBounds_right]
      intro y hy
      have hneg : -y ∈ -A.right := by
        rw [Set.mem_neg]
        simpa only [right, neg_neg] using hy
      have hxy_z : x - y ≤ z := by
        simpa only [sub_eq_add_neg] using hz (Set.add_mem_add hx hneg)
      have hxy_zero : x - y ≤ 0 := sub_nonpos.mpr (A.1.rel_extent_intent hx hy)
      have hxy : x - y ≤ z ⊓ 0 := le_inf hxy_z hxy_zero
      have hnegpart : z ⊓ 0 = -z⁻ := by
        rw [negPart_def, neg_sup, neg_zero]
        simp only [neg_neg]
      rw [hnegpart] at hxy
      have hle : x ≤ -z⁻ + y := sub_le_iff_le_add.mp hxy
      calc
        x + z⁻ ≤ (-z⁻ + y) + z⁻ := add_le_add hle le_rfl
        _ = y := by abel
    obtain ⟨x, hx⟩ := A.left_nonempty
    obtain ⟨y, hy⟩ := A.right_nonempty
    have hiter : ∀ n : ℕ, x + n • z⁻ ∈ A.left := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
          simpa only [succ_nsmul, add_assoc] using hshift _ ih
    have harch : z⁻ = 0 :=
      IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
        (negPart_nonneg z) (y := y - x) (by
          intro n
          have hle : x + n • z⁻ ≤ y := A.1.rel_extent_intent (hiter n) hy
          exact le_sub_iff_add_le.mpr (by simpa only [add_comm] using hle))
    exact (negPart_eq_zero.mp harch)
  · intro hz
    rintro _ ⟨x, hx, w, hw, rfl⟩
    rw [Set.mem_neg] at hw
    have hxy : x ≤ -w := A.1.rel_extent_intent hx hw
    have hnonpos : x + w ≤ 0 := by
      simpa using (add_le_add hxy (le_refl w))
    exact hnonpos.trans hz

/-- Bounded cuts of an Archimedean lattice-ordered group form an additive commutative group. -/
noncomputable instance [IsVLArchimedean X] : AddCommGroup (BoundedCut X) where
  __ := (inferInstance : AddCommMonoid (BoundedCut X))
  neg := negCut
  sub := fun A B ↦ addCut A (negCut B)
  sub_eq_add_neg := by intros; rfl
  neg_add_cancel := by
    intro A
    change addCut (negCut A) A = principal 0
    rw [addCut_comm, addCut_negCut]
  zsmul := zsmulRec

omit [IsOrderedAddMonoid X] in
/-- The principal cuts form an order-dense subset of the bounded cuts. -/
theorem principal_orderDense :
    IsOrderDense (Set.range (principal : X → BoundedCut X)) := by
  intro A hA
  have hnot : ¬ A ≤ principal (0 : X) := not_le_of_gt hA
  have hx : ∃ x ∈ A.left, ¬ x ≤ 0 := by
    by_contra h
    apply hnot
    change A.1.left ⊆ (DedekindCut.principal (0 : X)).left
    intro x hx
    by_contra hnx
    exact h ⟨x, hx, hnx⟩
  obtain ⟨x, hxA, hxnot⟩ := hx
  have hp : 0 < x⁺ := by
    apply lt_of_le_of_ne (posPart_nonneg x)
    intro heq
    exact hxnot ((le_posPart x).trans heq.symm.le)
  refine ⟨principal x⁺, ⟨x⁺, rfl⟩, ?_, ?_⟩
  · exact DedekindCut.principal_lt_principal.mpr hp
  · rw [show x⁺ = x ⊔ 0 from rfl, principal_sup]
    exact sup_le ((principal_le_iff A x).mpr hxA) hA.le

end BoundedCut

end AdditiveGroup

noncomputable section Scalar

open scoped Pointwise

variable {X : Type u} [Lattice X] [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X]

namespace BoundedCut

/-- Multiplication of a bounded cut by a positive real scalar, scaling its lower and upper
parts. -/
private def posSmulCut (r : ℝ) (hr : 0 < r) (A : BoundedCut X) : BoundedCut X :=
  ⟨{
    extent := r • A.left
    intent := r • A.right
    upperPolar_extent := (upperBounds_smul_of_pos hr).trans
      (congrArg (r • ·) (DedekindCut.upperBounds_left A.1))
    lowerPolar_intent := (lowerBounds_smul_of_pos hr).trans
      (congrArg (r • ·) (DedekindCut.lowerBounds_right A.1))
  }, A.left_nonempty.smul_set, A.right_nonempty.smul_set⟩

/-- The lower part of a positively scaled cut is the scaled lower part. -/
@[simp] private lemma posSmulCut_left (r : ℝ) (hr : 0 < r) (A : BoundedCut X) :
    (posSmulCut r hr A).left = r • A.left := rfl

/-- Positive scalar multiplication sends a principal cut to the scaled principal cut. -/
private lemma posSmulCut_principal (r : ℝ) (hr : 0 < r) (x : X) :
    posSmulCut r hr (principal x) = principal (r • x) :=
  Subtype.ext (DedekindCut.ext ((OrderIso.smulRight hr).image_Iic x))

/-- Successive positive scalings multiply their scalars. -/
private lemma posSmulCut_mul (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (A : BoundedCut X) :
    posSmulCut r hr (posSmulCut s hs A) =
      posSmulCut (r * s) (mul_pos hr hs) A :=
  Subtype.ext (DedekindCut.ext (smul_smul r s A.left))

/-- Scaling a cut by one leaves it unchanged. -/
private lemma posSmulCut_one (A : BoundedCut X) :
    posSmulCut 1 (by norm_num) A = A :=
  Subtype.ext (DedekindCut.ext (one_smul ℝ A.left))

/-- Positive scalar multiplication distributes over cut addition. -/
private lemma posSmulCut_add (r : ℝ) (hr : 0 < r)
    (A B : BoundedCut X) :
    posSmulCut r hr (A + B) = posSmulCut r hr A + posSmulCut r hr B := by
  apply Subtype.ext
  apply DedekindCut.ext'
  change r • upperBounds (A.left + B.left) = upperBounds (r • A.left + r • B.left)
  rw [← smul_add, upperBounds_smul_of_pos hr]

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] in
/-- The lower part of a cut is closed under binary suprema. -/
private lemma left_sup_mem (A : BoundedCut X) {x y : X}
    (hx : x ∈ A.left) (hy : y ∈ A.left) : x ⊔ y ∈ A.left := by
  change x ⊔ y ∈ A.1.left
  rw [← DedekindCut.lowerBounds_right]
  intro z hz
  exact sup_le (A.1.rel_extent_intent hx hz) (A.1.rel_extent_intent hy hz)

/-- For positive scalars, scalar addition distributes over cuts. -/
private lemma posSmulCut_add_scalar (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (A : BoundedCut X) :
    posSmulCut (r + s) (add_pos hr hs) A =
      posSmulCut r hr A + posSmulCut s hs A := by
  apply le_antisymm
  · change (r + s) • A.left ⊆ (Concept.ofObjects (· ≤ ·) (r • A.left + s • A.left)).extent
    rintro z ⟨x, hx, rfl⟩
    change (r + s) • x ∈ lowerBounds (upperBounds (r • A.left + s • A.left))
    intro y hy
    rw [add_smul]
    exact hy (Set.add_mem_add ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩)
  · change Concept.ofObjects (· ≤ ·) (r • A.left + s • A.left) ≤
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
    posSmulCut r hr (-A) = -posSmulCut r hr A :=
  Subtype.ext (DedekindCut.ext (Set.smul_set_neg r A.right))

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
      exact Set.smul_set_mono hAB
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

end Scalar
end DedekindCompletion
