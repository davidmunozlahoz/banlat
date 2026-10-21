/-
Authors: Pedro Tradacete
-/

import Mathlib.Order.Completion
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Bounded Dedekind cuts

Nonempty lower and upper parts of Mathlib's Dedekind cuts form the
conditionally complete lattice underlying the completion construction.
-/

open Set

namespace DedekindCompletion

universe u

variable {X : Type u} [PartialOrder X]

/-- A nonempty, proper Dedekind cut, represented by its lower and upper parts. -/
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

/-- The principal bounded cut of an element of the original order. -/
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

/-- The supremum of a nonempty bounded-above family of bounded cuts is bounded. -/
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
end DedekindCompletion
