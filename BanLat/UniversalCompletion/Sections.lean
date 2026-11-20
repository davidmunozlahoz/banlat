/-
Authors: Pedro Tradacete
-/

import BanLat.Substructures.Band.BandProjection.Complete
import BanLat.Substructures.Band.BandProjection.OrderContinuous

/-!
# Compatible sections over covering families of projection bands

For a Dedekind complete vector lattice, compatible sections on a downward closed
covering family of projection bands form a Dedekind complete vector lattice under
coordinatewise operations. A family is covering when its supremum is the whole space;
such families, containing the zero band, are called band domains. Restriction to a
smaller band domain admits bounded extensions of nonnegative sections. These section
spaces supply representatives for the universal completion.
-/

noncomputable section

namespace UniversalCompletionConstruction

variable {D : Type*} [AddCommGroup D] [ConditionallyCompleteLattice D]
  [IsOrderedAddMonoid D] [VectorLattice D]

/-! ### Band domains and compatible sections -/

/-- A **band domain** is a downward closed covering family of projection bands containing
the zero band. -/
structure BandDomain (D : Type*) [AddCommGroup D] [ConditionallyCompleteLattice D]
    [IsOrderedAddMonoid D] [VectorLattice D] where
  /-- Projection bands in the domain. -/
  carrier : Set (ProjectionBand D)
  /-- The domain is downward closed. -/
  lower : ∀ {B C : ProjectionBand D}, B ≤ C → C ∈ carrier → B ∈ carrier
  /-- The family covers the whole space: its supremum is the top band. -/
  cover : sSup carrier = ⊤
  /-- The zero band belongs to the domain. -/
  bot_mem : ⊥ ∈ carrier

namespace BandDomain

/-- Domains coerce to their underlying sets of projection bands. -/
instance : SetLike (BandDomain D) (ProjectionBand D) where
  coe := BandDomain.carrier
  coe_injective A C h := by
    cases A
    cases C
    congr

/-- Two domains are equal when they contain the same projection bands. -/
@[ext] theorem ext {A C : BandDomain D} (h : ∀ B, B ∈ A ↔ B ∈ C) : A = C :=
  SetLike.ext h

/-- The full set of projection bands is a domain. -/
def full : BandDomain D where
  carrier := Set.univ
  lower := by simp
  cover := by simp
  bot_mem := Set.mem_univ _

/-- The intersection of two downward closed covering families is again
a downward closed covering family. -/
def inter (A C : BandDomain D) : BandDomain D where
  carrier := A.carrier ∩ C.carrier
  lower := by
    intro B B' hBB' hB'
    exact ⟨A.lower hBB' hB'.1, C.lower hBB' hB'.2⟩
  cover := by
    apply top_unique
    calc
      ⊤ = sSup A.carrier ⊓ sSup C.carrier := by rw [A.cover, C.cover, top_inf_eq]
      _ = ⨆ p ∈ A.carrier ×ˢ C.carrier, p.1 ⊓ p.2 := sSup_inf_sSup
      _ ≤ sSup (A.carrier ∩ C.carrier) := by
        apply iSup₂_le
        intro p hp
        apply le_sSup
        exact ⟨A.lower inf_le_left hp.1, C.lower inf_le_right hp.2⟩
  bot_mem := ⟨A.bot_mem, C.bot_mem⟩

end BandDomain

/-- A compatible local section on a downward closed covering family of projection bands.
This defines a compatible family of vectors indexed by the projection bands in `A`, such that
the vectors belong to the corresponding bands and restrict by band projection. -/
structure Section (A : BandDomain D) where
  /-- Value of the section at a projection band in its domain. -/
  value : A.carrier → D
  /-- Each value belongs to its indexing band. -/
  mem_band : ∀ B : A.carrier, value B ∈ (B.1 : Set D)
  /-- Values restrict by band projection. -/
  compatible : ∀ (B C : A.carrier), B.1 ≤ C.1 →
    B.1.bandProjection (value C) = value B

namespace Section

variable {A C : BandDomain D}

/-- Sections on the same domain are determined by their coordinate values. -/
@[ext] theorem ext {x y : Section A}
    (h : ∀ B : A.carrier, x.value B = y.value B) : x = y := by
  cases x with
  | mk xv xm xc =>
    cases y with
    | mk yv ym yc =>
      congr 1
      funext B
      exact h B

/-- The zero local section. -/
def zero (A : BandDomain D) : Section A where
  value := fun _ ↦ 0
  mem_band B := B.1.toBand.toOrderIdeal.toSubmodule.zero_mem
  compatible B _ _ := map_zero B.1.bandProjection

/-- Pointwise addition of sections on one domain. -/
def add (x y : Section A) : Section A where
  value B := x.value B + y.value B
  mem_band B := B.1.toBand.toOrderIdeal.toSubmodule.add_mem
    (x.mem_band B) (y.mem_band B)
  compatible B C hBC := by
    rw [map_add, x.compatible B C hBC, y.compatible B C hBC]

/-- Pointwise negation of a section. -/
def neg (x : Section A) : Section A where
  value B := -x.value B
  mem_band B := B.1.toBand.toOrderIdeal.toSubmodule.neg_mem (x.mem_band B)
  compatible B C hBC := by
    rw [map_neg, x.compatible B C hBC]

/-- Pointwise scalar multiplication of a section. -/
def smul (c : ℝ) (x : Section A) : Section A where
  value B := c • x.value B
  mem_band B := B.1.toBand.toOrderIdeal.toSubmodule.smul_mem c (x.mem_band B)
  compatible B C hBC := by
    rw [map_smul, x.compatible B C hBC]

/-- Pointwise lattice supremum of sections. -/
def sup (x y : Section A) : Section A where
  value B := x.value B ⊔ y.value B
  mem_band B := B.1.toBand.sup_mem (x.mem_band B) (y.mem_band B)
  compatible B C hBC := by
    have hsup := (VecLatHom.ofIsVecLatHom B.1.bandProjection
      B.1.bandProjection_isVecLatHom).map_sup' (x.value C) (y.value C)
    change B.1.bandProjection (x.value C ⊔ y.value C) =
      B.1.bandProjection (x.value C) ⊔ B.1.bandProjection (y.value C) at hsup
    rw [hsup, x.compatible B C hBC, y.compatible B C hBC]

/-- Pointwise lattice infimum of sections. -/
def inf (x y : Section A) : Section A where
  value B := x.value B ⊓ y.value B
  mem_band B := B.1.toBand.inf_mem (x.mem_band B) (y.mem_band B)
  compatible B C hBC := by
    have hinf := (VecLatHom.ofIsVecLatHom B.1.bandProjection
      B.1.bandProjection_isVecLatHom).map_inf' (x.value C) (y.value C)
    change B.1.bandProjection (x.value C ⊓ y.value C) =
      B.1.bandProjection (x.value C) ⊓ B.1.bandProjection (y.value C) at hinf
    rw [hinf, x.compatible B C hBC, y.compatible B C hBC]

/-- The zero section on a fixed domain. -/
instance : Zero (Section A) := ⟨zero A⟩

/-- Pointwise addition of sections. -/
instance : Add (Section A) := ⟨add⟩

/-- Pointwise negation of sections. -/
instance : Neg (Section A) := ⟨neg⟩

/-- Subtraction of sections. -/
instance : Sub (Section A) := ⟨fun x y ↦ add x (neg y)⟩

/-- Sections on a fixed domain form an additive commutative monoid. -/
instance : AddCommMonoid (Section A) where
  zero := zero A
  add := add
  add_assoc x y z := by
    ext B
    exact add_assoc (x.value B) (y.value B) (z.value B)
  zero_add x := by
    ext B
    exact zero_add (x.value B)
  add_zero x := by
    ext B
    exact add_zero (x.value B)
  add_comm x y := by
    ext B
    exact add_comm (x.value B) (y.value B)
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intros; rfl

/-- Sections on a fixed domain form an additive commutative group. -/
instance : AddCommGroup (Section A) where
  __ := (inferInstance : AddCommMonoid (Section A))
  neg := neg
  sub x y := add x (neg y)
  sub_eq_add_neg := by intros; rfl
  neg_add_cancel x := by
    ext B
    exact neg_add_cancel (x.value B)
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl

/-- Pointwise real scalar multiplication of sections. -/
instance : SMul ℝ (Section A) := ⟨smul⟩

/-- Sections on a fixed domain form a real module. -/
instance : Module ℝ (Section A) where
  one_smul x := by ext B; exact one_smul ℝ (x.value B)
  mul_smul a b x := by ext B; exact mul_smul a b (x.value B)
  smul_zero a := by ext B; exact smul_zero a
  smul_add a x y := by ext B; exact smul_add a (x.value B) (y.value B)
  add_smul a b x := by ext B; exact add_smul a b (x.value B)
  zero_smul x := by ext B; exact zero_smul ℝ (x.value B)

/-- Pointwise order on sections. -/
instance : LE (Section A) := ⟨fun x y ↦ ∀ B, x.value B ≤ y.value B⟩

/-- The pointwise relation on sections is a partial order. -/
instance : PartialOrder (Section A) where
  le_refl x B := le_refl (x.value B)
  le_trans x y z hxy hyz B := (hxy B).trans (hyz B)
  le_antisymm x y hxy hyx := by
    ext B
    exact le_antisymm (hxy B) (hyx B)

/-- Sections on a fixed domain form a lattice with the pointwise operations. -/
instance : Lattice (Section A) where
  sup := sup
  inf := inf
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ hxz hyz B := sup_le (hxz B) (hyz B)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ hxy hxz B := le_inf (hxy B) (hxz B)

/-- Addition of sections respects the pointwise order. -/
instance : IsOrderedAddMonoid (Section A) where
  add_le_add_left x y hxy z B := by
    change x.value B + z.value B ≤ y.value B + z.value B
    exact add_le_add_left (hxy B) (z.value B)

/-- Positive scalar multiplication respects the pointwise order. -/
instance : PosSMulMono ℝ (Section A) where
  smul_le_smul_of_nonneg_left := by
    intro c hc x y hxy B
    change c • x.value B ≤ c • y.value B
    exact smul_le_smul_of_nonneg_left (hxy B) hc

/-- Sections on a fixed domain form a vector lattice. -/
instance : VectorLattice (Section A) where
  __ := (inferInstance : Module ℝ (Section A))
  __ := (inferInstance : PosSMulMono ℝ (Section A))

/-- Every fixed-domain section space has coordinatewise bounded suprema. -/
private theorem exists_isLUB_with_value (A : BandDomain D) (S : Set (Section A))
    (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ s : Section A, IsLUB S s ∧
      ∀ B : A.carrier, s.value B = sSup ((fun x : Section A ↦ x.value B) '' S) := by
  -- Form coordinatewise suprema; band projections preserve them.
  let coord (B : A.carrier) : Set D := (fun x : Section A ↦ x.value B) '' S
  have hcoord_ne (B : A.carrier) : (coord B).Nonempty := hne.image _
  obtain ⟨u, hu⟩ := hbdd
  have hcoord_bdd (B : A.carrier) : BddAbove (coord B) := by
    refine ⟨u.value B, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hu hx B
  let s : Section A := {
    value := fun B ↦ sSup (coord B)
    mem_band := by
      intro B
      apply B.1.toBand.sSup_mem (S := coord B)
      · rintro z ⟨x, hx, rfl⟩
        exact x.mem_band B
      · exact hcoord_ne B
      · exact isLUB_csSup (hcoord_ne B) (hcoord_bdd B)
    compatible := by
      intro B C hBC
      have hmap : B.1.bandProjection '' coord C = coord B := by
        ext z
        constructor
        · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, (x.compatible B C hBC).symm⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.value C, ⟨x, hx, rfl⟩, x.compatible B C hBC⟩
      rw [← (B.1.isLUB_bandProjection_image (isLUB_csSup (hcoord_ne C) (hcoord_bdd C))).csSup_eq
        ((hcoord_ne C).image _), hmap]
  }
  refine ⟨s, ?_, fun _ ↦ rfl⟩
  constructor
  · intro x hx B
    exact le_csSup (hcoord_bdd B) ⟨x, hx, rfl⟩
  · intro v hv B
    apply csSup_le (hcoord_ne B)
    rintro z ⟨x, hx, rfl⟩
    exact hv hx B

/-- Every fixed-domain section space is Dedekind complete. -/
theorem exists_isLUB (A : BandDomain D) (S : Set (Section A))
    (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ s : Section A, IsLUB S s := by
  obtain ⟨s, hs, _⟩ := exists_isLUB_with_value A S hne hbdd
  exact ⟨s, hs⟩

/-- Every band domain has a zero section. -/
instance (A : BandDomain D) : Nonempty (Section A) := ⟨0⟩

/-- Sections on a fixed domain are Dedekind complete. -/
noncomputable instance (A : BandDomain D) : ConditionallyCompleteLattice (Section A) :=
  conditionallyCompleteLatticeOfPosSet (Section A)
    (fun {S} _ hne hbdd ↦ exists_isLUB A S hne hbdd)

/-- The value of a bounded supremum is the supremum of its coordinate values. -/
theorem sSup_value (A : BandDomain D) (S : Set (Section A))
    (hne : S.Nonempty) (hbdd : BddAbove S) (B : A.carrier) :
    (sSup S).value B = sSup ((fun x : Section A ↦ x.value B) '' S) := by
  obtain ⟨s, hs, hvalue⟩ := exists_isLUB_with_value A S hne hbdd
  have heq : sSup S = s := (isLUB_csSup hne hbdd).unique hs
  rw [heq]
  exact hvalue B

/-! ### Restriction and bounded extension -/

/-- Restriction of a section to a smaller downward closed covering family. -/
def restrict (x : Section C) (hAC : A.carrier ⊆ C.carrier) : Section A where
  value B := x.value ⟨B.1, hAC B.2⟩
  mem_band B := x.mem_band ⟨B.1, hAC B.2⟩
  compatible B B' hBB' := x.compatible ⟨B.1, hAC B.2⟩
    ⟨B'.1, hAC B'.2⟩ hBB'

/-- Projecting a coordinate to any band reads off its restriction. -/
theorem projection (x : Section A) (C : A.carrier) (B : ProjectionBand D) :
    B.bandProjection (x.value C) =
      x.value ⟨B ⊓ C.1, A.lower inf_le_right C.2⟩ := by
  have h := x.compatible ⟨B ⊓ C.1, A.lower inf_le_right C.2⟩ C inf_le_right
  rw [ProjectionBand.bandProjection_inf] at h
  change B.bandProjection (C.1.bandProjection (x.value C)) = _ at h
  rwa [C.1.bandProjection_eq_of_mem (x.mem_band C)] at h

/-- The values of a section viewed on a single band. -/
private def overlapSet (y : Section A) (B : ProjectionBand D) : Set D :=
  Set.range (fun a : A.carrier ↦ B.bandProjection (y.value a))

private theorem overlapSet_nonempty (y : Section A) (B : ProjectionBand D) :
    (overlapSet y B).Nonempty := by
  exact ⟨_, ⟨⟨⊥, A.bot_mem⟩, rfl⟩⟩

/-- A section dominated by a nonnegative section remains bounded by that section
after projection to any band in the larger domain. -/
private theorem overlapSet_le (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : ∀ b : C.carrier, 0 ≤ x.value b)
    (hyx : ∀ a : A.carrier, y.value a ≤ x.value ⟨a.1, hAC a.2⟩)
    (b : C.carrier) : x.value b ∈ upperBounds (overlapSet y b.1) := by
  rintro z ⟨a, rfl⟩
  let m : A.carrier := ⟨b.1 ⊓ a.1, A.lower inf_le_right a.2⟩
  have hmC : (b.1 ⊓ a.1) ∈ C.carrier := hAC m.2
  have hym : b.1.bandProjection (y.value a) = y.value m := y.projection a b.1
  change b.1.bandProjection (y.value a) ≤ x.value b
  rw [hym]
  calc
    y.value m ≤ x.value ⟨m.1, hAC m.2⟩ := hyx m
    _ = (b.1 ⊓ a.1).bandProjection (x.value b) := by
      exact (x.compatible ⟨m.1, hmC⟩ b inf_le_left).symm
    _ ≤ x.value b :=
      Positive.le_iff.mp (b.1 ⊓ a.1).bandProjection_le_id _ (hxpos b)

private theorem overlapSet_bddAbove (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : ∀ b : C.carrier, 0 ≤ x.value b)
    (hyx : ∀ a : A.carrier, y.value a ≤ x.value ⟨a.1, hAC a.2⟩)
    (b : C.carrier) : BddAbove (overlapSet y b.1) :=
  ⟨x.value b, overlapSet_le x y hAC hxpos hyx b⟩

/-- Suprema of overlap values define a section on the larger domain. -/
private def boundedExtend (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : ∀ b : C.carrier, 0 ≤ x.value b)
    (hyx : ∀ a : A.carrier, y.value a ≤ x.value ⟨a.1, hAC a.2⟩) :
    Section C where
  value b := sSup (overlapSet y b.1)
  mem_band b := by
    apply b.1.toBand.sSup_mem
      (S := overlapSet y b.1)
    · rintro z ⟨a, rfl⟩
      exact b.1.bandProjection_mem _
    · exact overlapSet_nonempty y b.1
    · exact isLUB_csSup (overlapSet_nonempty y b.1)
        (overlapSet_bddAbove x y hAC hxpos hyx b)
  compatible b c hbc := by
    have hne := overlapSet_nonempty y c.1
    have hbdd := overlapSet_bddAbove x y hAC hxpos hyx c
    rw [← (b.1.isLUB_bandProjection_image (isLUB_csSup hne hbdd)).csSup_eq (hne.image _)]
    congr 1
    ext z
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (ProjectionBand.bandProjection_comp_of_le b.1 c.1 hbc (y.value a)).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨c.1.bandProjection (y.value a), ⟨a, rfl⟩,
        ProjectionBand.bandProjection_comp_of_le b.1 c.1 hbc (y.value a)⟩

/-- The bounded extension agrees with the original section on its domain. -/
private theorem boundedExtend_agrees (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : ∀ b : C.carrier, 0 ≤ x.value b)
    (hypos : ∀ a : A.carrier, 0 ≤ y.value a)
    (hyx : ∀ a : A.carrier, y.value a ≤ x.value ⟨a.1, hAC a.2⟩)
    (b : A.carrier) :
    (boundedExtend x y hAC hxpos hyx).value ⟨b.1, hAC b.2⟩ = y.value b := by
  change sSup (overlapSet y b.1) = y.value b
  have hbdd := overlapSet_bddAbove x y hAC hxpos hyx ⟨b.1, hAC b.2⟩
  have hne := overlapSet_nonempty y b.1
  apply le_antisymm
  · apply csSup_le hne
    rintro z ⟨a, rfl⟩
    let m : A.carrier := ⟨b.1 ⊓ a.1, A.lower inf_le_left b.2⟩
    have hym : b.1.bandProjection (y.value a) = y.value m := y.projection a b.1
    change b.1.bandProjection (y.value a) ≤ y.value b
    rw [hym]
    calc
      y.value m = (b.1 ⊓ a.1).bandProjection (y.value b) :=
        (y.compatible m b inf_le_left).symm
      _ ≤ y.value b :=
        Positive.le_iff.mp (b.1 ⊓ a.1).bandProjection_le_id _ (hypos b)
  · apply le_csSup hbdd
    refine ⟨b, ?_⟩
    change b.1.bandProjection (y.value b) = y.value b
    exact b.1.bandProjection_eq_of_mem (y.mem_band b)

private theorem boundedExtend_nonneg (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : ∀ b : C.carrier, 0 ≤ x.value b)
    (hypos : ∀ a : A.carrier, 0 ≤ y.value a)
    (hyx : ∀ a : A.carrier, y.value a ≤ x.value ⟨a.1, hAC a.2⟩)
    (b : C.carrier) :
    0 ≤ (boundedExtend x y hAC hxpos hyx).value b := by
  change 0 ≤ sSup (overlapSet y b.1)
  let a : A.carrier := ⟨⊥, A.bot_mem⟩
  have hterm : 0 ≤ b.1.bandProjection (y.value a) :=
    (Positive.zero_le_iff.mp b.1.bandProjection_nonneg) _ (hypos a)
  exact hterm.trans (le_csSup (overlapSet_bddAbove x y hAC hxpos hyx b)
    ⟨a, rfl⟩)

private theorem boundedExtend_le (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : ∀ b : C.carrier, 0 ≤ x.value b)
    (hyx : ∀ a : A.carrier, y.value a ≤ x.value ⟨a.1, hAC a.2⟩)
    (b : C.carrier) :
    (boundedExtend x y hAC hxpos hyx).value b ≤ x.value b := by
  change sSup (overlapSet y b.1) ≤ x.value b
  exact csSup_le (overlapSet_nonempty y b.1)
    (overlapSet_le x y hAC hxpos hyx b)

/-- The image of restriction is order solid: a positive section below a
restricted positive section extends to the larger domain with the same bound. -/
theorem exists_bounded_extension (x : Section C) (y : Section A)
    (hAC : A.carrier ⊆ C.carrier)
    (hxpos : 0 ≤ x) (hypos : 0 ≤ y)
    (hyx : y ≤ x.restrict hAC) :
    ∃ z : Section C, 0 ≤ z ∧ z ≤ x ∧ z.restrict hAC = y :=
  ⟨boundedExtend x y hAC hxpos hyx,
    boundedExtend_nonneg x y hAC hxpos hypos hyx,
    boundedExtend_le x y hAC hxpos hyx,
    Section.ext (boundedExtend_agrees x y hAC hxpos hypos hyx)⟩

end Section

end UniversalCompletionConstruction
