/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.Construction
import BanLat.UniversalCompletion.Sections

/-!
# Construction of the universal completion

This module constructs the universal completion of an Archimedean vector lattice `X`.
First, bounded Dedekind cuts give its Dedekind completion. Compatible local sections
over downward closed covering families of projection bands then give a Dedekind and
laterally complete vector lattice of germs. Composing the canonical embeddings realizes
`X` as an order-dense vector sublattice of `UniversalCompletion X`. The intermediate Dedekind
completion embeds as an order-dense ideal. The band-section construction itself
applies to any Dedekind complete vector lattice.
-/

noncomputable section

namespace UniversalCompletionConstruction

variable {D : Type*} [AddCommGroup D] [ConditionallyCompleteLattice D]
  [IsOrderedAddMonoid D] [VectorLattice D]

/-! ### Germs of sections and their vector-lattice structure

Operations are lifted from representatives of local sections restricted to a common
covering domain. The algebraic laws below are checked on their coordinates.
-/

/-- A local section together with its covering domain. -/
abbrev RawSection (D : Type*) [AddCommGroup D] [ConditionallyCompleteLattice D]
    [IsOrderedAddMonoid D] [VectorLattice D] :=
  Σ A : BandDomain D, Section A

/-- Two local sections represent the same germ when their coordinates agree
where both are defined. -/
def SectionAgreement (r s : RawSection D) : Prop :=
  ∀ (B : ProjectionBand D) (hr : B ∈ r.1.carrier) (hs : B ∈ s.1.carrier),
    r.2.value ⟨B, hr⟩ = s.2.value ⟨B, hs⟩

private theorem sectionAgreement_refl (r : RawSection D) : SectionAgreement r r := by
  intro B hr hs
  rfl

private theorem sectionAgreement_symm {r s : RawSection D}
    (h : SectionAgreement r s) : SectionAgreement s r := by
  intro B hs hr
  exact (h B hr hs).symm

private theorem sectionAgreement_trans {r s t : RawSection D}
    (hrs : SectionAgreement r s) (hst : SectionAgreement s t) :
    SectionAgreement r t := by
  intro B hr ht
  apply ProjectionBand.eq_of_bandProjection_eq_on_cover s.1.carrier s.1.cover
  intro K hK
  let J : ProjectionBand D := K ⊓ B
  have hJr : J ∈ r.1.carrier := r.1.lower inf_le_right hr
  have hJs : J ∈ s.1.carrier := s.1.lower inf_le_left hK
  have hJt : J ∈ t.1.carrier := t.1.lower inf_le_right ht
  calc
    K.bandProjection (r.2.value ⟨B, hr⟩)
        = r.2.value ⟨J, hJr⟩ := r.2.projection ⟨B, hr⟩ K
    _ = s.2.value ⟨J, hJs⟩ := hrs J hJr hJs
    _ = t.2.value ⟨J, hJt⟩ := hst J hJs hJt
    _ = K.bandProjection (t.2.value ⟨B, ht⟩) :=
      (t.2.projection ⟨B, ht⟩ K).symm

/-- Equivalence relation used to form germs of local sections. -/
def sectionSetoid (D : Type*) [AddCommGroup D] [ConditionallyCompleteLattice D]
    [IsOrderedAddMonoid D] [VectorLattice D] : Setoid (RawSection D) where
  r := SectionAgreement
  iseqv := ⟨sectionAgreement_refl, sectionAgreement_symm,
    sectionAgreement_trans⟩

/-- The carrier of the universal completion construction. -/
abbrev BandGerms (D : Type*) [AddCommGroup D] [ConditionallyCompleteLattice D]
    [IsOrderedAddMonoid D] [VectorLattice D] :=
  Quotient (sectionSetoid D)

/-- Add representatives after restriction to their common domain. -/
private def rawAdd (r s : RawSection D) : RawSection D :=
  let T := r.1.inter s.1
  ⟨T,
    r.2.restrict (A := T) (fun _ h ↦ h.1) +
      s.2.restrict (A := T) (fun _ h ↦ h.2)⟩

private def rawNeg (r : RawSection D) : RawSection D := ⟨r.1, -r.2⟩

private def rawZero : RawSection D := ⟨BandDomain.full, (0 : Section BandDomain.full)⟩

private def rawSmul (c : ℝ) (r : RawSection D) : RawSection D := ⟨r.1, c • r.2⟩

private def rawSup (r s : RawSection D) : RawSection D :=
  let T := r.1.inter s.1
  ⟨T,
    Section.sup (r.2.restrict (A := T) (fun _ h ↦ h.1))
      (s.2.restrict (A := T) (fun _ h ↦ h.2))⟩

private def rawInf (r s : RawSection D) : RawSection D :=
  let T := r.1.inter s.1
  ⟨T,
    Section.inf (r.2.restrict (A := T) (fun _ h ↦ h.1))
      (s.2.restrict (A := T) (fun _ h ↦ h.2))⟩

private theorem rawAdd_congr {r r' s s' : RawSection D}
    (hrr' : SectionAgreement r r') (hss' : SectionAgreement s s') :
    SectionAgreement (rawAdd r s) (rawAdd r' s') := by
  intro B hB hB'
  change r.2.value ⟨B, hB.1⟩ + s.2.value ⟨B, hB.2⟩ =
    r'.2.value ⟨B, hB'.1⟩ + s'.2.value ⟨B, hB'.2⟩
  rw [hrr' B hB.1 hB'.1, hss' B hB.2 hB'.2]

private theorem rawNeg_congr {r s : RawSection D} (hrs : SectionAgreement r s) :
    SectionAgreement (rawNeg r) (rawNeg s) := by
  intro B hr hs
  change -(r.2.value ⟨B, hr⟩) = -(s.2.value ⟨B, hs⟩)
  rw [hrs B hr hs]

private theorem rawSmul_congr (c : ℝ) {r s : RawSection D}
    (hrs : SectionAgreement r s) :
    SectionAgreement (rawSmul c r) (rawSmul c s) := by
  intro B hr hs
  change c • r.2.value ⟨B, hr⟩ = c • s.2.value ⟨B, hs⟩
  rw [hrs B hr hs]

private theorem rawSup_congr {r r' s s' : RawSection D}
    (hrr' : SectionAgreement r r') (hss' : SectionAgreement s s') :
    SectionAgreement (rawSup r s) (rawSup r' s') := by
  intro B hB hB'
  change r.2.value ⟨B, hB.1⟩ ⊔ s.2.value ⟨B, hB.2⟩ =
    r'.2.value ⟨B, hB'.1⟩ ⊔ s'.2.value ⟨B, hB'.2⟩
  rw [hrr' B hB.1 hB'.1, hss' B hB.2 hB'.2]

private theorem rawInf_congr {r r' s s' : RawSection D}
    (hrr' : SectionAgreement r r') (hss' : SectionAgreement s s') :
    SectionAgreement (rawInf r s) (rawInf r' s') := by
  intro B hB hB'
  change r.2.value ⟨B, hB.1⟩ ⊓ s.2.value ⟨B, hB.2⟩ =
    r'.2.value ⟨B, hB'.1⟩ ⊓ s'.2.value ⟨B, hB'.2⟩
  rw [hrr' B hB.1 hB'.1, hss' B hB.2 hB'.2]

/-- Addition of germs is induced by addition on a common domain. -/
instance : Add (BandGerms D) :=
  ⟨Quotient.map₂ rawAdd (fun _ _ h _ _ k ↦ rawAdd_congr h k)⟩

/-- The germ of the zero section. -/
instance : Zero (BandGerms D) := ⟨Quotient.mk (sectionSetoid D) rawZero⟩

/-- Negation of germs is induced by negation of sections. -/
instance : Neg (BandGerms D) := ⟨Quotient.map rawNeg (fun _ _ h ↦ rawNeg_congr h)⟩

/-- Subtraction of germs. -/
instance : Sub (BandGerms D) := ⟨fun x y ↦ x + -y⟩

/-- Real scalar multiplication of germs. -/
instance : SMul ℝ (BandGerms D) :=
  ⟨fun c ↦ Quotient.map (rawSmul c) (fun _ _ h ↦ rawSmul_congr c h)⟩

/-- Supremum of two germs is computed on a common domain. -/
instance : Max (BandGerms D) :=
  ⟨Quotient.map₂ rawSup (fun _ _ h _ _ k ↦ rawSup_congr h k)⟩

/-- Infimum of two germs is computed on a common domain. -/
instance : Min (BandGerms D) :=
  ⟨Quotient.map₂ rawInf (fun _ _ h _ _ k ↦ rawInf_congr h k)⟩

/-- Germs form an additive commutative monoid. -/
instance : AddCommMonoid (BandGerms D) where
  add_assoc := by
    intro p q r
    induction p using Quotient.inductionOn with | _ a =>
    induction q using Quotient.inductionOn with | _ b =>
    induction r using Quotient.inductionOn with | _ c =>
    apply Quotient.sound
    intro B hleft hright
    change (a.2.value ⟨B, hleft.1.1⟩ + b.2.value ⟨B, hleft.1.2⟩) +
        c.2.value ⟨B, hleft.2⟩ =
      a.2.value ⟨B, hright.1⟩ +
        (b.2.value ⟨B, hright.2.1⟩ + c.2.value ⟨B, hright.2.2⟩)
    exact add_assoc _ _ _
  zero_add := by
    intro p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B hleft hright
    change (0 : D) + a.2.value ⟨B, hleft.2⟩ = a.2.value ⟨B, hright⟩
    exact zero_add _
  add_zero := by
    intro p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B hleft hright
    change a.2.value ⟨B, hleft.1⟩ + (0 : D) = a.2.value ⟨B, hright⟩
    exact add_zero _
  add_comm := by
    intro p q
    induction p using Quotient.inductionOn with | _ a =>
    induction q using Quotient.inductionOn with | _ b =>
    apply Quotient.sound
    intro B hleft hright
    change a.2.value ⟨B, hleft.1⟩ + b.2.value ⟨B, hleft.2⟩ =
      b.2.value ⟨B, hright.1⟩ + a.2.value ⟨B, hright.2⟩
    exact add_comm _ _
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intros; rfl

/-- Germs form an additive commutative group. -/
instance : AddCommGroup (BandGerms D) where
  __ := (inferInstance : AddCommMonoid (BandGerms D))
  sub_eq_add_neg := by intros; rfl
  neg_add_cancel := by
    intro p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B hleft hright
    change -a.2.value ⟨B, hleft.1⟩ + a.2.value ⟨B, hleft.2⟩ = (0 : D)
    exact neg_add_cancel _
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl

/-- Germs form a real module. -/
instance : Module ℝ (BandGerms D) where
  one_smul := by
    intro p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B ha hb
    change (1 : ℝ) • a.2.value ⟨B, ha⟩ = a.2.value ⟨B, hb⟩
    exact one_smul ℝ _
  mul_smul := by
    intro c d p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B ha hb
    change (c * d) • a.2.value ⟨B, ha⟩ = c • (d • a.2.value ⟨B, hb⟩)
    exact mul_smul c d _
  smul_zero := by
    intro c
    apply Quotient.sound
    intro B _ _
    change c • (0 : D) = 0
    exact smul_zero c
  smul_add := by
    intro c p q
    induction p using Quotient.inductionOn with | _ a =>
    induction q using Quotient.inductionOn with | _ b =>
    apply Quotient.sound
    intro B hleft hright
    change c • (a.2.value ⟨B, hleft.1⟩ + b.2.value ⟨B, hleft.2⟩) =
      c • a.2.value ⟨B, hright.1⟩ + c • b.2.value ⟨B, hright.2⟩
    exact smul_add c _ _
  add_smul := by
    intro c d p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B ha hb
    change (c + d) • a.2.value ⟨B, ha⟩ =
      c • a.2.value ⟨B, hb.1⟩ + d • a.2.value ⟨B, hb.2⟩
    exact add_smul c d _
  zero_smul := by
    intro p
    induction p using Quotient.inductionOn with | _ a =>
    apply Quotient.sound
    intro B ha _
    change (0 : ℝ) • a.2.value ⟨B, ha⟩ = (0 : D)
    exact zero_smul ℝ _

/-- Germs form a lattice under their coordinatewise operations. -/
noncomputable instance : Lattice (BandGerms D) :=
  Lattice.mk'
    (by
      intro p q
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      apply Quotient.sound
      intro B hleft hright
      change a.2.value ⟨B, hleft.1⟩ ⊔ b.2.value ⟨B, hleft.2⟩ =
        b.2.value ⟨B, hright.1⟩ ⊔ a.2.value ⟨B, hright.2⟩
      exact sup_comm _ _)
    (by
      intro p q r
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      induction r using Quotient.inductionOn with | _ c =>
      apply Quotient.sound
      intro B hleft hright
      change (a.2.value ⟨B, hleft.1.1⟩ ⊔ b.2.value ⟨B, hleft.1.2⟩) ⊔
          c.2.value ⟨B, hleft.2⟩ =
        a.2.value ⟨B, hright.1⟩ ⊔
          (b.2.value ⟨B, hright.2.1⟩ ⊔ c.2.value ⟨B, hright.2.2⟩)
      exact sup_assoc _ _ _)
    (by
      intro p q
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      apply Quotient.sound
      intro B hleft hright
      change a.2.value ⟨B, hleft.1⟩ ⊓ b.2.value ⟨B, hleft.2⟩ =
        b.2.value ⟨B, hright.1⟩ ⊓ a.2.value ⟨B, hright.2⟩
      exact inf_comm _ _)
    (by
      intro p q r
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      induction r using Quotient.inductionOn with | _ c =>
      apply Quotient.sound
      intro B hleft hright
      change (a.2.value ⟨B, hleft.1.1⟩ ⊓ b.2.value ⟨B, hleft.1.2⟩) ⊓
          c.2.value ⟨B, hleft.2⟩ =
        a.2.value ⟨B, hright.1⟩ ⊓
          (b.2.value ⟨B, hright.2.1⟩ ⊓ c.2.value ⟨B, hright.2.2⟩)
      exact inf_assoc _ _ _)
    (by
      intro p q
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      apply Quotient.sound
      intro B hleft hright
      change a.2.value ⟨B, hleft.1⟩ ⊔
        (a.2.value ⟨B, hleft.2.1⟩ ⊓ b.2.value ⟨B, hleft.2.2⟩) =
        a.2.value ⟨B, hright⟩
      exact sup_inf_self)
    (by
      intro p q
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      apply Quotient.sound
      intro B hleft hright
      change a.2.value ⟨B, hleft.1⟩ ⊓
        (a.2.value ⟨B, hleft.2.1⟩ ⊔ b.2.value ⟨B, hleft.2.2⟩) =
        a.2.value ⟨B, hright⟩
      exact inf_sup_self)

/-- Order on germs can be tested coordinatewise on a common domain. -/
theorem germ_le_iff (r s : RawSection D) :
    (Quotient.mk (sectionSetoid D) r : BandGerms D) ≤
      Quotient.mk (sectionSetoid D) s ↔
    ∀ (B : ProjectionBand D) (hr : B ∈ r.1.carrier)
      (hs : B ∈ s.1.carrier),
      r.2.value ⟨B, hr⟩ ≤ s.2.value ⟨B, hs⟩ := by
  change (Quotient.mk (sectionSetoid D) (rawSup r s) : BandGerms D) =
    Quotient.mk (sectionSetoid D) s ↔ _
  constructor
  · intro h B hr hs
    have heq : SectionAgreement (rawSup r s) s := Quotient.exact h
    have hB := heq B ⟨hr, hs⟩ hs
    change r.2.value ⟨B, hr⟩ ⊔ s.2.value ⟨B, hs⟩ =
      s.2.value ⟨B, hs⟩ at hB
    exact sup_eq_right.mp hB
  · intro h
    apply Quotient.sound
    intro B hB hs
    change r.2.value ⟨B, hB.1⟩ ⊔ s.2.value ⟨B, hB.2⟩ =
      s.2.value ⟨B, hs⟩
    exact sup_eq_right.mpr (h B hB.1 hB.2)

/-- Addition of germs respects the lattice order. -/
instance : IsOrderedAddMonoid (BandGerms D) where
  add_le_add_left := by
    intro p q hpq r
    induction p using Quotient.inductionOn with | _ a =>
    induction q using Quotient.inductionOn with | _ b =>
    induction r using Quotient.inductionOn with | _ c =>
    rw [germ_le_iff] at hpq
    change (Quotient.mk (sectionSetoid D) (rawAdd a c) : BandGerms D) ≤
      Quotient.mk (sectionSetoid D) (rawAdd b c)
    rw [germ_le_iff]
    intro B hleft hright
    change a.2.value ⟨B, hleft.1⟩ + c.2.value ⟨B, hleft.2⟩ ≤
      b.2.value ⟨B, hright.1⟩ + c.2.value ⟨B, hright.2⟩
    exact add_le_add_left (hpq B hleft.1 hright.1) _

/-- Positive scalar multiplication of germs respects the lattice order. -/
instance : PosSMulMono ℝ (BandGerms D) where
  smul_le_smul_of_nonneg_left := by
    intro c hc p q hpq
    induction p using Quotient.inductionOn with | _ a =>
    induction q using Quotient.inductionOn with | _ b =>
    rw [germ_le_iff] at hpq
    change (Quotient.mk (sectionSetoid D) (rawSmul c a) : BandGerms D) ≤
      Quotient.mk (sectionSetoid D) (rawSmul c b)
    rw [germ_le_iff]
    intro B ha hb
    change c • a.2.value ⟨B, ha⟩ ≤ c • b.2.value ⟨B, hb⟩
    exact smul_le_smul_of_nonneg_left (hpq B ha hb) hc

/-- Germs form a vector lattice. -/
instance : VectorLattice (BandGerms D) where
  __ := (inferInstance : Module ℝ (BandGerms D))
  __ := (inferInstance : PosSMulMono ℝ (BandGerms D))

/-! ### The embedding and Dedekind completeness -/

/-- The global section associated with an element of the original lattice. -/
def globalSection (d : D) : Section (BandDomain.full (D := D)) where
  value B := B.1.bandProjection d
  mem_band B := B.1.bandProjection_mem d
  compatible B C hBC := ProjectionBand.bandProjection_comp_of_le B.1 C.1 hBC d

/-- Map an element to its germ of projected coordinates. -/
def germOf (d : D) : BandGerms D :=
  Quotient.mk (sectionSetoid D) ⟨BandDomain.full, globalSection d⟩

/-- The map sending a lattice element to its global germ is injective. -/
theorem germOf_injective : Function.Injective (germOf (D := D)) := by
  intro x y hxy
  have h : SectionAgreement
      (⟨BandDomain.full, globalSection x⟩ : RawSection D)
      (⟨BandDomain.full, globalSection y⟩ : RawSection D) := Quotient.exact hxy
  have htop := h ⊤ (Set.mem_univ _) (Set.mem_univ _)
  change (⊤ : ProjectionBand D).bandProjection x =
    (⊤ : ProjectionBand D).bandProjection y at htop
  rw [(⊤ : ProjectionBand D).bandProjection_eq_of_mem ProjectionBand.mem_top,
    (⊤ : ProjectionBand D).bandProjection_eq_of_mem ProjectionBand.mem_top] at htop
  exact htop

/-- The canonical vector lattice homomorphism into the space of germs. -/
def germHom : VecLatHom D (BandGerms D) :=
  VecLatHom.ofIsVecLatHom germOf {
    map_add := by
      intro x y
      apply Quotient.sound
      intro B hleft hright
      change B.bandProjection (x + y) =
        B.bandProjection x + B.bandProjection y
      exact map_add B.bandProjection x y
    map_smul := by
      intro c x
      apply Quotient.sound
      intro B hleft hright
      change B.bandProjection (c • x) = c • B.bandProjection x
      exact map_smul B.bandProjection c x
    map_sup' := by
      intro x y
      apply Quotient.sound
      intro B hleft hright
      change B.bandProjection (x ⊔ y) =
        B.bandProjection x ⊔ B.bandProjection y
      have h := (VecLatHom.ofIsVecLatHom B.bandProjection
        B.bandProjection_isVecLatHom).map_sup' x y
      exact h
    map_inf' := by
      intro x y
      apply Quotient.sound
      intro B hleft hright
      change B.bandProjection (x ⊓ y) =
        B.bandProjection x ⊓ B.bandProjection y
      have h := (VecLatHom.ofIsVecLatHom B.bandProjection
        B.bandProjection_isVecLatHom).map_inf' x y
      exact h
  }

/-- The canonical map into the space of germs, which corresponds to the universal
completion, is injective. -/
theorem germHom_injective : Function.Injective (germHom (D := D)) :=
  germOf_injective

/-- A positive germ bounded by a positive germ has a representative on the
domain corresponding to the larger germ. This is the quotient form of bounded
extension. -/
private theorem exists_representative_on_upper_domain (r : RawSection D)
    (hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D))
    {v : BandGerms D} (hvpos : 0 ≤ v)
    (hvr : v ≤ Quotient.mk (sectionSetoid D) r) :
    ∃ z : Section r.1, 0 ≤ z ∧ z ≤ r.2 ∧
      v = Quotient.mk (sectionSetoid D) ⟨r.1, z⟩ := by
  induction v using Quotient.inductionOn with | _ s =>
    let A := s.1.inter r.1
    have hAr : A.carrier ⊆ r.1.carrier := fun _ h ↦ h.2
    have hAs : A.carrier ⊆ s.1.carrier := fun _ h ↦ h.1
    have hrpos' := (germ_le_iff rawZero r).mp hrpos
    have hspos' := (germ_le_iff rawZero s).mp hvpos
    have hsr := (germ_le_iff s r).mp hvr
    have hxpos : 0 ≤ r.2 := by
      intro B
      exact hrpos' B.1 (Set.mem_univ _) B.2
    have hypos : 0 ≤ s.2.restrict hAs := by
      intro B
      exact hspos' B.1 (Set.mem_univ _) (hAs B.2)
    have hyx : s.2.restrict hAs ≤ r.2.restrict hAr := by
      intro B
      exact hsr B.1 (hAs B.2) (hAr B.2)
    obtain ⟨z, hzpos, hzx, hzrestrict⟩ :=
      Section.exists_bounded_extension r.2 (s.2.restrict hAs)
        hAr hxpos hypos hyx
    refine ⟨z, hzpos, hzx, ?_⟩
    apply Quotient.sound
    intro B hsB hrB
    have hB : B ∈ A.carrier := ⟨hsB, hrB⟩
    have hcoord := congrArg (fun w : Section A ↦ w.value ⟨B, hB⟩) hzrestrict
    change z.value ⟨B, hrB⟩ = s.2.value ⟨B, hsB⟩ at hcoord
    exact hcoord.symm

/-- Nonempty bounded families of positive germs have a least upper bound. -/
private theorem exists_isLUB_positive_germs (S : Set (BandGerms D))
    (hpos : S ⊆ {v | 0 ≤ v}) (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ s : BandGerms D, IsLUB S s := by
  obtain ⟨u, hu⟩ := hbdd
  induction u using Quotient.inductionOn with | _ r =>
    obtain ⟨v₀, hv₀⟩ := hne
    have hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D) :=
      (hpos hv₀).trans (hu hv₀)
    -- Represent all members on the upper bound's domain and take their section supremum.
    let T : Set (Section r.1) :=
      {z | z ≤ r.2 ∧ (Quotient.mk (sectionSetoid D) ⟨r.1, z⟩ : BandGerms D) ∈ S}
    have hrep : ∀ v ∈ S, ∃ z ∈ T,
        v = (Quotient.mk (sectionSetoid D) ⟨r.1, z⟩ : BandGerms D) := by
      intro v hv
      obtain ⟨z, _, hzr, hvz⟩ :=
        exists_representative_on_upper_domain r hrpos (hpos hv) (hu hv)
      exact ⟨z, ⟨hzr, hvz ▸ hv⟩, hvz⟩
    obtain ⟨z₀, hz₀, _⟩ := hrep v₀ hv₀
    have hTne : T.Nonempty := ⟨z₀, hz₀⟩
    have hTbdd : BddAbove T := ⟨r.2, fun _ hz ↦ hz.1⟩
    refine ⟨Quotient.mk (sectionSetoid D) ⟨r.1, sSup T⟩, ?_⟩
    constructor
    · intro v hv
      obtain ⟨z, hz, rfl⟩ := hrep v hv
      apply (germ_le_iff ⟨r.1, z⟩ ⟨r.1, sSup T⟩).mpr
      intro B hr hs
      exact le_csSup hTbdd hz ⟨B, hr⟩
    · intro w hw
      induction w using Quotient.inductionOn with | _ t =>
        apply (germ_le_iff ⟨r.1, sSup T⟩ t).mpr
        intro B hr ht
        rw [Section.sSup_value r.1 T hTne hTbdd ⟨B, hr⟩]
        apply csSup_le (hTne.image _)
        rintro x ⟨z, hz, rfl⟩
        have hzw := hw hz.2
        exact (germ_le_iff ⟨r.1, z⟩ t).mp hzw B hr ht

/-- The zero germ witnesses nonemptiness. -/
instance : Nonempty (BandGerms D) := ⟨0⟩

/-- Bounded nonempty families of germs have suprema and infima. -/
noncomputable instance : ConditionallyCompleteLattice (BandGerms D) :=
  conditionallyCompleteLatticeOfPosSet (BandGerms D)
    (fun {S} hpos hne hbdd ↦ exists_isLUB_positive_germs S hpos hne hbdd)

/-- Dedekind completeness makes the germ lattice Archimedean. -/
instance : IsVLArchimedean (BandGerms D) :=
  IsVLArchimedean_of_sigmaConditionallyCompleteLattice

/-- Each positive coordinate is an element of the original lattice below
the germ it represents. -/
theorem coordinate_le_germ (r : RawSection D)
    (hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D))
    (B : r.1.carrier) :
    0 ≤ r.2.value B ∧
      germHom (r.2.value B) ≤ Quotient.mk (sectionSetoid D) r := by
  have hpos := (germ_le_iff rawZero r).mp hrpos
  refine ⟨hpos B.1 (Set.mem_univ _) B.2, ?_⟩
  apply (germ_le_iff ⟨BandDomain.full, globalSection (r.2.value B)⟩ r).mpr
  intro K _ hK
  let J : r.1.carrier := ⟨K ⊓ B.1, r.1.lower inf_le_left hK⟩
  have hproj : K.bandProjection (r.2.value B) = r.2.value J := r.2.projection B K
  change K.bandProjection (r.2.value B) ≤ r.2.value ⟨K, hK⟩
  rw [hproj]
  calc
    r.2.value J = J.1.bandProjection (r.2.value ⟨K, hK⟩) :=
      (r.2.compatible J ⟨K, hK⟩ inf_le_left).symm
    _ ≤ r.2.value ⟨K, hK⟩ :=
      Positive.le_iff.mp J.1.bandProjection_le_id _
        (hpos K (Set.mem_univ _) hK)

/-- The original Dedekind complete vector lattice is order dense in its
germ construction. -/
theorem germHom_orderDense : IsOrderDense (Set.range (germHom (D := D))) := by
  intro ξ hξ
  induction ξ using Quotient.inductionOn with | _ r =>
    have hrpos := (germ_le_iff rawZero r).mp hξ.le
    have hsome : ∃ B : r.1.carrier, r.2.value B ≠ 0 := by
      by_contra hn
      push Not at hn
      have heq : (Quotient.mk (sectionSetoid D) r : BandGerms D) = 0 := by
        apply Quotient.sound
        intro B hr hs
        change r.2.value ⟨B, hr⟩ = (0 : D)
        exact hn ⟨B, hr⟩
      exact (ne_of_gt hξ) heq
    obtain ⟨B, hBne⟩ := hsome
    let d := r.2.value B
    have hdpos : 0 ≤ d := hrpos B.1 (Set.mem_univ _) B.2
    have hgpos : 0 ≤ germHom d := germHom.map_nonneg hdpos
    have hgne : germHom d ≠ 0 := fun hzero ↦
      hBne (germHom_injective (hzero.trans (map_zero germHom).symm))
    have hgstrict : 0 < germHom d := lt_of_le_of_ne hgpos (Ne.symm hgne)
    have hrle : germHom d ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D) :=
      (coordinate_le_germ r hξ.le B).2
    exact ⟨germHom d, ⟨d, rfl⟩, hgstrict, hrle⟩

/-- Every positive germ dominated by an embedded element comes from the
original vector lattice. This is the interval form of the ideal-range property. -/
theorem germHom_interval_surjective (d : D) {v : BandGerms D}
    (hvpos : 0 ≤ v) (hvd : v ≤ germHom d) :
    ∃ d' : D, 0 ≤ d' ∧ d' ≤ d ∧ germHom d' = v := by
  let r : RawSection D := ⟨BandDomain.full, globalSection d⟩
  have hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D) :=
    hvpos.trans hvd
  obtain ⟨z, hzpos, hzd, hvz⟩ :=
    exists_representative_on_upper_domain r hrpos hvpos hvd
  let t : (BandDomain.full (D := D)).carrier := ⟨⊤, Set.mem_univ _⟩
  let d' : D := z.value t
  have hzglobal : z = globalSection d' := by
    ext B
    have h := z.compatible B t le_top
    change B.1.bandProjection d' = z.value B at h
    exact h.symm
  have hd'pos : 0 ≤ d' := hzpos t
  have hd'le : d' ≤ d := by
    have h := hzd t
    change d' ≤ (⊤ : ProjectionBand D).bandProjection d at h
    rwa [(⊤ : ProjectionBand D).bandProjection_eq_of_mem ProjectionBand.mem_top] at h
  refine ⟨d', hd'pos, hd'le, ?_⟩
  change germOf d' = v
  rw [hvz, hzglobal]
  rfl

/-- The embedded copy of `D` is an order ideal of its completion. -/
def germHomRange : OrderIdeal (BandGerms D) where
  toVectorSublattice := (germHom (D := D)).range
  solid' := by
    rintro _ _ ⟨x, rfl⟩ hy hxy
    obtain ⟨z, _, _, hz⟩ := germHom_interval_surjective x hy hxy
    exact ⟨z, hz⟩

/-! ### Lateral completeness by gluing disjoint sections -/

/-- Positive elements of the base lattice lying below a germ. -/
private def supportWitnesses (ξ : BandGerms D) : Set D :=
  {d | 0 ≤ d ∧ germHom d ≤ ξ}

/-- The band generated by all base-lattice witnesses below a germ. -/
private def supportBand (ξ : BandGerms D) : ProjectionBand D :=
  ProjectionBand.ofBand (Band.generated (supportWitnesses ξ))

private theorem coordinate_mem_support (r : RawSection D)
    (hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D))
    (B : r.1.carrier) : r.2.value B ∈ supportBand
      (Quotient.mk (sectionSetoid D) r : BandGerms D) := by
  change r.2.value B ∈
    (ProjectionBand.ofBand (Band.generated (supportWitnesses
      (Quotient.mk (sectionSetoid D) r)))).toBand
  rw [ProjectionBand.toBand_ofBand]
  exact Band.subset_generated _ (coordinate_le_germ r hrpos B)

private theorem supportWitnesses_disjoint {ξ η : BandGerms D}
    (hξη : ξ ⊓ η = 0) {d e : D}
    (hd : d ∈ supportWitnesses ξ) (he : e ∈ supportWitnesses η) :
    IsVLDisjoint d e := by
  have hde0 : 0 ≤ d ⊓ e := le_inf hd.1 he.1
  have hmap : germHom (d ⊓ e) = germHom d ⊓ germHom e :=
    (germHom (D := D)).map_inf' d e
  have hle : germHom (d ⊓ e) ≤ 0 := by
    rw [hmap, ← hξη]
    exact inf_le_inf hd.2 he.2
  have hge : 0 ≤ germHom (d ⊓ e) := germHom.map_nonneg hde0
  have hzero : germHom (d ⊓ e) = 0 := le_antisymm hle hge
  have hdezero : d ⊓ e = 0 := by
    apply germOf_injective
    change germHom (d ⊓ e) = germHom (0 : D)
    rw [hzero, map_zero]
  exact isVLDisjoint_of_inf_eq_zero hdezero

/-- Supports of disjoint positive germs are disjoint projection bands. -/
private theorem supportBand_disjoint {ξ η : BandGerms D} (hξη : ξ ⊓ η = 0) :
    supportBand ξ ⊓ supportBand η = ⊥ := by
  have hWξ : supportWitnesses ξ ⊆
      disjointComplement (supportWitnesses η) := by
    intro d hd e he
    exact supportWitnesses_disjoint hξη hd he
  have hHξ : (supportBand ξ : Set D) ⊆
      disjointComplement (supportWitnesses η) := by
    intro d hd
    apply (Band.generated_le (B := Band.disjointComplement (supportWitnesses η)) hWξ)
    change d ∈ (supportBand ξ).toBand at hd
    rwa [supportBand, ProjectionBand.toBand_ofBand] at hd
  have hWη : supportWitnesses η ⊆
      disjointComplement (supportBand ξ : Set D) := by
    intro e he d hd
    exact isVLDisjoint_comm.mp (hHξ hd e he)
  have hHη : (supportBand η : Set D) ⊆
      disjointComplement (supportBand ξ : Set D) := by
    intro e he
    apply (Band.generated_le
      (B := Band.disjointComplement (supportBand ξ : Set D)) hWη)
    change e ∈ (supportBand η).toBand at he
    rwa [supportBand, ProjectionBand.toBand_ofBand] at he
  apply le_antisymm
  · intro z hz
    have hz0 : z = 0 := Set.mem_singleton_iff.mp
      (disjointComplement_inter_eq_zero (supportBand ξ : Set D)
        ⟨hz.1, hHη hz.2⟩)
    exact ProjectionBand.mem_bot.mpr hz0
  · exact bot_le

private theorem Section.value_eq_zero_of_band_bot {A : BandDomain D}
    (x : Section A) (B : A.carrier) (hB : B.1 = ⊥) : x.value B = 0 := by
  have hm := x.mem_band B
  rw [hB] at hm
  exact ProjectionBand.mem_bot.mp hm

/-- The combined support of a family of germs. -/
private def familySupport (S : Set (BandGerms D)) : ProjectionBand D :=
  sSup (supportBand '' S)

/-- Bands on which a chosen representative of some family member is defined
and which lie below that member's support. -/
private def gluePieces (S : Set (BandGerms D)) : Set (ProjectionBand D) :=
  {B | ∃ ξ ∈ S, B ∈ (Quotient.out ξ : RawSection D).1.carrier ∧
    B ≤ supportBand ξ}

/-- The downward closed covering family used to glue a disjoint family, including
the complement of its combined support where the glued section is zero. -/
private def glueDomain (S : Set (BandGerms D)) : BandDomain D where
  carrier := gluePieces S ∪ {B | B ≤ (familySupport S)ᶜ}
  lower := by
    intro B C hBC hC
    rcases hC with hpiece | hzero
    · obtain ⟨ξ, hξ, hCdom, hCsupp⟩ := hpiece
      exact Or.inl ⟨ξ, hξ, (Quotient.out ξ : RawSection D).1.lower hBC hCdom,
        hBC.trans hCsupp⟩
    · exact Or.inr (hBC.trans hzero)
  cover := by
    apply top_unique
    have hpiece (ξ : BandGerms D) (hξ : ξ ∈ S) :
        supportBand ξ ≤ sSup (gluePieces S ∪
          {B | B ≤ (familySupport S)ᶜ}) := by
      let A := (Quotient.out ξ : RawSection D).1
      calc
        supportBand ξ = supportBand ξ ⊓ sSup A.carrier := by
          rw [A.cover, inf_top_eq]
        _ = ⨆ K ∈ A.carrier, supportBand ξ ⊓ K := inf_sSup_eq
        _ ≤ sSup (gluePieces S ∪
            {B | B ≤ (familySupport S)ᶜ}) := by
          apply iSup₂_le
          intro K hK
          apply le_sSup
          exact Or.inl ⟨ξ, hξ,
            A.lower inf_le_right hK, inf_le_left⟩
    have hsupport : familySupport S ≤ sSup (gluePieces S ∪
        {B | B ≤ (familySupport S)ᶜ}) := by
      apply sSup_le
      rintro B ⟨ξ, hξ, rfl⟩
      exact hpiece ξ hξ
    have hcomplement : (familySupport S)ᶜ ≤ sSup (gluePieces S ∪
        {B | B ≤ (familySupport S)ᶜ}) :=
      le_sSup (Or.inr (show (familySupport S)ᶜ ≤ (familySupport S)ᶜ from le_rfl))
    calc
      ⊤ = familySupport S ⊔ (familySupport S)ᶜ := sup_compl_eq_top.symm
      _ ≤ sSup (gluePieces S ∪
          {B | B ≤ (familySupport S)ᶜ}) := sup_le hsupport hcomplement
  bot_mem := Or.inr (show (⊥ : ProjectionBand D) ≤ (familySupport S)ᶜ from bot_le)

/-- Candidate coordinate for the glued section. The choice of a source germ
does not affect the result when the family is pairwise disjoint. -/
private def glueValue (S : Set (BandGerms D)) (B : (glueDomain S).carrier) : D :=
  by
    classical
    exact if h : B.1 ∈ gluePieces S then
      (Quotient.out (Classical.choose h) : RawSection D).2.value
        ⟨B.1, (Classical.choose_spec h).2.1⟩
    else 0

private theorem glueValue_piece (S : Set (BandGerms D))
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0))
    (ξ : BandGerms D) (hξ : ξ ∈ S)
    (B : (glueDomain S).carrier)
    (hBdom : B.1 ∈ (Quotient.out ξ : RawSection D).1.carrier)
    (hBsupp : B.1 ≤ supportBand ξ) :
    glueValue S B = (Quotient.out ξ : RawSection D).2.value ⟨B.1, hBdom⟩ := by
  classical
  have hp : B.1 ∈ gluePieces S := ⟨ξ, hξ, hBdom, hBsupp⟩
  unfold glueValue
  rw [dite_eq_left hp]
  let η := Classical.choose hp
  have hη : η ∈ S ∧
      B.1 ∈ (Quotient.out η : RawSection D).1.carrier ∧
      B.1 ≤ supportBand η := Classical.choose_spec hp
  by_cases hEq : η = ξ
  · change Classical.choose hp = ξ at hEq
    cases hEq
    rfl
  · have hdisj : supportBand η ⊓ supportBand ξ = ⊥ :=
      supportBand_disjoint (hpair hη.1 hξ hEq)
    have hBbot : B.1 = ⊥ :=
      (disjoint_iff.mpr hdisj).out B.1 hη.2.2 hBsupp
    have hηzero : (Quotient.out η : RawSection D).2.value
        ⟨B.1, hη.2.1⟩ = 0 :=
      Section.value_eq_zero_of_band_bot (Quotient.out η : RawSection D).2
        ⟨B.1, hη.2.1⟩ hBbot
    have hξzero : (Quotient.out ξ : RawSection D).2.value
        ⟨B.1, hBdom⟩ = 0 :=
      Section.value_eq_zero_of_band_bot (Quotient.out ξ : RawSection D).2
        ⟨B.1, hBdom⟩ hBbot
    exact hηzero.trans hξzero.symm

private theorem glueValue_zero (S : Set (BandGerms D))
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0))
    (B : (glueDomain S).carrier)
    (hBzero : B.1 ≤ (familySupport S)ᶜ) : glueValue S B = 0 := by
  classical
  by_cases hp : B.1 ∈ gluePieces S
  · obtain ⟨ξ, hξ, hBdom, hBsupp⟩ := hp
    have hHξ : supportBand ξ ≤ familySupport S :=
      le_sSup ⟨ξ, hξ, rfl⟩
    have hBbot : B.1 = ⊥ :=
      disjoint_compl_right.out B.1 (hBsupp.trans hHξ) hBzero
    rw [glueValue_piece S hpair ξ hξ B hBdom hBsupp]
    exact Section.value_eq_zero_of_band_bot _ _ hBbot
  · simp [glueValue, hp]

/-- The glued local section associated with a pairwise disjoint family. -/
private def glueSection (S : Set (BandGerms D))
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0)) : Section (glueDomain S) where
  value := glueValue S
  mem_band := by
    intro B
    rcases B.2 with hpiece | hzero
    · obtain ⟨ξ, hξ, hBdom, hBsupp⟩ := hpiece
      rw [glueValue_piece S hpair ξ hξ B hBdom hBsupp]
      exact (Quotient.out ξ : RawSection D).2.mem_band ⟨B.1, hBdom⟩
    · rw [glueValue_zero S hpair B hzero]
      exact B.1.toBand.toOrderIdeal.toSubmodule.zero_mem
  compatible := by
    intro B C hBC
    rcases C.2 with hpiece | hzero
    · obtain ⟨ξ, hξ, hCdom, hCsupp⟩ := hpiece
      have hBdom : B.1 ∈ (Quotient.out ξ : RawSection D).1.carrier :=
        (Quotient.out ξ : RawSection D).1.lower hBC hCdom
      have hBsupp : B.1 ≤ supportBand ξ := hBC.trans hCsupp
      rw [glueValue_piece S hpair ξ hξ C hCdom hCsupp,
        glueValue_piece S hpair ξ hξ B hBdom hBsupp]
      exact (Quotient.out ξ : RawSection D).2.compatible
        ⟨B.1, hBdom⟩ ⟨C.1, hCdom⟩ hBC
    · have hBzero : B.1 ≤ (familySupport S)ᶜ := hBC.trans hzero
      rw [glueValue_zero S hpair C hzero,
        glueValue_zero S hpair B hBzero, map_zero]

private theorem glueSection_nonneg (S : Set (BandGerms D))
    (hpos : ∀ ξ ∈ S, 0 ≤ ξ)
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0)) :
    0 ≤ glueSection S hpair := by
  intro B
  rcases B.2 with hpiece | hzero
  · obtain ⟨ξ, hξ, hBdom, hBsupp⟩ := hpiece
    rw [show (glueSection S hpair).value B = glueValue S B from rfl,
      glueValue_piece S hpair ξ hξ B hBdom hBsupp]
    have hrpos : 0 ≤ (Quotient.mk (sectionSetoid D)
        (Quotient.out ξ : RawSection D) : BandGerms D) := by
      rw [Quotient.out_eq]
      exact hpos ξ hξ
    exact (coordinate_le_germ (Quotient.out ξ : RawSection D) hrpos
      ⟨B.1, hBdom⟩).1
  · change 0 ≤ glueValue S B
    rw [glueValue_zero S hpair B hzero]

private theorem coordinate_eq_zero_of_band_disjoint (r : RawSection D)
    (hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D))
    (B : r.1.carrier) (K : ProjectionBand D)
    (hBK : B.1 ≤ K)
    (hdisj : supportBand
      (Quotient.mk (sectionSetoid D) r : BandGerms D) ⊓ K = ⊥) :
    r.2.value B = 0 := by
  have hrin : r.2.value B ∈ supportBand
      (Quotient.mk (sectionSetoid D) r : BandGerms D) :=
    coordinate_mem_support r hrpos B
  have hrinK : r.2.value B ∈ K := hBK (r.2.mem_band B)
  have : r.2.value B ∈ (⊥ : ProjectionBand D) := hdisj ▸ ⟨hrin, hrinK⟩
  exact ProjectionBand.mem_bot.mp this

/-- The glued germ is an upper bound for every member of a pairwise disjoint
positive family. -/
private theorem le_glued_germ (S : Set (BandGerms D))
    (hpos : ∀ ξ ∈ S, 0 ≤ ξ)
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0))
    (ξ : BandGerms D) (hξ : ξ ∈ S) :
    ξ ≤ Quotient.mk (sectionSetoid D) ⟨glueDomain S, glueSection S hpair⟩ := by
  let r : RawSection D := Quotient.out ξ
  have hrEq : (Quotient.mk (sectionSetoid D) r : BandGerms D) = ξ :=
    Quotient.out_eq ξ
  have hrpos : 0 ≤ (Quotient.mk (sectionSetoid D) r : BandGerms D) := by
    rw [hrEq]
    exact hpos ξ hξ
  rw [← hrEq]
  apply (germ_le_iff r ⟨glueDomain S, glueSection S hpair⟩).mpr
  intro B hrB hglueB
  change r.2.value ⟨B, hrB⟩ ≤ glueValue S ⟨B, hglueB⟩
  rcases hglueB with hpiece | hzero
  · have hp : B ∈ gluePieces S := hpiece
    obtain ⟨η, hη, hBdom, hBsupp⟩ := hpiece
    by_cases hEq : ξ = η
    · subst η
      rw [glueValue_piece S hpair ξ hξ ⟨B, Or.inl hp⟩ hBdom hBsupp]
    · have hdisj : supportBand
          (Quotient.mk (sectionSetoid D) r : BandGerms D) ⊓ supportBand η = ⊥ := by
        rw [hrEq]
        exact supportBand_disjoint (hpair hξ hη hEq)
      have hcoord0 : r.2.value ⟨B, hrB⟩ = 0 :=
        coordinate_eq_zero_of_band_disjoint r hrpos ⟨B, hrB⟩
          (supportBand η) hBsupp hdisj
      rw [hcoord0]
      exact glueSection_nonneg S hpos hpair ⟨B, Or.inl hp⟩
  · have hξH : supportBand ξ ≤ familySupport S :=
      le_sSup ⟨ξ, hξ, rfl⟩
    have hdisj : supportBand
        (Quotient.mk (sectionSetoid D) r : BandGerms D) ⊓
        (familySupport S)ᶜ = ⊥ := by
      rw [hrEq]
      apply le_antisymm _ bot_le
      calc
        supportBand ξ ⊓ (familySupport S)ᶜ ≤
            familySupport S ⊓ (familySupport S)ᶜ := inf_le_inf hξH le_rfl
        _ = ⊥ := inf_compl_eq_bot
    have hcoord0 : r.2.value ⟨B, hrB⟩ = 0 :=
      coordinate_eq_zero_of_band_disjoint r hrpos ⟨B, hrB⟩
        (familySupport S)ᶜ hzero hdisj
    rw [hcoord0, glueValue_zero S hpair ⟨B, Or.inr hzero⟩ hzero]

/-- Every pairwise disjoint positive family of germs is bounded above. -/
theorem disjoint_positive_bddAbove (S : Set (BandGerms D))
    (hpos : ∀ ξ ∈ S, 0 ≤ ξ)
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0)) : BddAbove S := by
  refine ⟨Quotient.mk (sectionSetoid D)
    ⟨glueDomain S, glueSection S hpair⟩, ?_⟩
  intro ξ hξ
  exact le_glued_germ S hpos hpair ξ hξ

/-- Every nonempty pairwise disjoint family of positive germs has a supremum. -/
theorem isLUB_disjoint_positive (S : Set (BandGerms D))
    (hpos : ∀ ξ ∈ S, 0 ≤ ξ)
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0))
    (hne : S.Nonempty) : IsLUB S (sSup S) :=
  isLUB_csSup hne (disjoint_positive_bddAbove S hpos hpair)

end UniversalCompletionConstruction

/-! ### Universal completion of an Archimedean vector lattice -/

/-- The universal completion of an Archimedean vector lattice, obtained by applying
the band-section construction to its bounded-cut Dedekind completion. -/
abbrev UniversalCompletion (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] :=
  UniversalCompletionConstruction.BandGerms (DedekindCompletion.BoundedCut X)

namespace UniversalCompletion

open DedekindCompletion UniversalCompletionConstruction

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] [IsVLArchimedean X]

/-- The canonical embedding into the universal completion, through the Dedekind completion. -/
def inclusion : VecLatHom X (UniversalCompletion X) :=
  germHom.comp BoundedCut.principalHom

/-- The canonical embedding of an Archimedean vector lattice is injective. -/
theorem inclusion_injective : Function.Injective (inclusion (X := X)) :=
  germHom_injective.comp BoundedCut.principal_injective

/-- The original vector lattice is order dense in its universal completion. -/
theorem inclusion_orderDense : (inclusion (X := X)).range.IsOrderDense := by
  intro ξ hξ
  obtain ⟨_, ⟨d, rfl⟩, hdpos, hdle⟩ := germHom_orderDense hξ
  let g : BoundedCut X ↪o UniversalCompletion X :=
    { toFun := germHom
      inj' := germHom_injective
      map_rel_iff' :=
        ⟨germHom.le_of_map_le germHom_injective, fun h ↦ germHom.monotone h⟩ }
  have hg0 : g 0 = 0 := map_zero germHom
  have hd : 0 < d := g.lt_iff_lt.mp (hg0.symm ▸ hdpos)
  obtain ⟨_, ⟨x, rfl⟩, hxpos, hxle⟩ := BoundedCut.principal_orderDense hd
  exact ⟨inclusion x, ⟨x, rfl⟩, hg0 ▸ g.strictMono hxpos, (g.monotone hxle).trans hdle⟩

/-- Every pairwise disjoint positive family in the universal completion is bounded above. -/
theorem disjoint_positive_bddAbove (S : Set (UniversalCompletion X))
    (hpos : ∀ ξ ∈ S, 0 ≤ ξ)
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0)) : BddAbove S :=
  UniversalCompletionConstruction.disjoint_positive_bddAbove S hpos hpair

/-- Every nonempty pairwise disjoint positive family in the universal completion
has a supremum. -/
theorem isLUB_disjoint_positive (S : Set (UniversalCompletion X))
    (hpos : ∀ ξ ∈ S, 0 ≤ ξ)
    (hpair : S.Pairwise (fun ξ η ↦ ξ ⊓ η = 0))
    (hne : S.Nonempty) : IsLUB S (sSup S) :=
  UniversalCompletionConstruction.isLUB_disjoint_positive S hpos hpair hne

end UniversalCompletion
