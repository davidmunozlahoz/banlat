/-
Authors: Pedro Tradacete
-/

import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.PrimeSeparator
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sets.Closeds

/-!
# Stone representation of Boolean algebras

The Stone space of a Boolean algebra consists of its prime ideals. Each algebra element
determines the clopen set of prime ideals that do not contain it. The space is compact and
totally separated, and the algebra is isomorphic to its algebra of clopen subsets.
-/

universe u

namespace BooleanAlgebra

variable {B : Type u} [BooleanAlgebra B]

/-- The points of the Stone space of a Boolean algebra are its prime ideals. -/
def StoneSpace (B : Type u) [BooleanAlgebra B] :=
  {I : Order.Ideal B // Order.Ideal.IsPrime I}

/-- The basic set associated to an element consists of the prime ideals omitting it. -/
def stoneSet (a : B) : Set (StoneSpace B) :=
  {I | a ∉ I.1}

/-- A prime ideal separates two elements when the first is not below the second. -/
private lemma exists_prime_ideal_separating {a b : B} (hab : ¬ a ≤ b) :
    ∃ I : StoneSpace B, a ∉ I.1 ∧ b ∈ I.1 := by
  classical
  have hdis : Disjoint ((Order.PFilter.principal a : Order.PFilter B) : Set B)
      ((Order.Ideal.principal b : Order.Ideal B) : Set B) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxF hxI
    exact hab ((Order.PFilter.mem_principal.mp hxF).trans (Order.Ideal.mem_principal.mp hxI))
  obtain ⟨I, hI, hb, hFI⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdis
  refine ⟨⟨I, hI⟩, ?_, ?_⟩
  · exact (Set.disjoint_left.mp hFI) (Order.PFilter.mem_principal.mpr le_rfl)
  · exact hb Order.Ideal.mem_principal_self

/-- Inclusion of basic sets reflects the order of the Boolean algebra. -/
theorem stoneSet_subset_iff (a b : B) : stoneSet a ⊆ stoneSet b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    obtain ⟨I, haI, hbI⟩ := exists_prime_ideal_separating hab
    exact (h haI) hbI
  · intro hab I haI
    exact fun hbI ↦ haI (I.1.lower hab hbI)

/-- Every Boolean algebra embeds in a field of sets on its prime ideals. -/
def stoneEmbedding : B ↪o Set (StoneSpace B) :=
  OrderEmbedding.ofMapLEIff stoneSet stoneSet_subset_iff

/-- The basic set of an infimum is the intersection of its basic sets. -/
@[simp]
theorem stoneSet_inf (a b : B) : stoneSet (a ⊓ b) = stoneSet a ∩ stoneSet b := by
  ext I
  change (a ⊓ b ∉ I.1) ↔ a ∉ I.1 ∧ b ∉ I.1
  constructor
  · exact fun h ↦ ⟨fun ha ↦ h (I.1.lower inf_le_left ha),
      fun hb ↦ h (I.1.lower inf_le_right hb)⟩
  · exact fun ⟨ha, hb⟩ hab ↦ (I.2.mem_or_mem hab).elim ha hb

/-- The basic set of a complement is the set complement. -/
@[simp]
theorem stoneSet_compl (a : B) : stoneSet aᶜ = (stoneSet a)ᶜ := by
  ext I
  change (aᶜ ∉ I.1) ↔ ¬(a ∉ I.1)
  push Not
  constructor
  · exact fun h ↦ (I.2.mem_or_compl_mem (x := a)).resolve_right h
  · intro ha hac
    exact I.2.top_notMem (by simpa using I.1.sup_mem ha hac)

/-- The bottom element represents the empty set. -/
@[simp]
theorem stoneSet_bot : stoneSet (⊥ : B) = ∅ := by
  ext I
  simp [stoneSet]

/-- The top element represents the whole Stone space. -/
@[simp]
theorem stoneSet_top : stoneSet (⊤ : B) = Set.univ := by
  simpa using stoneSet_compl (a := (⊥ : B))

/-- The basic set of a supremum is the union of its basic sets. -/
@[simp]
theorem stoneSet_sup (a b : B) : stoneSet (a ⊔ b) = stoneSet a ∪ stoneSet b := by
  ext I
  change (a ⊔ b ∉ I.1) ↔ a ∉ I.1 ∨ b ∉ I.1
  have h : a ⊔ b ∈ I.1 ↔ a ∈ I.1 ∧ b ∈ I.1 :=
    ⟨fun hab ↦ ⟨I.1.lower le_sup_left hab, I.1.lower le_sup_right hab⟩,
      fun ⟨ha, hb⟩ ↦ I.1.sup_mem ha hb⟩
  simpa only [not_and_or] using not_congr h

/-- The Stone representation as a Boolean algebra homomorphism into a powerset. -/
def stoneHom : BoundedLatticeHom B (Set (StoneSpace B)) where
  toFun := stoneSet
  map_bot' := stoneSet_bot
  map_top' := stoneSet_top
  map_sup' := stoneSet_sup
  map_inf' := stoneSet_inf

/-- The Stone homomorphism is injective. -/
theorem stoneHom_injective : Function.Injective (stoneHom (B := B)) :=
  (stoneEmbedding (B := B)).injective

/-- The field of subsets representing a Boolean algebra. -/
def stoneField (B : Type u) [BooleanAlgebra B] : BooleanSubalgebra (Set (StoneSpace B)) :=
  (⊤ : BooleanSubalgebra B).map stoneHom

/-- The Stone embedding with codomain restricted to its field of sets. -/
private def stoneFieldEmbedding : B ↪o stoneField B :=
  OrderEmbedding.ofMapLEIff
    (fun a ↦ ⟨stoneSet a, by simp [stoneField, stoneHom]⟩)
    (fun a b ↦ stoneSet_subset_iff a b)

/-- Every set in the Stone field is the image of an algebra element. -/
private theorem stoneFieldEmbedding_surjective :
    Function.Surjective (stoneFieldEmbedding (B := B)) := by
  rintro ⟨s, hs⟩
  change s ∈ (⊤ : BooleanSubalgebra B).map stoneHom at hs
  obtain ⟨a, -, rfl⟩ := BooleanSubalgebra.mem_map.mp hs
  exact ⟨a, rfl⟩

/-- Every Boolean algebra is isomorphic to a field of sets. -/
noncomputable def stoneFieldRepresentation : B ≃o stoneField B :=
  RelIso.ofSurjective stoneFieldEmbedding stoneFieldEmbedding_surjective

/-- The topology generated by the basic subsets of prime ideals. -/
instance instTopologicalSpace : TopologicalSpace (StoneSpace B) :=
  TopologicalSpace.generateFrom (Set.range (stoneSet (B := B)))

/-- Every basic set is open in the Stone topology. -/
theorem isOpen_stoneSet (a : B) : IsOpen (stoneSet a) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, rfl⟩

/-- Every basic set is clopen in the Stone topology. -/
theorem isClopen_stoneSet (a : B) : IsClopen (stoneSet a) :=
  ⟨by simpa using (isOpen_stoneSet aᶜ).isClosed_compl, isOpen_stoneSet a⟩

/-- An algebra element as a clopen subset of its Stone space. -/
def stoneClopen (a : B) : TopologicalSpace.Clopens (StoneSpace B) :=
  ⟨stoneSet a, isClopen_stoneSet a⟩

/-- The Stone homomorphism with clopen codomain. -/
def stoneClopenHom : BoundedLatticeHom B (TopologicalSpace.Clopens (StoneSpace B)) where
  toFun := stoneClopen
  map_bot' := TopologicalSpace.Clopens.ext stoneSet_bot
  map_top' := TopologicalSpace.Clopens.ext stoneSet_top
  map_sup' a b := TopologicalSpace.Clopens.ext (stoneSet_sup a b)
  map_inf' a b := TopologicalSpace.Clopens.ext (stoneSet_inf a b)

/-- The ideal of elements whose basic sets do not belong to an ultrafilter. -/
private def idealOfUltrafilter (U : Ultrafilter (StoneSpace B)) : Order.Ideal B where
  carrier := {a | stoneSet a ∉ U}
  lower' := by
    intro a b hab hb
    exact fun h ↦ hb (U.mem_of_superset h ((stoneSet_subset_iff b a).2 hab))
  nonempty' := ⟨⊥, by simp⟩
  directed' := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    simpa [stoneSet_sup, Ultrafilter.union_mem_iff] using And.intro ha hb

/-- The ideal obtained from an ultrafilter is prime. -/
private theorem idealOfUltrafilter_isPrime (U : Ultrafilter (StoneSpace B)) :
    Order.Ideal.IsPrime (idealOfUltrafilter U) := by
  haveI : Order.Ideal.IsProper (idealOfUltrafilter U) := by
    apply Order.Ideal.isProper_iff_top_notMem.mpr
    change ¬ (stoneSet (⊤ : B) ∉ U)
    simpa only [stoneSet_top, not_not] using (Ultrafilter.mem_coe.mp U.univ_mem)
  apply Order.Ideal.isPrime_of_mem_or_compl_mem
  intro a
  by_cases h : stoneSet a ∈ U
  · right
    change stoneSet aᶜ ∉ U
    simpa only [stoneSet_compl] using (Ultrafilter.compl_notMem_iff.mpr h)
  · exact Or.inl h

/-- The Stone point corresponding to an ultrafilter on the Stone space. -/
private def pointOfUltrafilter (U : Ultrafilter (StoneSpace B)) : StoneSpace B :=
  ⟨idealOfUltrafilter U, idealOfUltrafilter_isPrime U⟩

/-- The Stone space is compact. -/
instance instCompactSpace : CompactSpace (StoneSpace B) := by
  apply isCompact_univ_iff.mp
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro U hU
  refine ⟨pointOfUltrafilter U, Set.mem_univ _, ?_⟩
  rw [TopologicalSpace.nhds_generateFrom]
  refine le_iInf fun s ↦ le_iInf fun hs ↦ ?_
  rw [Filter.le_principal_iff]
  obtain ⟨hx, ⟨a, rfl⟩⟩ := hs
  change ¬ (stoneSet a ∉ U) at hx
  exact Ultrafilter.mem_coe.mpr (not_not.mp hx)

/-- The basic sets form a basis for the Stone topology. -/
private theorem stoneSet_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis (Set.range (stoneSet (B := B))) := by
  apply TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter rfl
  constructor
  · exact ⟨⊤, stoneSet_top⟩
  · rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩
    exact ⟨a ⊓ b, stoneSet_inf a b⟩

/-- A finite join represents the union of its basic sets. -/
private theorem stoneSet_finset_sup {ι : Type*} (t : Finset ι) (f : ι → B) :
    stoneSet (t.sup f) = ⋃ i ∈ t, stoneSet (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [ih, stoneSet_sup]

/-- Every clopen subset is the basic set of an algebra element. -/
private theorem exists_stoneSet_eq_clopen
    (C : TopologicalSpace.Clopens (StoneSpace B)) :
    ∃ a : B, stoneSet a = (C : Set (StoneSpace B)) := by
  let A := {a : B // stoneSet a ⊆ (C : Set (StoneSpace B))}
  have hcover : (C : Set (StoneSpace B)) ⊆ ⋃ a : A, stoneSet a.1 := by
    intro x hx
    obtain ⟨t, ht, hxt, htC⟩ := stoneSet_isTopologicalBasis.isOpen_iff.mp C.isOpen x hx
    obtain ⟨a, rfl⟩ := ht
    exact Set.mem_iUnion.mpr ⟨⟨a, htC⟩, hxt⟩
  obtain ⟨t, ht⟩ := C.isClosed.isCompact.elim_finite_subcover
    (fun a : A ↦ stoneSet a.1) (fun a ↦ isOpen_stoneSet a.1) hcover
  refine ⟨t.sup (fun a : A ↦ a.1), ?_⟩
  rw [stoneSet_finset_sup]
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun i hi ↦ i.property
  · exact ht

/-- Every clopen subset of the Stone space is represented by an algebra element. -/
theorem stoneClopenHom_surjective :
    Function.Surjective (stoneClopenHom (B := B)) := by
  intro C
  obtain ⟨a, ha⟩ := exists_stoneSet_eq_clopen C
  exact ⟨a, TopologicalSpace.Clopens.ext ha⟩

/-- Distinct algebra elements determine distinct clopen subsets. -/
theorem stoneClopenHom_injective :
    Function.Injective (stoneClopenHom (B := B)) := by
  intro a b h
  exact stoneHom_injective (congrArg
    (fun C : TopologicalSpace.Clopens (StoneSpace B) ↦ (C : Set (StoneSpace B))) h)

/-- The Stone embedding with codomain restricted to clopen subsets. -/
private def stoneClopenEmbedding : B ↪o TopologicalSpace.Clopens (StoneSpace B) :=
  OrderEmbedding.ofMapLEIff stoneClopen stoneSet_subset_iff

/-- Stone's representation theorem: a Boolean algebra is the algebra of clopen subsets of
its Stone space. -/
noncomputable def stoneRepresentation : B ≃o TopologicalSpace.Clopens (StoneSpace B) :=
  RelIso.ofSurjective stoneClopenEmbedding stoneClopenHom_surjective

/-- The Stone space is totally separated. -/
instance instTotallySeparatedSpace : TotallySeparatedSpace (StoneSpace B) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro I J hIJ
  have hne : (I.1 : Set B) ≠ J.1 := fun h ↦ hIJ (Subtype.ext (Order.Ideal.ext h))
  have hdiff : ¬ ((I.1 : Set B) ⊆ J.1 ∧ (J.1 : Set B) ⊆ I.1) :=
    fun h ↦ hne (Set.Subset.antisymm h.1 h.2)
  rcases not_and_or.mp hdiff with h | h
  · obtain ⟨a, haI, haJ⟩ := Set.not_subset_iff_exists_mem_notMem.mp h
    refine ⟨(stoneSet a)ᶜ, (isClopen_stoneSet a).compl, ?_, ?_⟩
    · simpa [stoneSet] using haI
    · simpa [stoneSet] using haJ
  · obtain ⟨a, haJ, haI⟩ := Set.not_subset_iff_exists_mem_notMem.mp h
    refine ⟨stoneSet a, isClopen_stoneSet a, ?_, ?_⟩
    · simpa [stoneSet] using haI
    · simpa [stoneSet] using haJ

end BooleanAlgebra
