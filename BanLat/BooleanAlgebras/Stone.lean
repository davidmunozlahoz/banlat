/-
Authors: Pedro Tradacete
-/

import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.PrimeSeparator
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Sets.Closeds

/-!
# Stone representation of Boolean algebras

The Stone space of a Boolean algebra consists of its prime ideals. Each algebra element
determines the clopen set of prime ideals that do not contain it. The space is compact and
totally disconnected, and the algebra is isomorphic to its algebra of clopen subsets.
Completeness of the Boolean algebra is equivalent to extremal disconnectedness of its Stone
space. The clopen subsets of any extremally disconnected topological space form a complete
Boolean algebra.
-/

universe u

namespace TopologicalSpace.Clopens

variable {X : Type u} [TopologicalSpace X]

/-- In an extremally disconnected space, every family of clopen sets has a least
upper bound, obtained by taking the closure of its union. -/
private lemma exists_isLUB (h : ExtremallyDisconnected X)
    (s : Set (Clopens X)) : ∃ C, IsLUB s C := by
  let C : Clopens X :=
    ⟨closure (⋃ c ∈ s, (c : Set X)), isClosed_closure,
      h.open_closure _ (isOpen_iUnion fun c ↦ isOpen_iUnion fun _ ↦ c.isOpen)⟩
  refine ⟨C, ?_, ?_⟩
  · exact fun c hc x hx ↦ subset_closure (Set.mem_iUnion₂.mpr ⟨c, hc, hx⟩)
  · intro D hD
    exact closure_minimal (Set.iUnion₂_subset fun c hc ↦ hD hc) D.isClosed

/-- Clopen subsets of an extremally disconnected topological space form a complete Boolean
algebra. -/
noncomputable instance instCompleteBooleanAlgebra [ExtremallyDisconnected X] :
    CompleteBooleanAlgebra (Clopens X) where
  __ := (inferInstance : BooleanAlgebra (Clopens X))
  sSup s := (exists_isLUB inferInstance s).choose
  sInf s := (exists_isLUB inferInstance (lowerBounds s)).choose
  isLUB_sSup s := (exists_isLUB inferInstance s).choose_spec
  isGLB_sInf s := isLUB_lowerBounds.mp (exists_isLUB inferInstance (lowerBounds s)).choose_spec

end TopologicalSpace.Clopens

namespace BooleanAlgebra

variable {B : Type u} [BooleanAlgebra B]

/-- The points of the Stone space of a Boolean algebra are its prime ideals. -/
def StoneSpace (B : Type u) [BooleanAlgebra B] :=
  {I : Order.Ideal B // Order.Ideal.IsPrime I}

/-- A prime ideal determines the homomorphism that is false on its elements. -/
private noncomputable def primeIdealToBoolHom (I : StoneSpace B) : BoundedLatticeHom B Bool where
  toFun a := by classical exact decide (a ∉ I.1)
  map_bot' := by classical simp
  map_top' := by classical simpa using I.2.top_notMem
  map_sup' a b := by classical simp
  map_inf' a b := by
    classical
    have h : a ⊓ b ∈ I.1 ↔ a ∈ I.1 ∨ b ∈ I.1 :=
      ⟨I.2.mem_or_mem, fun h => h.elim (I.1.lower inf_le_left) (I.1.lower inf_le_right)⟩
    simp [h]

/-- The homomorphism associated to a prime ideal is true outside that ideal. -/
private theorem primeIdealToBoolHom_apply_eq_true (I : StoneSpace B) (a : B) :
    primeIdealToBoolHom I a = true ↔ a ∉ I.1 := by
  classical
  simp [primeIdealToBoolHom]

/-- The false fiber of a homomorphism to `Bool` is a prime ideal. -/
private def boolHomToPrimeIdeal (f : BoundedLatticeHom B Bool) : StoneSpace B := by
  let I : Order.Ideal B := {
    carrier := {a | f a = false}
    lower' := by
      intro a b hab ha
      change f a = false at ha
      change f b = false
      exact le_bot_iff.mp (by simpa [ha] using (map_rel f hab))
    nonempty' := ⟨⊥, by simp⟩
    directed' := by
      intro a ha b hb
      change f a = false at ha
      change f b = false at hb
      exact ⟨a ⊔ b, by simp [ha, hb], le_sup_left, le_sup_right⟩ }
  haveI : I.IsProper := Order.Ideal.isProper_iff_top_notMem.mpr (by
    change f ⊤ ≠ false
    simp)
  refine ⟨I, Order.Ideal.isPrime_of_mem_or_compl_mem ?_⟩
  intro a
  change f a = false ∨ f aᶜ = false
  rw [map_compl' f]
  cases f a <;> simp

/-- Membership in the ideal associated to a homomorphism is its false fiber. -/
private theorem mem_boolHomToPrimeIdeal_iff (f : BoundedLatticeHom B Bool) (a : B) :
    a ∈ (boolHomToPrimeIdeal f).1 ↔ f a = false := Iff.rfl

/-- Prime ideals of a Boolean algebra correspond to homomorphisms into the two-element
Boolean algebra. -/
noncomputable def stoneSpaceEquivBoolHom : StoneSpace B ≃ BoundedLatticeHom B Bool where
  toFun := primeIdealToBoolHom
  invFun := boolHomToPrimeIdeal
  left_inv I := by
    apply Subtype.ext
    apply Order.Ideal.ext
    ext a
    change (primeIdealToBoolHom I a = false) ↔ a ∈ I.1
    simp [primeIdealToBoolHom]
  right_inv f := by
    ext a
    apply Bool.eq_iff_iff.mpr
    rw [primeIdealToBoolHom_apply_eq_true, mem_boolHomToPrimeIdeal_iff]
    cases f a <;> simp

/-- Evaluation at a Stone point is true exactly outside its prime ideal. -/
@[simp]
theorem stoneSpaceEquivBoolHom_apply_eq_true (I : StoneSpace B) (a : B) :
    stoneSpaceEquivBoolHom I a = true ↔ a ∉ I.1 :=
  primeIdealToBoolHom_apply_eq_true I a

/-- The ideal corresponding to a homomorphism consists of its false inputs. -/
@[simp]
theorem mem_stoneSpaceEquivBoolHom_symm_iff (f : BoundedLatticeHom B Bool) (a : B) :
    a ∈ (stoneSpaceEquivBoolHom.symm f).1 ↔ f a = false :=
  mem_boolHomToPrimeIdeal_iff f a

/-- The Stone set associated to an element consists of the prime ideals omitting it. -/
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

/-- Inclusion of Stone sets reflects the order of the Boolean algebra. -/
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

/-- The Stone set of an infimum is the intersection of its Stone sets. -/
@[simp]
theorem stoneSet_inf (a b : B) : stoneSet (a ⊓ b) = stoneSet a ∩ stoneSet b := by
  ext I
  change (a ⊓ b ∉ I.1) ↔ a ∉ I.1 ∧ b ∉ I.1
  constructor
  · exact fun h ↦ ⟨fun ha ↦ h (I.1.lower inf_le_left ha),
      fun hb ↦ h (I.1.lower inf_le_right hb)⟩
  · exact fun ⟨ha, hb⟩ hab ↦ (I.2.mem_or_mem hab).elim ha hb

/-- The Stone set of a complement is the set complement. -/
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

/-- The Stone set of a supremum is the union of its Stone sets. -/
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

/-- The topology generated by the Stone sets of prime ideals. -/
instance instTopologicalSpace : TopologicalSpace (StoneSpace B) :=
  TopologicalSpace.generateFrom (Set.range (stoneSet (B := B)))

/-- Every Stone set is open in the Stone topology. -/
theorem isOpen_stoneSet (a : B) : IsOpen (stoneSet a) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, rfl⟩

/-- Every Stone set is clopen in the Stone topology. -/
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

/-- The ideal of elements whose Stone sets do not belong to an ultrafilter. -/
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
  have : Order.Ideal.IsProper (idealOfUltrafilter U) := by
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

/-- The Stone sets form a basis for the Stone topology. -/
private theorem stoneSet_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis (Set.range (stoneSet (B := B))) := by
  apply TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter rfl
  constructor
  · exact ⟨⊤, stoneSet_top⟩
  · rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩
    exact ⟨a ⊓ b, stoneSet_inf a b⟩

/-- A finite join represents the union of its Stone sets. -/
private theorem stoneSet_finset_sup {ι : Type*} (t : Finset ι) (f : ι → B) :
    stoneSet (t.sup f) = ⋃ i ∈ t, stoneSet (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [ih, stoneSet_sup]

/-- Every clopen subset is the Stone set of an algebra element. -/
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

/-- If `a` is the supremum of `s`, its Stone set is the closure of the union of the
Stone sets associated to elements of `s`. -/
private lemma stoneSet_eq_closure_iUnion {s : Set B} {a : B} (ha : IsLUB s a) :
    stoneSet a = closure (⋃ b ∈ s, stoneSet b) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hx'
    obtain ⟨_, ⟨b, rfl⟩, hxb, hb⟩ :=
      stoneSet_isTopologicalBasis.exists_subset_of_mem_open hx' isClosed_closure.isOpen_compl
    have hab : a ≤ bᶜ := ha.2 fun c hc ↦ (stoneSet_subset_iff c bᶜ).mp (by
      rw [stoneSet_compl]
      exact fun I hIc hIb ↦ hb hIb (subset_closure (Set.mem_iUnion₂.mpr ⟨c, hc, hIc⟩)))
    exact ((stoneSet_compl b) ▸ (stoneSet_subset_iff a bᶜ).mpr hab hx) hxb
  · exact closure_minimal
      (Set.iUnion₂_subset fun b hb ↦ (stoneSet_subset_iff b a).mpr (ha.1 hb))
      (isClopen_stoneSet a).isClosed

/-- Every subset of the Boolean algebra has a least upper bound (and therefore it's complete)
if and only if its Stone space is extremally disconnected. -/
theorem extremallyDisconnected_stoneSpace_iff :
    ExtremallyDisconnected (StoneSpace B) ↔ ∀ s : Set B, ∃ a : B, IsLUB s a := by
  constructor
  · intro h s
    let := h
    exact ⟨stoneRepresentation.symm (sSup (stoneRepresentation '' s)),
      stoneRepresentation.isLUB_image.mp (isLUB_sSup _)⟩
  · intro h
    refine ⟨fun U hU ↦ ?_⟩
    obtain ⟨S, hS, rfl⟩ := stoneSet_isTopologicalBasis.open_eq_sUnion hU
    obtain ⟨a, ha⟩ := h (stoneSet ⁻¹' S)
    have heq := stoneSet_eq_closure_iUnion ha
    simp only [← Set.sUnion_image, Set.image_preimage_eq_of_subset hS] at heq
    exact heq ▸ isOpen_stoneSet a

/-- The Stone space of a complete Boolean algebra is extremally disconnected. -/
instance instExtremallyDisconnected {B : Type u} [CompleteBooleanAlgebra B] :
    ExtremallyDisconnected (StoneSpace B) := by
  exact extremallyDisconnected_stoneSpace_iff.mpr fun s ↦ ⟨sSup s, isLUB_sSup s⟩

end BooleanAlgebra
