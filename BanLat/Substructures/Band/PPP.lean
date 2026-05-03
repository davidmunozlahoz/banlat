import BanLat.Substructures.Band.Projection
import BanLat.OrderComplete

/-!
# The (principal) projection property

A vector lattice has the **Projection Property** (PP) when every band is a
projection band, and the **Principal Projection Property** (PPP) when every
principal band is a projection band. Clearly PP implies PPP.

The two main sources of these properties come from order completeness: order
complete vector lattices have PP, and σ-order complete vector lattices have
PPP. Under PPP every finite positive sum may be replaced by a disjoint sum
with the same supremum. Finally, PP and PPP both imply the Archimedean
property.
-/

/-! ### The projection properties -/

section Defs

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- A vector lattice has the **Projection Property** (PP) when every band in
`X` is a projection band. -/
class HasProjectionProperty (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  exists_projectionBand : ∀ B : Band X, ∃ P : ProjectionBand X,
    (P : Set X) = (B : Set X)

/-- A vector lattice has the **Principal Projection Property** (PPP) when every
principal band in `X` is a projection band. -/
class HasPrincipalProjectionProperty (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  exists_projectionBand : ∀ a : X, ∃ P : ProjectionBand X,
    (P : Set X) = (Band.generated ({a} : Set X) : Set X)

/-- PP implies PPP. -/
instance (priority := 100) HasPrincipalProjectionProperty.of_hasProjectionProperty
    [HasProjectionProperty X] : HasPrincipalProjectionProperty X where
  exists_projectionBand a :=
    HasProjectionProperty.exists_projectionBand (Band.generated ({a} : Set X))

end Defs

/-! ### Order completeness implies the projection properties -/

section OrderComplete

/-- An order complete vector lattice has the Projection Property. -/
instance (priority := 100) HasProjectionProperty.of_isOrderComplete
    {X : Type*} [AddCommGroup X] [ConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    HasProjectionProperty X := by
  haveI : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  refine ⟨fun B => ?_⟩
  apply (ProjectionBand.projectionBand_iff_isLUB_inter_Icc B).mpr
  intro x hx
  refine ⟨sSup ((B : Set X) ∩ Set.Icc 0 x),
    isLUB_csSup ⟨0, B.toOrderIdeal.toSubmodule.zero_mem, le_refl 0, hx⟩
      ⟨x, fun _ hy => hy.2.2⟩⟩

/-- A σ-order complete vector lattice has the Principal Projection Property. -/
instance (priority := 100)
    HasPrincipalProjectionProperty.of_isSigmaOrderComplete
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    HasPrincipalProjectionProperty X := by
  haveI : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  refine ⟨fun a => ?_⟩
  have hband_eq : (Band.generated ({a} : Set X) : Set X)
      = (Band.generated ({|a|} : Set X) : Set X) := by
    apply le_antisymm <;> apply Band.generated_le <;> rintro y rfl
    · refine (Band.generated _).mem_of_abs_le_abs
        (Band.subset_generated _ rfl) ?_
      rw [abs_abs]
    · exact (Band.generated _).abs_mem (Band.subset_generated _ rfl)
  have habs_nn : (0 : X) ≤ |a| := abs_nonneg a
  have hLUB : ∀ x : X, 0 ≤ x →
      ∃ s, IsLUB (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|) s := by
    intro x hx
    have hcount : (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|).Countable :=
      Set.countable_range _
    have hne : (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|).Nonempty :=
      Set.range_nonempty _
    have hbdd : BddAbove (Set.range fun n : ℕ => x ⊓ (n : ℕ) • |a|) :=
      ⟨x, by rintro _ ⟨n, rfl⟩; exact inf_le_left⟩
    refine ⟨sSup _,
      fun _ hy => SigmaConditionallyCompleteLattice.le_csSup _ _ hcount hbdd hy,
      fun _ hy => SigmaConditionallyCompleteLattice.csSup_le _ _ hcount hne hy⟩
  obtain ⟨P, hP⟩ :=
    (ProjectionBand.principalBand_projectionBand_iff_isLUB_range habs_nn).mpr hLUB
  exact ⟨P, hP.trans hband_eq.symm⟩

end OrderComplete

section Rest

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### Disjoint refinement of finite positive families

Under PPP, any finite family of positive vectors may be replaced by a
pairwise disjoint family of positive vectors, dominated termwise by the
original family, whose sum equals the supremum of the original family. -/

private lemma ProjectionBand.bandProjection_eq_zero_of_mem_disjointComplement
    (B : ProjectionBand X) {z : X}
    (hz : z ∈ disjointComplement (B : Set X)) :
    B.bandProjection z = 0 := by
  have h0_mem : (0 : X) ∈ (B : Set X) := B.toBand.toOrderIdeal.toSubmodule.zero_mem
  have hdec : z = B.bandProjection z + (z - B.bandProjection z) := by abel
  exact (B.decomposition_unique (B.bandProjection_mem z)
    (B.id_sub_bandProjection_mem z) h0_mem hz hdec (zero_add z).symm).1

/-- For two positive elements in a vector lattice with PPP, their sum can be
rewritten as a sum of two positive disjoint elements, with the new summands
dominated by `2 • x` and `2 • y` respectively. -/
theorem exists_disjoint_add_eq_add_of_hasPrincipalProjectionProperty
    [HasPrincipalProjectionProperty X] {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ u v : X, IsVLDisjoint u v ∧ 0 ≤ u ∧ 0 ≤ v ∧
      u ≤ (2 : ℕ) • x ∧ v ≤ (2 : ℕ) • y ∧ u + v = x + y := by
  obtain ⟨P, hP⟩ := HasPrincipalProjectionProperty.exists_projectionBand ((x - y)⁺)
  set a := x + y
  set u := P.bandProjection a
  set v := a - u
  have ha : 0 ≤ a := by simp [a, add_nonneg hx hy]
  have hu_mem : u ∈ (P : Set X) := by
    exact P.bandProjection_mem a
  have hv_mem : v ∈ disjointComplement (P : Set X) := by
    simpa [u, v] using P.id_sub_bandProjection_mem a
  have huv : IsVLDisjoint u v :=
    isVLDisjoint_comm.mp (hv_mem _ hu_mem)
  have hu0 : 0 ≤ u := by
    simpa [u] using Positive.zero_le_iff.mp P.bandProjection_nonneg a ha
  have hv0 : 0 ≤ v := by
    have hu_le_a : u ≤ a := by
      simpa [u] using Positive.le_iff.mp P.bandProjection_le_id a ha
    simpa [v] using sub_nonneg.mpr hu_le_a
  have hmono : Monotone P.bandProjection :=
    Positive.monotone_iff.mpr (Positive.zero_le_iff.mp P.bandProjection_nonneg)
  have hgen_sub :
      (Band.generated ({(x - y)⁺} : Set X) : Set X) ⊆
        disjointComplement ({(x - y)⁻} : Set X) := by
    refine Band.generated_le (B := Band.disjointComplement ({(x - y)⁻} : Set X)) ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change (x - y)⁺ ∈ disjointComplement ({(x - y)⁻} : Set X)
    rw [mem_disjointComplement_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact isVLDisjoint_posPart_negPart (x - y)
  have hneg_mem : (x - y)⁻ ∈ disjointComplement (P : Set X) := by
    intro z hz
    have hz_gen : z ∈ (Band.generated ({(x - y)⁺} : Set X) : Set X) := by
      simpa [hP] using hz
    have hz_dc : z ∈ disjointComplement ({(x - y)⁻} : Set X) :=
      hgen_sub hz_gen
    exact isVLDisjoint_comm.mp (hz_dc _ (Set.mem_singleton _))
  have hPneg_zero : P.bandProjection ((x - y)⁻) = 0 :=
    ProjectionBand.bandProjection_eq_zero_of_mem_disjointComplement P hneg_mem
  have ha_le_x : a ≤ (2 : ℕ) • x + (x - y)⁻ := by
    have hyx_le : y - x ≤ (x - y)⁻ := by
      rw [show y - x = -(x - y) by abel, negPart_def]
      exact le_sup_left
    calc
      a = (2 : ℕ) • x + (y - x) := by
        simp [a]
        abel
      _ ≤ (2 : ℕ) • x + (x - y)⁻ := by gcongr
  have hu_le : u ≤ (2 : ℕ) • x := by
    calc
      u ≤ P.bandProjection ((2 : ℕ) • x + (x - y)⁻) := by
        simpa [u] using hmono ha_le_x
      _ = P.bandProjection ((2 : ℕ) • x) + P.bandProjection ((x - y)⁻) := by
        rw [map_add]
      _ = P.bandProjection ((2 : ℕ) • x) := by rw [hPneg_zero, add_zero]
      _ ≤ (2 : ℕ) • x := by
        exact Positive.le_iff.mp P.bandProjection_le_id _ (nsmul_nonneg hx 2)
  have hpos_mem : (x - y)⁺ ∈ (P : Set X) := by
    rw [hP]
    exact Band.subset_generated _ rfl
  have hpos_mem_comp :
      (x - y)⁺ ∈ disjointComplement ((Pᶜ : ProjectionBand X) : Set X) := by
    intro z hz
    exact isVLDisjoint_comm.mp (hz _ hpos_mem)
  have hPcpos_zero : (Pᶜ : ProjectionBand X).bandProjection ((x - y)⁺) = 0 :=
    ProjectionBand.bandProjection_eq_zero_of_mem_disjointComplement (Pᶜ) hpos_mem_comp
  have hmono_comp : Monotone (Pᶜ : ProjectionBand X).bandProjection :=
    Positive.monotone_iff.mpr
      (Positive.zero_le_iff.mp (Pᶜ : ProjectionBand X).bandProjection_nonneg)
  have ha_le_y : a ≤ (2 : ℕ) • y + (x - y)⁺ := by
    have hxy_le : x - y ≤ (x - y)⁺ := by
      rw [posPart_def]
      exact le_sup_left
    calc
      a = (2 : ℕ) • y + (x - y) := by
        simp [a]
        abel
      _ ≤ (2 : ℕ) • y + (x - y)⁺ := by gcongr
  have hv_eq : (Pᶜ : ProjectionBand X).bandProjection a = v := by
    rw [ProjectionBand.bandProjection_compl]
    simp [u, v]
  have hv_le : v ≤ (2 : ℕ) • y := by
    calc
      v = (Pᶜ : ProjectionBand X).bandProjection a := hv_eq.symm
      _ ≤ (Pᶜ : ProjectionBand X).bandProjection ((2 : ℕ) • y + (x - y)⁺) :=
        hmono_comp ha_le_y
      _ = (Pᶜ : ProjectionBand X).bandProjection ((2 : ℕ) • y) +
          (Pᶜ : ProjectionBand X).bandProjection ((x - y)⁺) := by
            rw [map_add]
      _ = (Pᶜ : ProjectionBand X).bandProjection ((2 : ℕ) • y) := by
        rw [hPcpos_zero, add_zero]
      _ ≤ (2 : ℕ) • y := by
        exact Positive.le_iff.mp (Pᶜ : ProjectionBand X).bandProjection_le_id _
          (nsmul_nonneg hy 2)
  refine ⟨u, v, huv, hu0, hv0, hu_le, hv_le, ?_⟩
  calc
    u + v = a := by
      simp [v]
    _ = x + y := by simp [a]

/-
/-- **Replacement of a positive sum by a disjoint sum.** Let `X` be a vector
lattice with PPP and `x₁, …, xₙ ∈ X₊`. There exist pairwise disjoint
`y₁, …, yₙ ∈ X₊` with `yᵢ ≤ xᵢ` for every `i`, and
`∑ᵢ yᵢ = ⋁ᵢ xᵢ`. -/
theorem exists_disjoint_sum_eq_sup_of_hasPrincipalProjectionProperty
    [HasPrincipalProjectionProperty X] {n : ℕ}
    (x : Fin (n + 1) → X) (hx : ∀ i, 0 ≤ x i) :
    ∃ y : Fin (n + 1) → X,
      (∀ i j, i ≠ j → IsVLDisjoint (y i) (y j))
        ∧ (∀ i, 0 ≤ y i)
        ∧ (∀ i, y i ≤ x i)
        ∧ ∑ i, y i = Finset.univ.sup' Finset.univ_nonempty x := sorry

/-! ### The Archimedean property -/

/-- A vector lattice with the Principal Projection Property is Archimedean. -/
theorem isVLArchimedean_of_hasPrincipalProjectionProperty
    [HasPrincipalProjectionProperty X] : IsVLArchimedean X := sorry

/-- A vector lattice with the Projection Property is Archimedean. -/
theorem isVLArchimedean_of_hasProjectionProperty
    [HasProjectionProperty X] : IsVLArchimedean X :=
  isVLArchimedean_of_hasPrincipalProjectionProperty
-/

end Rest
