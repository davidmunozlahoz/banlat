/-
Authors: Pedro Tradacete
-/

import BanLat.Substructures.Band.PPP
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Completeness of projection bands

Band projections preserve existing suprema. In a vector lattice with the projection
property, every band is a projection band, so the complete lattice of bands equips
projection bands with a complete Boolean algebra structure. A family of projection
bands is covering when its supremum is the whole space. The band projections
associated with a covering family separate points.
-/

noncomputable section

namespace ProjectionBand

variable {D : Type*} [AddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [VectorLattice D]

/-- Projecting first onto a larger band does not change projection onto a smaller band. -/
theorem bandProjection_comp_of_le (B C : ProjectionBand D) (hBC : B ≤ C)
    (z : D) : B.bandProjection (C.bandProjection z) = B.bandProjection z := by
  have h := congrArg (fun f : D →ₗ[ℝ] D ↦ f z)
    (ProjectionBand.bandProjection_inf B C)
  rw [inf_eq_left.mpr hBC] at h
  exact h.symm

/-- A band projection sends an existing supremum to the supremum of the
projected family. -/
theorem isLUB_bandProjection_image (B : ProjectionBand D) {S : Set D} {s : D}
    (hs : IsLUB S s) :
    IsLUB (B.bandProjection '' S) (B.bandProjection s) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact (Positive.monotone_iff.mpr
      (Positive.zero_le_iff.mp B.bandProjection_nonneg)) (hs.1 hx)
  · intro u hu
    have hbound : ∀ x ∈ S, x ≤ u + Bᶜ.bandProjection s := by
      intro x hx
      have hPx : B.bandProjection x ≤ u := hu ⟨x, hx, rfl⟩
      have hQx : Bᶜ.bandProjection x ≤ Bᶜ.bandProjection s :=
        (Positive.monotone_iff.mpr
          (Positive.zero_le_iff.mp Bᶜ.bandProjection_nonneg)) (hs.1 hx)
      have hdecomp_x : x = B.bandProjection x + Bᶜ.bandProjection x := by
        rw [ProjectionBand.bandProjection_compl]
        simp
      rw [hdecomp_x]
      exact add_le_add hPx hQx
    have hsu : s ≤ u + Bᶜ.bandProjection s := hs.2 hbound
    have hdecomp_s : s = B.bandProjection s + Bᶜ.bandProjection s := by
      rw [ProjectionBand.bandProjection_compl]
      simp
    have hsu' : B.bandProjection s + Bᶜ.bandProjection s ≤
        u + Bᶜ.bandProjection s := hdecomp_s.symm.le.trans hsu
    exact (add_le_add_iff_right _).mp hsu'

private theorem toBand_injective :
    Function.Injective (ProjectionBand.toBand : ProjectionBand D → Band D) := by
  intro P Q h
  apply SetLike.ext'
  exact congrArg (fun C : Band D ↦ (C : Set D)) h

section ProjectionProperty

variable [HasProjectionProperty D]

/-- The projection band corresponding to a band when the projection property holds. -/
def ofBand (B : Band D) : ProjectionBand D :=
  Classical.choose (HasProjectionProperty.exists_projectionBand B)

/-- Converting a band to a projection band preserves its underlying band. -/
@[simp] theorem toBand_ofBand (B : Band D) :
    (ofBand B).toBand = B := by
  apply SetLike.ext'
  exact Classical.choose_spec (HasProjectionProperty.exists_projectionBand B)

/-- Supremum of projection bands, transported from bands. -/
noncomputable instance : SupSet (ProjectionBand D) where
  sSup S := ofBand (sSup (ProjectionBand.toBand '' S))

/-- Infimum of projection bands, transported from bands. -/
noncomputable instance : InfSet (ProjectionBand D) where
  sInf S := ofBand (sInf (ProjectionBand.toBand '' S))

/-- The existing finite Boolean operations on projection bands extend to a
complete lattice via the order equivalence with all bands. -/
noncomputable instance : CompleteLattice (ProjectionBand D) :=
  toBand_injective.completeLattice ProjectionBand.toBand
    (by intro P Q; rfl)
    (by intro P Q; rfl)
    (by intro P Q; exact ProjectionBand.sup_toBand P Q)
    (by intro P Q; exact ProjectionBand.inf_toBand P Q)
    (by intro S
        change (ofBand (sSup (ProjectionBand.toBand '' S))).toBand = _
        rw [toBand_ofBand, sSup_image])
    (by intro S
        change (ofBand (sInf (ProjectionBand.toBand '' S))).toBand = _
        rw [toBand_ofBand, sInf_image])
    (by rfl)
    (by rfl)

/-- Under the projection property, projection bands form a complete Boolean algebra. -/
noncomputable instance : CompleteBooleanAlgebra (ProjectionBand D) where
  __ := (inferInstance : CompleteLattice (ProjectionBand D))
  __ := (inferInstance : BooleanAlgebra (ProjectionBand D))

/-- The band projections associated with a covering family separate points.
This is the uniqueness principle behind restriction of local sections. -/
theorem eq_of_bandProjection_eq_on_cover (A : Set (ProjectionBand D))
    (hA : sSup A = ⊤) {x y : D}
    (hxy : ∀ B ∈ A, B.bandProjection x = B.bandProjection y) : x = y := by
  let z := x - y
  let C : Band D := Band.disjointComplement ({z} : Set D)
  have hBC : ∀ B ∈ A, B ≤ ofBand C := by
    intro B hB v hv
    have hBz : B.bandProjection z = 0 := by
      dsimp [z]
      rw [map_sub, hxy B hB, sub_self]
    have hzBd : z ∈ disjointComplement (B : Set D) := by
      simpa only [hBz, sub_zero] using B.id_sub_bandProjection_mem z
    change v ∈ (ofBand C).toBand
    rw [toBand_ofBand]
    change ∀ a ∈ ({z} : Set D), IsVLDisjoint v a
    intro a ha
    have haz : a = z := ha
    subst a
    exact isVLDisjoint_comm.mp (hzBd v hv)
  have htopC : (⊤ : ProjectionBand D) ≤ ofBand C := by
    rw [← hA]
    exact sSup_le hBC
  have hzC : z ∈ C := by
    have hzTop : z ∈ (⊤ : ProjectionBand D) := ProjectionBand.mem_top
    have := htopC hzTop
    change z ∈ (ofBand C).toBand at this
    rwa [toBand_ofBand] at this
  have hz0 : z = 0 :=
    Set.mem_singleton_iff.mp
      (disjointComplement_inter_eq_zero ({z} : Set D) ⟨rfl, hzC⟩)
  exact sub_eq_zero.mp hz0

end ProjectionProperty

section DedekindComplete

variable {D : Type*} [AddCommGroup D] [ConditionallyCompleteLattice D]
  [IsOrderedAddMonoid D] [VectorLattice D]

/-- A band projection preserves suprema of nonempty bounded-above sets. -/
theorem bandProjection_sSup (B : ProjectionBand D) (S : Set D)
    (hne : S.Nonempty) (hbdd : BddAbove S) :
    B.bandProjection (sSup S) = sSup (B.bandProjection '' S) := by
  have h := isLUB_bandProjection_image B (isLUB_csSup hne hbdd)
  exact h.unique (isLUB_csSup (hne.image _)
    ((Positive.monotone_iff.mpr
      (Positive.zero_le_iff.mp B.bandProjection_nonneg)).map_bddAbove hbdd))

end DedekindComplete

end ProjectionBand
