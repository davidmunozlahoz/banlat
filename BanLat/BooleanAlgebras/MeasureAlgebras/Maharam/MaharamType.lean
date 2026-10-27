/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Atomless
import BanLat.BooleanAlgebras.MeasureAlgebras.Metric
import BanLat.Preliminaries.DensityCharacter

/-!
# Maharam type and homogeneous measure algebras

Let `(B, μ)` be a measure algebra, and `b ∈ B`. This file defines:
* The **Maharam type below `b`**: the density character of the relative
measure algebra below `b`.
* The **Maharam type of `(B, μ)`**: the density character of `(B, μ)`.
Equivalently, its Maharam type below `⊤`.
* **Homogeneous measure algebras**: those in which every non-trivial relative
measure algebra has the same Maharam type.

It also proves that density character, Maharam type, and homogeneity are
preserved by measure-algebra equivalences.
-/

open Set
open scoped ENNReal

universe u v

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- The **Maharam type of `(B, μ)` below `b ∈ B`** is the density character of the
relative measure algebra `(Set.Iic b, μ.restrict b)`. -/
noncomputable def maharamTypeBelow (μ : MeasureAlgebra B) (b : B) : Cardinal.{u} :=
  (μ.restrict b).densityCharacter

/-- The **Maharam type `μ.maharamType` of `(B, μ)`** is its density character
`μ.densityCharacter`. -/
noncomputable def maharamType (μ : MeasureAlgebra B) : Cardinal.{u} :=
  μ.densityCharacter

/-- The Maharam type `μ.maharamType` of a nontrivial atomless measure algebra
is at least `ℵ₀`. -/
theorem aleph0_le_maharamType_of_isAtomless [Nontrivial B]
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B) :
    Cardinal.aleph0 ≤ μ.maharamType := by
  letI : Infinite B := BooleanAlgebra.infinite_of_isAtomless hB
  letI := μ.toMetricSpace
  unfold maharamType densityCharacter
  exact TopologicalSpace.aleph0_le_densityCharacter _

/-- For every `b ∈ B`, `μ.maharamTypeBelow b ≤ μ.densityCharacter`. -/
theorem maharamTypeBelow_le_densityCharacter
    (μ : MeasureAlgebra B) (b : B) :
    μ.maharamTypeBelow b ≤ μ.densityCharacter := by
  let f : B → Set.Iic b := fun c ↦ ⟨c ⊓ b, inf_le_right⟩
  unfold maharamTypeBelow densityCharacter
  refine @TopologicalSpace.densityCharacter_le_of_continuous_surjective
    B (Set.Iic b)
    μ.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (μ.restrict b).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f ?_ ?_
  · apply (@Metric.continuous_iff B (Set.Iic b)
      μ.toMetricSpace.toPseudoMetricSpace
      (μ.restrict b).toMetricSpace.toPseudoMetricSpace f).2
    intro c ε hε
    refine ⟨ε, hε, ?_⟩
    intro d hdc
    apply lt_of_le_of_lt _ hdc
    simp only [f, dist_eq_measure_symmDiff]
    have hcoe :
        ((symmDiff (f d) (f c) : Set.Iic b) : B) =
          symmDiff (d ⊓ b) (c ⊓ b) := by
      simp [f]
    change (μ ((symmDiff (f d) (f c) : Set.Iic b) : B)).toReal ≤
      (μ (symmDiff d c)).toReal
    rw [hcoe]
    rw [← inf_symmDiff_distrib_right]
    exact ENNReal.toReal_mono (μ.measure_ne_top _) (μ.measure_mono inf_le_left)
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact inf_eq_left.mpr hc

/-- A measure algebra **`(B, μ)` is homogeneous** when
`μ.maharamTypeBelow b = μ.maharamType` for every `b ∈ B`, `b ≠ ⊥`. -/
def IsHomogeneous (μ : MeasureAlgebra B) : Prop :=
  ∀ ⦃b : B⦄, b ≠ ⊥ → μ.maharamTypeBelow b = μ.maharamType

/-- If `B` is atomless, `μ.densityCharacter ≤ ℵ₀`, and `b ≠ ⊥`, then
`μ.maharamTypeBelow b = ℵ₀`. -/
theorem maharamTypeBelow_eq_aleph0_of_isAtomless_of_densityCharacter_le
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    (hμ : μ.densityCharacter ≤ Cardinal.aleph0)
    {b : B} (hb : b ≠ ⊥) :
    μ.maharamTypeBelow b = Cardinal.aleph0 := by
  letI : Nontrivial (Set.Iic b) := ⟨⟨⊥, ⊤, fun h ↦ hb (congrArg Subtype.val h).symm⟩⟩
  apply le_antisymm (μ.maharamTypeBelow_le_densityCharacter b |>.trans hμ)
  exact aleph0_le_densityCharacter_of_isAtomless
    (μ.restrict b) hB.iic

/-- If `(B, μ)` is nontrivial and atomless and `μ.densityCharacter ≤ ℵ₀`, then
`μ.maharamType = ℵ₀`. -/
theorem maharamType_eq_aleph0_of_isAtomless_of_densityCharacter_le
    [Nontrivial B] (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    (hμ : μ.densityCharacter ≤ Cardinal.aleph0) :
    μ.maharamType = Cardinal.aleph0 := by
  exact le_antisymm hμ (μ.aleph0_le_maharamType_of_isAtomless hB)

/-- If `B` is atomless and `μ.densityCharacter ≤ ℵ₀`, then `(B, μ)` is
homogeneous: for every `b ≠ ⊥`,
`μ.maharamTypeBelow b = μ.maharamType = ℵ₀`. -/
theorem isHomogeneous_of_isAtomless_of_densityCharacter_le
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    (hμ : μ.densityCharacter ≤ Cardinal.aleph0) :
    μ.IsHomogeneous := by
  intro b hb
  letI : Nontrivial B := ⟨⟨b, ⊥, hb⟩⟩
  rw [μ.maharamTypeBelow_eq_aleph0_of_isAtomless_of_densityCharacter_le hB hμ hb]
  exact (le_antisymm hμ (aleph0_le_densityCharacter_of_isAtomless μ hB)).symm

/-- Every atomless separable measure algebra `(B, μ)` is homogeneous.
More precisely, for every `b ≠ ⊥`,
`μ.maharamTypeBelow b = μ.maharamType = ℵ₀`. -/
theorem isHomogeneous_of_isAtomless_of_isSeparable
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B)
    (hμ :
      letI := μ.toMetricSpace
      TopologicalSpace.SeparableSpace B) :
    μ.IsHomogeneous := by
  letI := μ.toMetricSpace
  letI : TopologicalSpace.SeparableSpace B := hμ
  exact μ.isHomogeneous_of_isAtomless_of_densityCharacter_le hB
    (TopologicalSpace.densityCharacter_le_aleph0 B)

end MeasureAlgebra

namespace MeasureAlgebraEquiv

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

/-- A measure-algebra equivalence preserves the Maharam type
of every element. -/
@[simp]
theorem map_maharamTypeBelow (e : MeasureAlgebraEquiv μ ν) (b : B) :
    Cardinal.lift.{u} (ν.maharamTypeBelow (e.toRelIso b)) =
      Cardinal.lift.{v} (μ.maharamTypeBelow b) := by
  exact (e.restrict b).densityCharacter_eq

/-- A measure-algebra equivalence preserves the Maharam type
of the whole measure algebra. -/
theorem map_maharamType (e : MeasureAlgebraEquiv μ ν) :
    Cardinal.lift.{u} ν.maharamType = Cardinal.lift.{v} μ.maharamType := by
  exact e.densityCharacter_eq

/-- A measure-algebra equivalence maps forward homogeneity. -/
private theorem isHomogeneous_of_equiv (e : MeasureAlgebraEquiv μ ν) :
    μ.IsHomogeneous → ν.IsHomogeneous := by
  intro hμ c hc
  apply Cardinal.lift_injective.{u}
  have ha : e.toRelIso.symm c ≠ ⊥ := by
    intro ha
    apply hc
    calc
      c = e (e.toRelIso.symm c) := (e.toRelIso.apply_symm_apply c).symm
      _ = e ⊥ := congrArg e ha
      _ = ⊥ := OrderIso.map_bot e.toRelIso
  calc
    Cardinal.lift.{u} (ν.maharamTypeBelow c) =
        Cardinal.lift.{v} (μ.maharamTypeBelow (e.toRelIso.symm c)) := by
      simpa using e.map_maharamTypeBelow (e.toRelIso.symm c)
    _ = Cardinal.lift.{v} μ.maharamType := congrArg _ (hμ ha)
    _ = Cardinal.lift.{u} ν.maharamType := e.map_maharamType.symm

/-- Homogeneity is invariant under measure-algebra equivalence. -/
theorem isHomogeneous_iff (e : MeasureAlgebraEquiv μ ν) :
    μ.IsHomogeneous ↔ ν.IsHomogeneous := by
  exact ⟨isHomogeneous_of_equiv e, isHomogeneous_of_equiv e.symm⟩

end MeasureAlgebraEquiv

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- The Maharam type below `⊤` is the Maharam type of the whole measure algebra:
`μ.maharamTypeBelow ⊤ = μ.maharamType`. -/
@[simp]
theorem maharamTypeBelow_top (μ : MeasureAlgebra B) :
    μ.maharamTypeBelow ⊤ = μ.maharamType := by
  let e : MeasureAlgebraEquiv μ (μ.restrict ⊤) :=
    { OrderIso.IicTop.symm with map_measure' := fun _ ↦ rfl }
  simpa only [maharamType, maharamTypeBelow, Cardinal.lift_id] using
    e.densityCharacter_eq

end MeasureAlgebra
