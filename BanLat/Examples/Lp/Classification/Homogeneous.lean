/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.Classification
import BanLat.Examples.Lp.DensityCharacter

/-!
# Classification of homogeneous `Lᵖ` spaces

Let `μ` be an atomless probability measure and let `1 ≤ p < ∞`.

If every nontrivial order interval in `Lᵖ(μ)` has density character `κ`, then `Lᵖ(μ)`
is lattice isometric to `Lᵖ([0, 1]^κ)`.

Consequently, if `μ` and `ν` are atomless probability measures whose `Lᵖ` spaces are homogeneous,
then `Lᵖ(μ)` and `Lᵖ(ν)` are lattice isometric exactly when their density characters agree.
-/

open scoped ENNReal NNReal

universe u

namespace MeasureTheory.Lp

variable {α : Type u} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {p : ℝ≥0} [Fact (1 ≤ p)]

/-- For an atomless probability measure `μ`, if `Lᵖ(μ)` is `κ`-homogeneous, then it is lattice
isometric to `Lᵖ(MeasureAlgebra.cubeMeasure κ)`. -/
theorem nonempty_banachLatEquiv_cube_of_isOrderIntervalHomogeneous
    (κ : Cardinal.{u}) (hμ : μ.HasNoAtoms)
    (hhom : TopologicalSpace.IsOrderIntervalHomogeneous (Lp ℝ (p : ENNReal) μ) κ) :
    Nonempty (BanachLatEquiv (Lp ℝ (p : ENNReal) μ)
      (Lp ℝ (p : ENNReal) (MeasureAlgebra.cubeMeasure κ))) := by
  have hκ : TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) = κ := by
    have h := (isOrderIntervalHomogeneous_iff_densityCharacter_restrict κ).mp hhom
      Set.univ MeasurableSet.univ (by simp)
    rwa [Measure.restrict_univ] at h
  have htype : (MeasureAlgebra.ofMeasure μ).maharamType = κ :=
    (densityCharacter_eq_maharamType hμ (NeZero.ne μ)).symm.trans hκ
  have hhom' : (MeasureAlgebra.ofMeasure μ).IsHomogeneous :=
    (isOrderIntervalHomogeneous_iff_isHomogeneous hμ).mp (hκ.symm ▸ hhom)
  obtain ⟨e⟩ :=
    MeasureAlgebra.nonempty_measureAlgebraEquiv_cube_of_isAtomless_of_isHomogeneous_of_top_eq_one
      (MeasureAlgebra.ofMeasure μ)
      (MeasureAlgebra.InducedBooleanAlgebra.isAtomless_of_hasNoAtoms μ hμ) hhom' (by simp)
  rw [htype] at e
  exact ⟨e.lpEquiv⟩

/-- For an atomless probability measure `μ`, if `Lᵖ(μ)` is homogeneous, then it is lattice
isometric to the Lebesgue-cube `Lᵖ` space indexed by its density character. -/
theorem nonempty_banachLatEquiv_cube_densityCharacter
    (hμ : μ.HasNoAtoms)
    (hhom : TopologicalSpace.IsOrderIntervalHomogeneous (Lp ℝ (p : ENNReal) μ)
      (TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ))) :
    Nonempty (BanachLatEquiv (Lp ℝ (p : ENNReal) μ)
      (Lp ℝ (p : ENNReal) (MeasureAlgebra.cubeMeasure
        (TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ))))) := by
  exact nonempty_banachLatEquiv_cube_of_isOrderIntervalHomogeneous _ hμ hhom

variable {β : Type u} [MeasurableSpace β]
variable {ν : Measure β} [IsProbabilityMeasure ν]

/-- For atomless probability measures `μ` and `ν`, the homogeneous spaces `Lᵖ(μ)` and `Lᵖ(ν)`
are lattice isometric exactly when their density characters agree. -/
theorem nonempty_banachLatEquiv_iff_densityCharacter_eq
    (hμ : μ.HasNoAtoms) (hν : ν.HasNoAtoms)
    (hμhom : TopologicalSpace.IsOrderIntervalHomogeneous (Lp ℝ (p : ENNReal) μ)
      (TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ)))
    (hνhom : TopologicalSpace.IsOrderIntervalHomogeneous (Lp ℝ (p : ENNReal) ν)
      (TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) ν))) :
    Nonempty (BanachLatEquiv (Lp ℝ (p : ENNReal) μ) (Lp ℝ (p : ENNReal) ν)) ↔
      TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) μ) =
        TopologicalSpace.densityCharacter (Lp ℝ (p : ENNReal) ν) := by
  constructor
  · rintro ⟨e⟩
    simpa only [Cardinal.lift_id] using
      (TopologicalSpace.densityCharacter_eq_of_homeomorph
        e.toLinearIsometryEquiv.toHomeomorph).symm
  · intro h
    obtain ⟨eμ⟩ := nonempty_banachLatEquiv_cube_densityCharacter hμ hμhom
    obtain ⟨eν⟩ := nonempty_banachLatEquiv_cube_densityCharacter hν hνhom
    rw [h] at eμ
    exact ⟨eμ.trans eν.symm⟩

end MeasureTheory.Lp
