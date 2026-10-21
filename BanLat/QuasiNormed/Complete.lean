/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.QuasiNormed.Topology

/-!
# Complete quasi-normed spaces

This file defines completeness for the uniform structure induced by a quasi-seminorm and gives
filter and sequential characterizations. It also defines **quasi-Banach spaces** over complete
normed fields and proves that Banach spaces are particular instances of them.
-/

open Filter

open scoped Topology

/-- Completeness for the uniform structure induced by a quasi-seminorm. -/
abbrev QuasiSeminormCompleteSpace (E : Type*)
    [AddCommGroup E] [Norm E] [IsQuasiSeminorm E] :=
  @CompleteSpace E (IsQuasiSeminorm.uniformSpace E)

/-- A quasi-Banach space over a normed field is a complete quasi-normed space. -/
class QuasiBanachSpace (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [Norm E]
    [IsQuasiNorm E] extends QuasiNormedSpace 𝕜 E,
      @CompleteSpace E (IsQuasiSeminorm.uniformSpace E)

namespace IsQuasiSeminorm

variable {E : Type*} [AddCommGroup E] [Norm E] [IsQuasiSeminorm E]

/-- Every Cauchy filter on a complete quasi-seminormed group converges. -/
theorem cauchy_tendsto [QuasiSeminormCompleteSpace E] {F : Filter E}
    (hF : F.NeBot ∧ ∀ ε > 0, ∃ M ∈ F, ∀ x ∈ M, ∀ y ∈ M, ‖y - x‖ < ε) :
    ∃ x, F ≤ @nhds E (topology E) x := by
  let : UniformSpace E := uniformSpace E
  exact CompleteSpace.complete (cauchy_iff.mpr hF)

/-- Completeness is equivalent to convergence of every quasi-seminorm Cauchy filter. -/
theorem quasiSeminormCompleteSpace_iff_cauchy_tendsto :
    QuasiSeminormCompleteSpace E ↔
      ∀ F : Filter E,
        (F.NeBot ∧ ∀ ε > 0, ∃ M ∈ F, ∀ x ∈ M, ∀ y ∈ M, ‖y - x‖ < ε) →
          ∃ x, F ≤ @nhds E (topology E) x := by
  constructor
  · intro hcomplete
    let : QuasiSeminormCompleteSpace E := hcomplete
    exact fun _ ↦ cauchy_tendsto
  · intro h
    let : UniformSpace E := uniformSpace E
    exact ⟨fun {F} hF ↦ h F (cauchy_iff.mp hF)⟩

/-- Every Cauchy sequence in a complete quasi-seminormed group converges. -/
theorem cauchySeq_tendsto [QuasiSeminormCompleteSpace E] {u : ℕ → E}
    (hu : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖u n - u m‖ < ε) :
    ∃ x, ∀ ε > 0, ∀ᶠ n in atTop, ‖u n - x‖ < ε := by
  let : UniformSpace E := uniformSpace E
  have hu' : CauchySeq u := cauchySeq_iff.mpr hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hu'
  change Tendsto u atTop (@nhds E (topology E) x) at hx
  exact ⟨x, tendsto_nhds_iff.mp hx⟩

/-- Sequential completeness for quasi-seminorm Cauchy sequences implies completeness. -/
theorem quasiSeminormCompleteSpace_of_cauchySeq_tendsto
    (h : ∀ u : ℕ → E,
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖u n - u m‖ < ε) →
        ∃ x, ∀ ε > 0, ∀ᶠ n in atTop, ‖u n - x‖ < ε) :
    QuasiSeminormCompleteSpace E := by
  let : UniformSpace E := uniformSpace E
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨x, hx⟩ := h u (cauchySeq_iff.mp hu)
  exact ⟨x, tendsto_nhds_iff.mpr hx⟩

/-- Completeness is equivalent to convergence of every quasi-seminorm Cauchy sequence. -/
theorem quasiSeminormCompleteSpace_iff_cauchySeq_tendsto :
    QuasiSeminormCompleteSpace E ↔
      ∀ u : ℕ → E,
        (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖u n - u m‖ < ε) →
          ∃ x, ∀ ε > 0, ∀ᶠ n in atTop, ‖u n - x‖ < ε := by
  constructor
  · intro hcomplete
    let : QuasiSeminormCompleteSpace E := hcomplete
    exact fun _ ↦ cauchySeq_tendsto
  · exact quasiSeminormCompleteSpace_of_cauchySeq_tendsto

/-- A complete seminormed additive group is complete for its induced quasi-seminorm uniformity. -/
instance (priority := 100) instQuasiSeminormCompleteSpaceOfCompleteSpace
    (E : Type*) [SeminormedAddCommGroup E] [CompleteSpace E] :
    QuasiSeminormCompleteSpace E := by
  rw [QuasiSeminormCompleteSpace, uniformSpace_eq E]
  infer_instance

end IsQuasiSeminorm

/-- Every Banach space is a quasi-Banach space. -/
instance (priority := 100) NormedSpace.toQuasiBanachSpace
    (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] : QuasiBanachSpace 𝕜 E where
  toQuasiNormedSpace := NormedSpace.toQuasiNormedSpace 𝕜 E
  toCompleteSpace :=
    IsQuasiSeminorm.instQuasiSeminormCompleteSpaceOfCompleteSpace E
