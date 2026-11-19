/-
Authors: Pedro Tradacete
-/

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Reflexivity of normed spaces

`IsReflexiveBanachSpace 𝕜 E` expresses surjectivity of the canonical map into
the continuous bidual over `𝕜`. Reflexivity passes to the continuous dual and to
continuously linearly isomorphic spaces over any nontrivially normed field.
Over real or complex scalars, reflexivity also implies completeness and passes
to closed linear subspaces.
-/

noncomputable section

open Set NormedSpace

/-- A normed space over `𝕜` is reflexive when its canonical map into its continuous
bidual is surjective. -/
abbrev IsReflexiveBanachSpace (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)

namespace IsReflexiveBanachSpace

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- The continuous dual of a reflexive normed space is reflexive over the same field. -/
theorem dual (h : IsReflexiveBanachSpace 𝕜 E) :
    IsReflexiveBanachSpace 𝕜 (StrongDual 𝕜 E) := by
  intro G
  refine ⟨G.comp (inclusionInDoubleDual 𝕜 E), ContinuousLinearMap.ext fun g ↦ ?_⟩
  obtain ⟨x, rfl⟩ := h g
  rfl

/-- Reflexivity is preserved by a continuous linear equivalence of normed spaces. -/
theorem of_continuousLinearEquiv (e : E ≃L[𝕜] F) (h : IsReflexiveBanachSpace 𝕜 E) :
    IsReflexiveBanachSpace 𝕜 F := by
  intro G
  let pull : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 F :=
    e.symm.toContinuousLinearMap.precomp 𝕜
  obtain ⟨x, hx⟩ := h (G.comp pull)
  refine ⟨e x, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  have he : pull (φ.comp e.toContinuousLinearMap) = φ :=
    ContinuousLinearMap.ext fun y ↦ congrArg φ (e.apply_symm_apply y)
  exact (congrArg (fun H : StrongDual 𝕜 (StrongDual 𝕜 E) ↦
    H (φ.comp e.toContinuousLinearMap)) hx).trans (congrArg G he)

end NontriviallyNormedField

section RCLike

variable [RCLike 𝕜] [NormedSpace 𝕜 E]

/-- A reflexive normed space over real or complex scalars is complete: its canonical
embedding is a surjective isometry onto the complete continuous bidual. -/
theorem completeSpace (h : IsReflexiveBanachSpace 𝕜 E) : CompleteSpace E :=
  ((inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.completeSpace_congr h).mpr
    inferInstance

/-- A vector lies in a closed submodule whenever every continuous functional
vanishing on that submodule also vanishes at the vector. -/
private lemma mem_closedSubmodule_of_annihilators (S : Submodule 𝕜 E)
    (hS : IsClosed (S : Set E)) {x : E}
    (hx : ∀ φ : StrongDual 𝕜 E, (∀ y : S, φ y = 0) → φ x = 0) : x ∈ S := by
  let : IsClosed (S : Set E) := hS
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜)
  intro φ
  apply hx (φ.comp S.mkQL)
  exact fun y ↦ congrArg φ ((Submodule.Quotient.mk_eq_zero S).mpr y.property) |>.trans (map_zero φ)

/-- Every closed linear subspace of a reflexive normed space over real or complex
scalars is reflexive. -/
theorem closedSubmodule (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E))
    (h : IsReflexiveBanachSpace 𝕜 E) : IsReflexiveBanachSpace 𝕜 S := by
  intro G
  let restrict : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 S := S.subtypeL.precomp 𝕜
  obtain ⟨x, hx⟩ := h (G.comp restrict)
  have hv (φ : StrongDual 𝕜 E) : φ x = G (restrict φ) :=
    congrArg (fun H : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ H φ) hx
  have hm : x ∈ S := mem_closedSubmodule_of_annihilators S hS fun φ hφ ↦
    (hv φ).trans ((congrArg G (show restrict φ = 0 from ContinuousLinearMap.ext hφ)).trans
      (map_zero G))
  refine ⟨⟨x, hm⟩, ContinuousLinearMap.ext fun ψ ↦ ?_⟩
  obtain ⟨φ, hφ, _⟩ := exists_extension_norm_eq S ψ
  exact (hφ ⟨x, hm⟩).symm.trans ((hv φ).trans
    (congrArg G (show restrict φ = ψ from ContinuousLinearMap.ext hφ)))

end RCLike

end IsReflexiveBanachSpace
