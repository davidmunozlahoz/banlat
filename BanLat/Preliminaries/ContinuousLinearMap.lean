/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Closed spans and ranges of continuous linear maps

For a continuous linear map `T : E → F` with closed range, the image of a family
whose linear span is dense in `E` has closed linear span equal to `range(T)`.
The same conclusion holds for a family obtained by rescaling the image by a fixed unit.
-/

namespace ContinuousLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [TopologicalSpace E] [Module R E]
  [AddCommMonoid F] [TopologicalSpace F] [Module R F]
  [ContinuousAdd F] [ContinuousConstSMul R F]

/-- Let `T : E → F` be a continuous linear map with closed range.
If `closure(span(s)) = E`, then `range(T) = closure(span(T(s)))`. -/
theorem range_eq_topologicalClosure_span_image
    (T : E →L[R] F) (s : Set E)
    (hs : Dense (Submodule.span R s : Set E))
    (hclosed : IsClosed (T.range : Set F)) :
    T.range = (Submodule.span R (T '' s)).topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact closure_mono (Submodule.image_span_subset_span T.toLinearMap s)
      (mem_closure_image T.continuous.continuousAt (hs x))
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hclosed
    exact fun _ ⟨x, _, hxy⟩ ↦ ⟨x, hxy⟩

/-- Let `T : E → F` be a continuous linear map with closed range.
If `closure(span{eᵢ}) = E` and `T(eᵢ) = c • fᵢ` for a unit `c ∈ R`, then
`range(T) = closure(span{fᵢ})`. -/
theorem range_eq_topologicalClosure_span_range_of_smul {ι : Type*}
    (T : E →L[R] F) (e : ι → E) (f : ι → F)
    (he : Dense (Submodule.span R (Set.range e) : Set E))
    (hclosed : IsClosed (T.range : Set F))
    (c : R) (hc : IsUnit c) (hT : ∀ i, T (e i) = c • f i) :
    T.range = (Submodule.span R (Set.range f)).topologicalClosure := by
  rw [T.range_eq_topologicalClosure_span_image (Set.range e) he hclosed]
  simp_rw [← Set.range_comp, Function.comp_def, hT]
  rw [Set.range_smul, Submodule.span_smul_eq_of_isUnit _ _ hc]

end ContinuousLinearMap
