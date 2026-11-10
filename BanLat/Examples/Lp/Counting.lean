/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Ellp.Basic
import BanLat.Examples.Ellp.Sum

/-!
# `ℓ^p(α; ℝ)` as `L^p(α, count; ℝ)`

For every `1 ≤ p ≤ ∞`, `L^p(α, 𝒫(α), count; ℝ)` is lattice isometric
to `ℓ^p(α; ℝ)`.
-/

open MeasureTheory
open scoped ENNReal lp

noncomputable section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
  {p : ENNReal} [Fact (1 ≤ p)]

namespace Lp

/-! ### Lattice isometry between `L_p(count_α; ℝ)` and `ℓ^p(α; ℝ)` -/

private noncomputable def lpCountLinearIsometryEquiv :
    Lp ℝ p (Measure.count : Measure α) ≃ₗᵢ[ℝ] ℓ^p(α, ℝ) := by
  let : Fact (0 < p) := ⟨zero_lt_one.trans_le (Fact.out : 1 ≤ p)⟩
  exact (lpCountQuasiLinearIsometryEquiv (α := α) (p := p)).toLinearIsometryEquiv

private lemma lpCountLinearIsometryEquiv_map_sup
    (f g : Lp ℝ p (Measure.count : Measure α)) :
    lpCountLinearIsometryEquiv (f ⊔ g) =
    lpCountLinearIsometryEquiv f ⊔ lpCountLinearIsometryEquiv g := by
  apply lp.ext
  funext i
  exact Measure.ae_count_iff.mp (Lp.coeFn_sup f g) i

/-- For `1 ≤ p ≤ ∞`, the lattice isometry from `L_p(count_α; ℝ)` to `ℓ^p(α; ℝ)`,
where `count_α` is the counting measure over `α`. -/
noncomputable def lpCountEquiv :
    BanachLatEquiv
      (Lp ℝ p (Measure.count : Measure α))
      (ℓ^p(α, ℝ)) := by
  refine
    { toLinearIsometryEquiv := lpCountLinearIsometryEquiv
      map_sup' := lpCountLinearIsometryEquiv_map_sup
      map_inf' := fun f g ↦ ?_ }
  apply lp.ext
  funext i
  exact Measure.ae_count_iff.mp (Lp.coeFn_inf f g) i

/-- For `1 ≤ p ≤ ∞`, the image of `f ∈ L_p(count_α; ℝ)` in `ℓ^p(α; ℝ)` has
coordinate `f(a)` at every `a ∈ α`. -/
@[simp]
lemma lpCountEquiv_apply
    (f : Lp ℝ p (Measure.count : Measure α)) (x : α) :
    lpCountEquiv f x = f x := by
  rfl

/-- For `1 ≤ p ≤ ∞`, the image of `f ∈ ℓ^p(α; ℝ)` under the inverse equivalence
in `L_p(count_α; ℝ)` has value `f(a)` at every `a ∈ α`. -/
@[simp]
lemma lpCountEquiv_symm_apply
    (f : ℓ^p(α, ℝ)) (x : α) :
    ((lpCountEquiv (α := α) (p := p)).symm f :
      Lp ℝ p (Measure.count : Measure α)) x = f x := by
  exact congrArg (fun g : ℓ^p(α, ℝ) ↦ g x)
    ((lpCountEquiv (α := α) (p := p)).toLinearIsometryEquiv.apply_symm_apply f)

end Lp

end MeasureTheory
