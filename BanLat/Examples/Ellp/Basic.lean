/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.LpSum

/-!
# `ℓ^p` spaces as Banach lattices

For every index set `ι` and `1 ≤ p ≤ ∞`, the space `ℓ^p(ι, ℝ)` is a
Banach lattice under the coordinate-wise order and the usual `ℓ^p` norm.
Its lattice structure is specialization of the general `ℓ^p`-sum of a family
of Banach lattices to the case in which every summand is `ℝ`.

An equivalence `e : κ ≃ ι`  of index types induces a Banach lattice isometry
between `ℓ^p(ι, ℝ)` and `ℓ^p(κ, ℝ)`.
-/

open scoped ENNReal lp

noncomputable section

namespace MeasureTheory.Lp

variable {ι κ : Type*} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Reindexing `ℓ^p` spaces -/

private lemma memℓp_comp_equiv (e : κ ≃ ι) (f : ι → ℝ) :
    Memℓp (fun j => f (e j)) p ↔ Memℓp f p := by
  rcases eq_or_ne p ∞ with hp | hp
  · subst hp
    rw [memℓp_infty_iff, memℓp_infty_iff]
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨i, rfl⟩
      simpa using hC ⟨e.symm i, rfl⟩
    · rintro ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact hC ⟨e j, rfl⟩
  · have hp0 : p ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) Fact.out)
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [memℓp_gen_iff hpos, memℓp_gen_iff hpos]
    exact e.summable_iff (f := fun i => ‖f i‖ ^ p.toReal)

/-- An equivalence of index types induces a lattice isometry between the
corresponding `ℓ^p` spaces by reindexing coordinates. -/
noncomputable def lpCongr (e : κ ≃ ι) :
    BanachLatEquiv
      (ℓ^p(ι, ℝ))
      (ℓ^p(κ, ℝ)) := by
  let reindex : ℓ^p(ι, ℝ) →ₗᵢ[ℝ] ℓ^p(κ, ℝ) :=
    { toLinearMap :=
        { toFun := fun f =>
            ⟨fun j => f (e j), (memℓp_comp_equiv e f).2 (lp.memℓp f)⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      norm_map' := fun f => by
        rcases eq_or_ne p ∞ with hp | hp
        · subst hp
          rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
          exact e.iSup_congr fun _ => rfl
        · have hp0 : p ≠ 0 := ne_of_gt
            (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) Fact.out)
          have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
          rw [lp.norm_eq_tsum_rpow hpos, lp.norm_eq_tsum_rpow hpos]
          congr 1
          exact e.tsum_eq (fun i => ‖f i‖ ^ p.toReal) }
  let reindexEquiv : ℓ^p(ι, ℝ) ≃ₗᵢ[ℝ] ℓ^p(κ, ℝ) :=
    LinearIsometryEquiv.ofSurjective reindex fun g => by
      let f : ℓ^p(ι, ℝ) :=
        ⟨fun i => g (e.symm i), (memℓp_comp_equiv e.symm g).2 (lp.memℓp g)⟩
      exact ⟨f, by
        apply lp.ext
        funext j
        change g (e.symm (e j)) = g j
        rw [e.symm_apply_apply]⟩
  exact
    { toLinearIsometryEquiv := reindexEquiv
      map_sup' := fun _ _ => rfl
      map_inf' := fun _ _ => rfl }

/-- Reindexing an `ℓ^p` family evaluates by composing with the inverse
equivalence. -/
@[simp]
lemma lpCongr_apply
    (e : κ ≃ ι) (f : ℓ^p(ι, ℝ)) (j : κ) :
    lpCongr e f j = f (e j) := by
  rfl

end MeasureTheory.Lp
