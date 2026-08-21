import BanLat.Normed
import BanLat.Operators.Hom
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# `ℓ^p` spaces as Banach lattices

For every index set `ι` and `1 ≤ p ≤ ∞`, the space `ℓ^p(ι, ℝ)` is a
Banach lattice under the coordinate-wise order and the usual `ℓ^p` norm.

Equivalences of index types induce lattice isometries between the
corresponding `ℓ^p` spaces.
-/

open scoped ENNReal lp

noncomputable section

namespace lp

variable {ι : Type*} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Lattice and order structure -/

private instance instLEReal : LE (ℓ^p(ι, ℝ)) where
  le f g := (f : ι → ℝ) ≤ (g : ι → ℝ)

private instance instLTReal : LT (ℓ^p(ι, ℝ)) where
  lt f g := (f : ι → ℝ) < (g : ι → ℝ)

private noncomputable instance instMaxReal : Max (ℓ^p(ι, ℝ)) where
  max f g :=
    ⟨fun i => max (f i) (g i),
      (lp.memℓp f).norm.add (lp.memℓp g).norm |>.mono' fun i => by
        rcases le_total (f i) (g i) with h | h
        · rw [max_eq_right h]
          simp only [Pi.add_apply, Real.norm_eq_abs]
          exact (le_add_of_nonneg_left (abs_nonneg (f i))).trans_eq
            (abs_of_nonneg (add_nonneg (abs_nonneg (f i)) (abs_nonneg (g i)))).symm
        · rw [max_eq_left h]
          simp only [Pi.add_apply, Real.norm_eq_abs]
          exact (le_add_of_nonneg_right (abs_nonneg (g i))).trans_eq
            (abs_of_nonneg (add_nonneg (abs_nonneg (f i)) (abs_nonneg (g i)))).symm⟩

private noncomputable instance instMinReal : Min (ℓ^p(ι, ℝ)) where
  min f g :=
    ⟨fun i => min (f i) (g i),
      (lp.memℓp f).norm.add (lp.memℓp g).norm |>.mono' fun i => by
        rcases le_total (f i) (g i) with h | h
        · rw [min_eq_left h]
          simp only [Pi.add_apply, Real.norm_eq_abs]
          exact (le_add_of_nonneg_right (abs_nonneg (g i))).trans_eq
            (abs_of_nonneg (add_nonneg (abs_nonneg (f i)) (abs_nonneg (g i)))).symm
        · rw [min_eq_right h]
          simp only [Pi.add_apply, Real.norm_eq_abs]
          exact (le_add_of_nonneg_left (abs_nonneg (f i))).trans_eq
            (abs_of_nonneg (add_nonneg (abs_nonneg (f i)) (abs_nonneg (g i)))).symm⟩

/-- The space `ℓ^p(ι, ℝ)` is a lattice under the pointwise order. -/
noncomputable instance instLatticeReal :
    Lattice (ℓ^p(ι, ℝ)) :=
  Function.Injective.lattice (β := ι → ℝ) ((↑) : ℓ^p(ι, ℝ) → ι → ℝ)
    Subtype.val_injective Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Addition on `ℓ^p(ι, ℝ)` is monotone for the pointwise order. -/
instance instIsOrderedAddMonoidReal :
    IsOrderedAddMonoid (ℓ^p(ι, ℝ)) :=
  Function.Injective.isOrderedAddMonoid (β := ℓ^p(ι, ℝ)) (α := ι → ℝ)
    ((↑) : ℓ^p(ι, ℝ) → ι → ℝ) (fun _ _ => rfl) Iff.rfl

/-! ### Vector lattice -/

/-- The pointwise order makes `ℓ^p(ι, ℝ)` a vector lattice. -/
noncomputable instance instVectorLatticeReal : VectorLattice (ℓ^p(ι, ℝ)) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h i
    exact mul_le_mul_of_nonneg_left (h i) ha

/-! ### Normed vector lattice -/

/-- The `ℓ^p` norm is solid for every `1 ≤ p ≤ ∞`. -/
noncomputable instance instNormedVectorLatticeReal :
    NormedVectorLattice (ℓ^p(ι, ℝ)) where
  solid := fun f g h => by
    have hpt : ∀ i, ‖f i‖ ≤ ‖g i‖ := fun i =>
      HasSolidNorm.solid (α := ℝ) (h i)
    rcases eq_or_ne p ∞ with hp | hp
    · subst hp
      simp only [lp.norm_eq_ciSup]
      exact ciSup_mono (lp.memℓp g).bddAbove hpt
    · have hpos : 0 < p.toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) Fact.out, hp.lt_top⟩
      simp only [lp.norm_eq_tsum_rpow hpos]
      gcongr
      · exact (lp.memℓp f).summable hpos
      · exact (lp.memℓp g).summable hpos
      · exact hpt _

/-! ### Banach lattice -/

/-- For `1 ≤ p ≤ ∞`, the pointwise order and the `ℓ^p` norm make
`ℓ^p(ι, ℝ)` a Banach lattice. -/
noncomputable instance instBanachLatticeReal :
    BanachLattice (ℓ^p(ι, ℝ)) where

end lp

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
