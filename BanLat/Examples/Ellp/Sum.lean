/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Normed
import BanLat.Operators.Hom
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# `ℓᵖ`-sums of Banach lattices

For an arbitrary index type `ι` and exponent `1 ≤ p ≤ ∞`, this file equips
Mathlib's `ℓᵖ`-sum `lp X p` with its natural pointwise order and lattice
operations. It proves that if each factor `X i` is a Banach lattice, then so
is their `ℓᵖ`-sum.

In particular, with the `lp` scope open, `ℓ^p(ι, ℝ)` becomes the specialization
of `lp X p` to the constant family `X i = ℝ`.

The file also constructs canonical Banach lattice isometries for
* coordinatewise isometries,
* equivalences of index types,
and shows that, as Banach lattices,
* `ℓᵖ({a}, X) ≃ X`,
* `ℓᵖ(ι, ℓᵖ(κᵢ, Xᵢⱼ)) ≃ ℓᵖ((Σ i : ι, κᵢ), Xᵢⱼ)`.
-/

open scoped ENNReal BigOperators

/-! ### `ℓᵖ` sums

For an **arbitrary index set** `ι` and `1 ≤ p ≤ ∞`, the `ℓᵖ`-sum of a family of normed
vector lattices is again a normed vector lattice, and Banachness is preserved.
The order structure is pointwise; only the norm depends on `p`.
-/

namespace lp

variable {ι : Type*} {X : ι → Type*} {p : ENNReal} [Fact (1 ≤ p)]

section Add

variable {J : Type*} [∀ i, NormedAddCommGroup (X i)]

end Add

section Order

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

/-- Pointwise `≤` on an `ℓᵖ`-sum. -/
instance instLE : LE (lp X p) where
  le f g := ∀ i, f i ≤ g i

/-- Pointwise `<` on an `ℓᵖ`-sum. -/
instance instLT : LT (lp X p) where
  lt f g := (fun i => f i) < fun i => g i

omit [Fact (1 ≤ p)] [∀ i, IsOrderedAddMonoid (X i)] in
/-- The order on an `ℓᵖ`-sum is pointwise. -/
theorem le_def {f g : lp X p} : f ≤ g ↔ ∀ i, f i ≤ g i :=
  Iff.rfl

omit [Fact (1 ≤ p)] [∀ i, IsOrderedAddMonoid (X i)] in
/-- Strict inequality in an `ℓᵖ`-sum means pointwise inequality, strict in some coordinate. -/
theorem lt_def {f g : lp X p} : f < g ↔ f ≤ g ∧ ∃ i, f i < g i :=
  Pi.lt_def

/-- Pointwise `⊔` on an `ℓᵖ`-sum. -/
instance instMax [∀ i, HasSolidNorm (X i)] : Max (lp X p) where
  max f g := ⟨fun i => f i ⊔ g i,
    ((lp.memℓp f).norm.add (lp.memℓp g).norm).mono
      (fun i => norm_sup_le_add (f i) (g i))⟩

/-- Pointwise `⊓` on an `ℓᵖ`-sum. -/
instance instMin [∀ i, HasSolidNorm (X i)] : Min (lp X p) where
  min f g := ⟨fun i => f i ⊓ g i,
    ((lp.memℓp f).norm.add (lp.memℓp g).norm).mono
      (fun i => norm_inf_le_add (f i) (g i))⟩

omit [Fact (1 ≤ p)] in
/-- Coercion of a supremum in an `ℓᵖ`-sum to a function. -/
@[simp]
theorem coeFn_sup [∀ i, HasSolidNorm (X i)] (f g : lp X p) :
    ⇑(f ⊔ g) = fun i ↦ f i ⊔ g i :=
  rfl

omit [Fact (1 ≤ p)] in
/-- Coercion of an infimum in an `ℓᵖ`-sum to a function. -/
@[simp]
theorem coeFn_inf [∀ i, HasSolidNorm (X i)] (f g : lp X p) :
    ⇑(f ⊓ g) = fun i ↦ f i ⊓ g i :=
  rfl

/-- An `ℓᵖ`-sum carries the pointwise lattice structure. -/
instance instLattice [∀ i, HasSolidNorm (X i)] : Lattice (lp X p) :=
  Function.Injective.lattice (fun f : lp X p => fun i => f i) Subtype.val_injective
    Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Addition on an `ℓᵖ`-sum is monotone for the pointwise order. -/
instance instIsOrderedAddMonoid [∀ i, HasSolidNorm (X i)] : IsOrderedAddMonoid (lp X p) :=
  Function.Injective.isOrderedAddMonoid (fun f : lp X p => fun i => f i)
    (fun _ _ => rfl) Iff.rfl

omit [Fact (1 ≤ p)] in
/-- Coercion of an absolute value in an `ℓᵖ`-sum to a function. -/
@[simp]
theorem coeFn_abs [∀ i, HasSolidNorm (X i)] (f : lp X p) :
    ⇑|f| = fun i ↦ |f i| :=
  rfl

omit [Fact (1 ≤ p)] in
/-- Coercion of a positive part in an `ℓᵖ`-sum to a function. -/
@[simp]
theorem coeFn_posPart [∀ i, HasSolidNorm (X i)] (f : lp X p) :
    ⇑f⁺ = fun i ↦ (f i)⁺ :=
  rfl

omit [Fact (1 ≤ p)] in
/-- Coercion of a negative part in an `ℓᵖ`-sum to a function. -/
@[simp]
theorem coeFn_negPart [∀ i, HasSolidNorm (X i)] (f : lp X p) :
    ⇑f⁻ = fun i ↦ (f i)⁻ :=
  rfl

/-- The `ℓᵖ` norm is solid: `|x| ≤ |y|` implies `‖x‖ ≤ ‖y‖`. -/
instance instHasSolidNorm [∀ i, HasSolidNorm (X i)] : HasSolidNorm (lp X p) where
  solid := fun _ _ h => lp.norm_mono
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    (fun i => norm_le_norm_of_abs_le_abs (h i))

end Order

/-! #### Vector and Banach lattice structure -/

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

/-- Multiplication by nonnegative real scalars is monotone on an `ℓᵖ`-sum. -/
instance instPosSMulMono [∀ i, NormedVectorLattice (X i)] :
    PosSMulMono ℝ (lp X p) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h i
    exact smul_le_smul_of_nonneg_left (h i) ha

/-- The `ℓᵖ`-sum of normed vector lattices is a vector lattice. -/
noncomputable instance instVectorLattice [∀ i, NormedVectorLattice (X i)] :
    VectorLattice (lp X p) := ⟨⟩

/-- The `ℓᵖ`-sum of normed vector lattices is a normed vector lattice. -/
noncomputable instance instNormedVectorLattice [∀ i, NormedVectorLattice (X i)] :
    NormedVectorLattice (lp X p) where

/-- The `ℓᵖ`-sum of Banach lattices is a Banach lattice. -/
noncomputable instance instBanachLattice [∀ i, BanachLattice (X i)] :
    BanachLattice (lp X p) where

end lp

/-! ### Real `ℓᵖ` spaces -/

namespace lp

variable {ι : Type*} {p : ENNReal}

-- The real sequence-space instance is obtained by specializing the generic
-- Banach lattice instance for `ℓᵖ`-sums.
noncomputable example [Fact (1 ≤ p)] : BanachLattice (ℓ^p(ι, ℝ)) := inferInstance

end lp

/-! ### Banach lattice isometries between `ℓᵖ`-sums -/

namespace BanachLatEquiv

variable {ι : Type*} {p : ENNReal} [Fact (1 ≤ p)]

/-- Let `1 ≤ p < ∞`. Then `p.toReal` is strictly positive. -/
private lemma toReal_pos_of_ne_top (hp_top : p ≠ ∞) : 0 < p.toReal := by
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp_top

section PUnit

variable {X : Type*} [NormedAddCommGroup X]

/-- The norm of an element of a singleton-indexed `ℓᵖ`-sum is the norm of its
unique coordinate. -/
private lemma norm_punit (f : lp (fun _ : PUnit => X) p) :
    ‖f PUnit.unit‖ = ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [lp.norm_eq_ciSup]
    simp
  · have hp := toReal_pos_of_ne_top hp_top
    rw [lp.norm_eq_tsum_rpow hp]
    rw [tsum_eq_single PUnit.unit (fun i hi => (hi (Subsingleton.elim _ _)).elim)]
    rw [one_div]
    exact (Real.rpow_rpow_inv (norm_nonneg _) hp.ne').symm

variable [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X]

/-- The singleton-indexed `ℓᵖ`-sum of a Banach lattice is lattice
isometric to the Banach lattice itself. -/
def lpPUnit :
    BanachLatEquiv (lp (fun _ : PUnit => X) p) X := by
  let e : lp (fun _ : PUnit => X) p ≃ₗᵢ[ℝ] X :=
    { toFun := fun f => f PUnit.unit
      invFun := fun x => ⟨fun _ => x, Memℓp.all _⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        cases i
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := norm_punit }
  exact BanachLatEquiv.mk e (fun _ _ => rfl) (fun _ _ => rfl)

/-- The singleton-indexed `ℓᵖ`-sum equivalence evaluates at the unique coordinate. -/
@[simp]
theorem lpPUnit_apply (f : lp (fun _ : PUnit => X) p) :
    lpPUnit f = f PUnit.unit := by
  rfl

/-- The inverse singleton-indexed `ℓᵖ`-sum equivalence is the constant function. -/
@[simp]
theorem lpPUnit_symm_apply (x : X) (i : PUnit) :
    (lpPUnit (p := p)).symm x i = x := by
  rfl

end PUnit

section CongrRight

omit [Fact (1 ≤ p)] in
/-- If two families have equal coordinate norms, then `ℓᵖ`-summability of the
first family implies `ℓᵖ`-summability of the second. -/
private lemma memℓp_of_norm_eq {X Y : ι → Type*}
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedAddCommGroup (Y i)]
    {f : ∀ i, X i} {g : ∀ i, Y i} (h : ∀ i, ‖g i‖ = ‖f i‖)
    (hf : Memℓp f p) : Memℓp g p := by
  exact hf.mono' fun i => le_of_eq (h i)

/-- If two elements of `ℓᵖ`-sums have equal coordinate norms, then they have
equal `ℓᵖ` norms. -/
private lemma lp_norm_eq_of_norm_eq {X Y : ι → Type*}
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedAddCommGroup (Y i)]
    (f : lp X p) (g : lp Y p) (h : ∀ i, ‖g i‖ = ‖f i‖) :
    ‖g‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    exact fun i => le_of_eq (h i)
  · apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    exact fun i => le_of_eq (h i).symm

variable {X Y : ι → Type*}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)] [∀ i, BanachLattice (X i)]
  [∀ i, NormedAddCommGroup (Y i)] [∀ i, Lattice (Y i)]
  [∀ i, IsOrderedAddMonoid (Y i)] [∀ i, BanachLattice (Y i)]

omit [Fact (1 ≤ p)] in
/-- Applying a Banach lattice isometry at each coordinate of an `ℓᵖ`-summable family
produces an `ℓᵖ`-summable family. -/
private lemma memℓp_congrRight (e : ∀ i, BanachLatEquiv (X i) (Y i))
    (f : lp X p) : Memℓp (fun i => e i (f i)) p := by
  exact memℓp_of_norm_eq
    (fun i => (e i).toLinearIsometryEquiv.norm_map (f i)) (lp.memℓp f)

/-- Applying a Banach lattice isometry at each coordinate preserves the `ℓᵖ` norm. -/
private lemma norm_congrRight (e : ∀ i, BanachLatEquiv (X i) (Y i))
    (f : lp X p) :
    ‖(⟨fun i => e i (f i), memℓp_congrRight e f⟩ : lp Y p)‖ = ‖f‖ := by
  exact lp_norm_eq_of_norm_eq f _
    (fun i => (e i).toLinearIsometryEquiv.norm_map (f i))

/-- Coordinatewise Banach lattice isometries induce a Banach lattice isometry
between the corresponding `ℓᵖ`-sums. -/
def lpCongrRight (e : ∀ i, BanachLatEquiv (X i) (Y i)) :
    BanachLatEquiv (lp X p) (lp Y p) := by
  let Φ (f : lp X p) : lp Y p :=
    ⟨fun i => e i (f i), memℓp_congrRight e f⟩
  let Ψ (g : lp Y p) : lp X p :=
    ⟨fun i => (e i).symm (g i), memℓp_congrRight (fun i => (e i).symm) g⟩
  let E : lp X p ≃ₗᵢ[ℝ] lp Y p :=
    { toFun := Φ
      invFun := Ψ
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        exact (e i).symm_apply_apply (f i)
      right_inv := by
        intro g
        apply Subtype.ext
        funext i
        exact (e i).apply_symm_apply (g i)
      map_add' := fun _ _ => by apply Subtype.ext; funext i; exact (e i).map_add _ _
      map_smul' := fun c _ => by apply Subtype.ext; funext i; exact (e i).map_smul c _
      norm_map' := norm_congrRight e }
  exact BanachLatEquiv.mk E
    (fun _ _ => by apply Subtype.ext; funext i; exact (e i).map_sup' _ _)
    (fun _ _ => by apply Subtype.ext; funext i; exact (e i).map_inf' _ _)

/-- A coordinatewise `ℓᵖ`-sum equivalence acts by the given equivalence at each coordinate. -/
@[simp]
theorem lpCongrRight_apply (e : ∀ i, BanachLatEquiv (X i) (Y i))
    (f : lp X p) (i : ι) :
    lpCongrRight e f i = e i (f i) := by
  rfl

/-- The inverse coordinatewise `ℓᵖ`-sum equivalence acts coordinatewise by the inverses. -/
@[simp]
theorem lpCongrRight_symm_apply (e : ∀ i, BanachLatEquiv (X i) (Y i))
    (f : lp Y p) (i : ι) :
    (lpCongrRight e).symm f i = (e i).symm (f i) := by
  rfl

end CongrRight

/-- A family is `ℓᵖ`-summable if and only if its reindexing along a bijection
`e : ι ≃ κ` is `ℓᵖ`-summable. -/
private lemma memℓp_reindex_iff {κ : Type*} {X : ι → Type*}
    [∀ i, NormedAddCommGroup (X i)] (e : ι ≃ κ) (f : ∀ i, X i) :
    Memℓp (Equiv.piCongrLeft' X e f) p ↔ Memℓp f p := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [memℓp_infty_iff, memℓp_infty_iff]
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨i, rfl⟩
      obtain ⟨k, rfl⟩ := e.symm.surjective i
      exact hC (Set.mem_range_self k)
    · rintro ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hC (Set.mem_range_self (e.symm k))
  · have hp := toReal_pos_of_ne_top hp_top
    rw [memℓp_gen_iff hp, memℓp_gen_iff hp]
    exact e.symm.summable_iff (f := fun i => ‖f i‖ ^ p.toReal)

section CongrLeft

variable {κ : Type*} {X : ι → Type*}
  [∀ i, NormedAddCommGroup (X i)]

/-- Reindexing an `ℓᵖ`-summable family from `ι` to `κ` along a bijection
`e : ι ≃ κ` preserves `ℓᵖ`-summability. -/
private lemma memℓp_congrLeft (e : ι ≃ κ) (f : lp X p) :
    Memℓp (Equiv.piCongrLeft' X e f) p := by
  exact (memℓp_reindex_iff e f).mpr (lp.memℓp f)

/-- Reindexing an `ℓᵖ`-summable family in `X (e.symm k)` back from `κ` to `ι`
along the inverse of `e : ι ≃ κ` preserves `ℓᵖ`-summability. -/
private lemma memℓp_congrLeft_symm (e : ι ≃ κ)
    (g : lp (fun k => X (e.symm k)) p) :
    Memℓp ((Equiv.piCongrLeft' X e).symm (fun k => g k)) p := by
  apply (memℓp_reindex_iff e
    ((Equiv.piCongrLeft' X e).symm (fun k => g k))).mp
  convert lp.memℓp g using 1
  exact (Equiv.piCongrLeft' X e).apply_symm_apply (fun k => g k)

/-- Reindexing an `ℓᵖ`-sum along a bijection `e : ι ≃ κ` preserves its norm. -/
private lemma lp_norm_reindex (e : ι ≃ κ) (f : lp X p) :
    ‖(⟨Equiv.piCongrLeft' X e f,
      (memℓp_reindex_iff e f).mpr (lp.memℓp f)⟩ :
      lp (fun k => X (e.symm k)) p)‖ = ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · apply le_antisymm
    · apply lp.norm_le_of_forall_le (norm_nonneg f)
      intro k
      exact lp.norm_apply_le_norm (by simp) f (e.symm k)
    · apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro i
      obtain ⟨k, rfl⟩ := e.symm.surjective i
      exact lp.norm_apply_le_norm (by simp)
        (⟨Equiv.piCongrLeft' X e f,
          (memℓp_reindex_iff e f).mpr (lp.memℓp f)⟩ :
          lp (fun k => X (e.symm k)) ∞) k
  · have hp := toReal_pos_of_ne_top hp_top
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖f i‖ ^ p.toReal)

/-- The reindexed element of the `ℓᵖ`-sum of `X (e.symm k)` has the same norm
as the original element of the `ℓᵖ`-sum of `X i`. -/
private lemma norm_congrLeft (e : ι ≃ κ) (f : lp X p) :
    ‖(⟨Equiv.piCongrLeft' X e f, memℓp_congrLeft e f⟩ :
      lp (fun k => X (e.symm k)) p)‖ = ‖f‖ := by
  exact lp_norm_reindex e f

variable [∀ i, Lattice (X i)] [∀ i, IsOrderedAddMonoid (X i)]
  [∀ i, BanachLattice (X i)]

/-- Reindexing a family along an equivalence of index types induces a
Banach lattice isometry of its `ℓᵖ`-sums. -/
def lpCongrLeft (e : ι ≃ κ) :
    BanachLatEquiv (lp X p) (lp (fun k => X (e.symm k)) p) := by
  let Φ (f : lp X p) : lp (fun k => X (e.symm k)) p :=
    ⟨Equiv.piCongrLeft' X e f, memℓp_congrLeft e f⟩
  let Ψ (g : lp (fun k => X (e.symm k)) p) : lp X p :=
    ⟨(Equiv.piCongrLeft' X e).symm (fun k => g k), memℓp_congrLeft_symm e g⟩
  let E : lp X p ≃ₗᵢ[ℝ] lp (fun k => X (e.symm k)) p :=
    { toFun := Φ
      invFun := Ψ
      left_inv := by
        intro f
        apply Subtype.ext
        exact (Equiv.piCongrLeft' X e).symm_apply_apply f
      right_inv := by
        intro g
        apply Subtype.ext
        exact (Equiv.piCongrLeft' X e).apply_symm_apply g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := norm_congrLeft e }
  exact BanachLatEquiv.mk E
    (fun _ _ => by apply Subtype.ext; rfl) (fun _ _ => by apply Subtype.ext; rfl)

/-- Reindexing an `ℓᵖ`-sum evaluates by composing with the inverse index equivalence. -/
@[simp]
theorem lpCongrLeft_apply (e : ι ≃ κ) (f : lp X p) (k : κ) :
    lpCongrLeft e f k = f (e.symm k) := by
  rfl

/-- The inverse reindexing equivalence recovers the value at the corresponding index. -/
@[simp]
theorem lpCongrLeft_symm_apply (e : ι ≃ κ)
    (g : lp (fun k => X (e.symm k)) p) (k : κ) :
    (lpCongrLeft e).symm g (e.symm k) = g k := by
  exact Equiv.piCongrLeft'_symm_apply_apply X e (fun k => g k) k

end CongrLeft

section Congr

variable {κ : Type*} {X : ι → Type*} {Y : κ → Type*}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)] [∀ i, BanachLattice (X i)]
  [∀ k, NormedAddCommGroup (Y k)] [∀ k, Lattice (Y k)]
  [∀ k, IsOrderedAddMonoid (Y k)] [∀ k, BanachLattice (Y k)]

/-- Reindexing a family and applying coordinatewise Banach lattice isometries
induces a Banach lattice isometry between the corresponding `ℓᵖ`-sums. -/
noncomputable def lpCongr (e : ι ≃ κ)
    (φ : ∀ k, BanachLatEquiv (X (e.symm k)) (Y k)) :
    BanachLatEquiv (lp X p) (lp Y p) :=
  (lpCongrLeft (p := p) e).trans (lpCongrRight φ)

/-- A combined reindexing and coordinatewise equivalence evaluates coordinatewise. -/
@[simp]
theorem lpCongr_apply (e : ι ≃ κ)
    (φ : ∀ k, BanachLatEquiv (X (e.symm k)) (Y k))
    (f : lp X p) (k : κ) :
    lpCongr e φ f k = φ k (f (e.symm k)) := by
  rfl

/-- The inverse combined equivalence applies the coordinatewise inverse and reindexes back. -/
@[simp]
theorem lpCongr_symm_apply (e : ι ≃ κ)
    (φ : ∀ k, BanachLatEquiv (X (e.symm k)) (Y k))
    (g : lp Y p) (k : κ) :
    (lpCongr e φ).symm g (e.symm k) = (φ k).symm (g k) := by
  change (lpCongrLeft e).symm ((lpCongrRight φ).symm g) (e.symm k) = _
  rw [lpCongrLeft_symm_apply]
  exact lpCongrRight_symm_apply φ g k

end Congr

section Sigma

variable {κ : ι → Type*} {X : (Σ i, κ i) → Type*}
  [∀ ij, NormedAddCommGroup (X ij)]

/-- Given an `ℓᵖ`-summable family `f i` on each fiber `κ i`, the flattened family
`(i, j) ↦ f i j` is `ℓᵖ`-summable if and only if the family `i ↦ f i` is
`ℓᵖ`-summable with respect to the `ℓᵖ` norms of the fibers. -/
private lemma memℓp_sigma_iff (f : ∀ i, lp (fun j => X ⟨i, j⟩) p) :
    Memℓp (fun ij : Σ i, κ i => f ij.1 ij.2) p ↔ Memℓp f p := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [memℓp_infty_iff, memℓp_infty_iff]
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨max C 0, ?_⟩
      rintro _ ⟨i, rfl⟩
      apply lp.norm_le_of_forall_le (le_max_right C 0)
      intro j
      exact (hC (Set.mem_range_self (⟨i, j⟩ : Σ i, κ i))).trans (le_max_left C 0)
    · rintro ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact (lp.norm_apply_le_norm (by simp) (f i) j).trans
        (hC (Set.mem_range_self i))
  · have hp := toReal_pos_of_ne_top hp_top
    rw [memℓp_gen_iff hp, memℓp_gen_iff hp]
    constructor
    · intro h
      have hs := (summable_sigma_of_nonneg (fun _ => by positivity)).mp h
      simpa only [← lp.norm_rpow_eq_tsum hp] using hs.2
    · intro h
      apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
      refine ⟨fun i => (lp.memℓp (f i)).summable hp, ?_⟩
      simpa only [lp.norm_rpow_eq_tsum hp] using h

/-- Flattening an iterated `ℓᵖ`-sum into the `ℓᵖ`-sum over all dependent pairs
`(i, j)` preserves its norm. -/
private lemma norm_sigma_flatten
    (f : lp (fun i => lp (fun j => X ⟨i, j⟩) p) p) :
    ‖(⟨fun ij : Σ i, κ i => f ij.1 ij.2,
      (memℓp_sigma_iff f).mpr (lp.memℓp f)⟩ : lp X p)‖ = ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · apply le_antisymm
    · apply lp.norm_le_of_forall_le (norm_nonneg f)
      rintro ⟨i, j⟩
      exact (lp.norm_apply_le_norm (by simp) (f i) j).trans
        (lp.norm_apply_le_norm (by simp) f i)
    · apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro i
      apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro j
      exact lp.norm_apply_le_norm (by simp)
        (⟨fun ij : Σ i, κ i => f ij.1 ij.2,
          (memℓp_sigma_iff f).mpr (lp.memℓp f)⟩ : lp X ∞) ⟨i, j⟩
  · have hp := toReal_pos_of_ne_top hp_top
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    rw [Summable.tsum_sigma ((lp.memℓp _).summable hp)]
    congr 1
    funext i
    exact (lp.norm_rpow_eq_tsum hp (f i)).symm

/-- Restricting an `ℓᵖ`-summable family on dependent pairs `(i, j)` to a fixed
fiber `κ i` gives an `ℓᵖ`-summable family. -/
private lemma memℓp_sigma_fiber (g : lp X p) (i : ι) :
    Memℓp (fun j => g ⟨i, j⟩) p := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [memℓp_infty_iff]
    rcases memℓp_infty_iff.mp (lp.memℓp g) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro y hy
    rcases hy with ⟨j, hj⟩
    rw [← hj]
    exact hC (Set.mem_range_self (⟨i, j⟩ : Σ i, κ i))
  · have hp := toReal_pos_of_ne_top hp_top
    apply memℓp_gen
    exact ((summable_sigma_of_nonneg (fun _ => by positivity)).mp
      ((lp.memℓp g).summable hp)).1 i

/-- Group an `ℓᵖ`-summable family on dependent pairs `(i, j)` by its first index,
obtaining an element of the iterated `ℓᵖ`-sum with coordinates `g ⟨i, j⟩`. -/
private def sigmaCurry (g : lp X p) :
    lp (fun i => lp (fun j => X ⟨i, j⟩) p) p := by
  let f : ∀ i, lp (fun j => X ⟨i, j⟩) p :=
    fun i => ⟨fun j => g ⟨i, j⟩, memℓp_sigma_fiber g i⟩
  exact ⟨f, (memℓp_sigma_iff f).mp (by simpa [f] using lp.memℓp g)⟩

variable [∀ ij, Lattice (X ij)] [∀ ij, IsOrderedAddMonoid (X ij)]
  [∀ ij, BanachLattice (X ij)]

/-- The iterated `ℓᵖ`-sum associated with a doubly indexed family
`X : (Σ i, κ i) → Type*` is lattice isometric to the `ℓᵖ`-sum over
all pairs `(i, j)` with `i : ι` and `j : κ i`. -/
def lpSigma :
    BanachLatEquiv (lp (fun i => lp (fun j => X ⟨i, j⟩) p) p) (lp X p) := by
  let Φ (f : lp (fun i => lp (fun j => X ⟨i, j⟩) p) p) : lp X p :=
    ⟨fun ij => f ij.1 ij.2, (memℓp_sigma_iff f).mpr (lp.memℓp f)⟩
  let E : lp (fun i => lp (fun j => X ⟨i, j⟩) p) p ≃ₗᵢ[ℝ] lp X p :=
    { toFun := Φ
      invFun := sigmaCurry
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        apply Subtype.ext
        rfl
      right_inv := by
        intro g
        apply Subtype.ext
        rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := norm_sigma_flatten }
  exact BanachLatEquiv.mk E
    (fun _ _ => by apply Subtype.ext; rfl) (fun _ _ => by apply Subtype.ext; rfl)

/-- Flattening an iterated `ℓᵖ`-sum evaluates at the corresponding pair. -/
@[simp]
theorem lpSigma_apply (f : lp (fun i => lp (fun j => X ⟨i, j⟩) p) p)
    (i : ι) (j : κ i) :
    lpSigma f ⟨i, j⟩ = f i j := by
  rfl

/-- The inverse flattening equivalence curries a function on dependent pairs. -/
@[simp]
theorem lpSigma_symm_apply (f : lp X p) (i : ι) (j : κ i) :
    (lpSigma (p := p)).symm f i j = f ⟨i, j⟩ := by
  rfl

end Sigma

end BanachLatEquiv
