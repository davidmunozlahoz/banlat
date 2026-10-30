/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Ellp.Sum
import BanLat.OrderUnit
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weak order units in `ℓᵖ`-sums of normed vector lattices

A vector in an `ℓᵖ`-sum is a weak order unit exactly when each coordinate is a
weak order unit. For `1 ≤ p < ∞`, such a vector exists exactly when the set of
nontrivial summands in the `ℓᵖ`-sum is countable and every summand has a weak
order unit.

The corresponding for `ℓᵖ(ι, ℝ)`-spaces are obtained as corollaries.
-/

open scoped ENNReal lp

/-! ### Weak order units -/

namespace lp

variable {ι : Type*} {X : ι → Type*} {p : ENNReal}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)] [∀ i, NormedVectorLattice (X i)]

/-- Let `e` be a weak order unit and let `0 < c`. Then `c • e` is a weak order unit. -/
private lemma weakOrderUnit_smul_pos {E : Type*} [NormedAddCommGroup E]
    [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E]
    {e : E} (he : WeakOrderUnit e) {c : ℝ} (hc : 0 < c) :
    WeakOrderUnit (c • e) := by
  refine ⟨smul_nonneg hc.le he.1, fun y hy ↦ he.2 y ?_⟩
  have h := hy.smul_right c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h

/-- If `x` is a weak order unit of an `ℓᵖ`-sum, then `x i` is a weak order unit
of the corresponding summand. -/
private lemma weakOrderUnit_apply {x : lp X p} (hx : WeakOrderUnit x) (i : ι) :
    WeakOrderUnit (x i) := by
  classical
  refine ⟨hx.1 i, fun y hy ↦ ?_⟩
  let g : lp X p := lp.single p i y
  have hgx : IsVLDisjoint g x := by
    apply lp.ext
    funext j
    change |g j| ⊓ |x j| = 0
    by_cases hji : j = i
    · subst j
      change |y| ⊓ |x i| = 0 at hy
      simpa [g] using hy
    · have hgj : g j = 0 := lp.single_apply_ne p i y hji
      simp [hgj]
  have hg := hx.2 g hgx
  have heval := congrArg (fun u : lp X p ↦ u i) hg
  simpa [g] using heval

/-- If every coordinate of `x` is a weak order unit of its summand, then `x` is
a weak order unit of the `ℓᵖ`-sum. -/
private lemma weakOrderUnit_of_forall {x : lp X p}
    (hx : ∀ i, WeakOrderUnit (x i)) : WeakOrderUnit x := by
  refine ⟨fun i ↦ (hx i).1, fun g hg ↦ ?_⟩
  apply lp.ext
  funext i
  apply (hx i).2 (g i)
  exact congrArg (fun u : lp X p ↦ u i) hg

/-- An element `x` of an `ℓᵖ`-sum is a weak order unit if and only if every
coordinate `x i` is a weak order unit of the corresponding summand. -/
theorem weakOrderUnit_iff_forall {x : lp X p} :
    WeakOrderUnit x ↔ ∀ i, WeakOrderUnit (x i) :=
  ⟨fun hx i ↦ weakOrderUnit_apply hx i, weakOrderUnit_of_forall⟩

variable [Fact (1 ≤ p)]

/-- Let `1 ≤ p < ∞`. If an `ℓᵖ`-sum has a weak order unit, then it has a
countable set of non-trivial summands. -/
private lemma countable_nontrivial_of_weakOrderUnit (hp : p ≠ ∞)
    {x : lp X p} (hx : WeakOrderUnit x) :
    Set.Countable {i | Nontrivial (X i)} := by
  classical
  have hx_coord := weakOrderUnit_iff_forall.mp hx
  have hpR : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
  have hsum := (lp.memℓp x).summable hpR
  have hsupp : Function.support (fun i ↦ ‖x i‖ ^ p.toReal) =
      {i | Nontrivial (X i)} := by
    ext i
    simp only [Function.mem_support, Set.mem_ofPred_eq]
    constructor
    · intro hi
      have hxi : x i ≠ 0 := by
        intro hxi
        apply hi
        simp [hxi, Real.zero_rpow hpR.ne']
      exact ⟨⟨x i, 0, hxi⟩⟩
    · intro hi
      let : Nontrivial (X i) := hi
      have hxi : x i ≠ 0 := by
        intro hxi
        obtain ⟨y, hy⟩ := exists_ne (0 : X i)
        apply hy
        apply (hx_coord i).2 y
        rw [hxi]
        exact isVLDisjoint_zero_right y
      exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr hxi) _).ne'
  have hcount := hsum.countable_support
  rwa [hsupp] at hcount

/-- Let `1 ≤ p < ∞`. If an `ℓᵖ`-sum has a countable set of non-trivial summands
and every summand has a weak order unit, then the sum has a weak order unit. -/
private lemma exists_weakOrderUnit_of_countable (hp : p ≠ ∞)
    (hι : Set.Countable {i | Nontrivial (X i)})
    (hcoord : ∀ i, ∃ e : X i, WeakOrderUnit e) :
    ∃ x : lp X p, WeakOrderUnit x := by
  classical
  let S : Set ι := {i | Nontrivial (X i)}
  let : Countable S := hι.to_subtype
  choose e he using hcoord
  obtain ⟨g, hgpos, c, hgsum, -⟩ :=
    NNReal.exists_pos_sum_of_countable (ε := 1) one_ne_zero S
  let w : ι → NNReal := fun i ↦ if hi : Nontrivial (X i) then g ⟨i, hi⟩ else 0
  have hw_sum : Summable fun i ↦ (w i : ℝ) := by
    have hg_sum : Summable fun j ↦ (g j : ℝ) := NNReal.summable_coe.mpr hgsum.summable
    have hrestrict : Summable ((fun i ↦ (w i : ℝ)) ∘ fun j : S ↦ j.1) := by
      convert hg_sum using 1
      funext j
      have hj := j.property
      change Nontrivial (X j.1) at hj
      simp [w, hj]
    have hindicator := (summable_subtype_iff_indicator (s := S)).mp hrestrict
    convert hindicator using 1
    funext i
    by_cases hi : Nontrivial (X i)
    · simp [S, w, hi]
    · simp [S, w, hi]
  let r : ℝ := 1 / p.toReal
  let x₀ : ∀ i, X i := fun i ↦ if hi : Nontrivial (X i) then
    ((w i ^ r : NNReal) : ℝ) • (‖e i‖⁻¹ • e i) else e i
  have hxmem : Memℓp x₀ p := by
    have hpR : 0 < p.toReal :=
      ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
    rw [memℓp_gen_iff hpR]
    convert hw_sum using 1
    funext i
    by_cases hi : Nontrivial (X i)
    · let : Nontrivial (X i) := hi
      have he_ne : e i ≠ 0 := by
        intro hei
        obtain ⟨y, hy⟩ := exists_ne (0 : X i)
        apply hy
        apply (he i).2 y
        rw [hei]
        exact isVLDisjoint_zero_right y
      have he_norm_pos : 0 < ‖e i‖ := norm_pos_iff.mpr he_ne
      have hu_norm : ‖‖e i‖⁻¹ • e i‖ = 1 := by
        rw [norm_smul]
        simp [he_norm_pos.ne']
      rw [show x₀ i = ((w i ^ r : NNReal) : ℝ) • (‖e i‖⁻¹ • e i) by simp [x₀, hi],
        norm_smul, hu_norm, mul_one, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      simp only [NNReal.coe_rpow]
      rw [← Real.rpow_mul (NNReal.coe_nonneg _)]
      simp [r, hpR.ne']
    · have : Subsingleton (X i) := not_nontrivial_iff_subsingleton.mp hi
      simpa [x₀, w, hi, Subsingleton.elim (e i) 0] using Real.zero_rpow hpR.ne'
  let x : lp X p := ⟨x₀, hxmem⟩
  refine ⟨x, weakOrderUnit_iff_forall.mpr ?_⟩
  intro i
  change WeakOrderUnit (x₀ i)
  by_cases hi : Nontrivial (X i)
  · let : Nontrivial (X i) := hi
    have he_ne : e i ≠ 0 := by
      intro hei
      obtain ⟨y, hy⟩ := exists_ne (0 : X i)
      apply hy
      apply (he i).2 y
      rw [hei]
      exact isVLDisjoint_zero_right y
    rw [show x₀ i = ((w i ^ r : NNReal) : ℝ) • (‖e i‖⁻¹ • e i) by simp [x₀, hi]]
    apply weakOrderUnit_smul_pos
    · exact weakOrderUnit_smul_pos (he i) (inv_pos.mpr (norm_pos_iff.mpr he_ne))
    · exact_mod_cast NNReal.rpow_pos (by simpa [w, hi] using hgpos ⟨i, hi⟩)
  · simp [x₀, hi, he i]

/-- Let `1 ≤ p < ∞`. An `ℓᵖ`-sum has a weak order unit if and only if it has a
countable set of non-trivial summands and every summand has a weak order unit. -/
theorem exists_weakOrderUnit_iff (hp : p ≠ ∞) :
    (∃ x : lp X p, WeakOrderUnit x) ↔
      Set.Countable {i | Nontrivial (X i)} ∧ ∀ i, ∃ e : X i, WeakOrderUnit e := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨countable_nontrivial_of_weakOrderUnit hp hx,
      fun i ↦ ⟨x i, weakOrderUnit_apply hx i⟩⟩
  · rintro ⟨hι, hcoord⟩
    exact exists_weakOrderUnit_of_countable hp hι hcoord

end lp

/-! ### Real `ℓᵖ` spaces -/

namespace lp

variable {ι : Type*} {p : ENNReal}

/-- `x ∈ ℓ^p(ι, ℝ)` is a weak order unit iff `∀ i ∈ ι, x i > 0`. -/
theorem weakOrderUnit_iff_forall_pos {x : ℓ^p(ι, ℝ)} :
    WeakOrderUnit x ↔ ∀ i, 0 < x i := by
  rw [weakOrderUnit_iff_forall]
  apply forall_congr'
  intro i
  constructor
  · intro hx
    refine lt_of_le_of_ne hx.1 fun h ↦ ?_
    have := hx.2 1 (by simp [IsVLDisjoint, h.symm])
    norm_num at this
  · intro hx
    refine ⟨hx.le, fun y hy ↦ ?_⟩
    change min |y| |x i| = 0 at hy
    rw [abs_of_pos hx] at hy
    by_cases hle : |y| ≤ x i
    · rw [min_eq_left hle] at hy
      exact abs_eq_zero.mp hy
    · rw [min_eq_right (le_of_not_ge hle)] at hy
      exact ((ne_of_gt hx) hy).elim

variable [Fact (1 ≤ p)]

/-- Let `1 ≤ p < ∞`. Then `ℓ^p(ι, ℝ)` has a weak order unit if and only if `ι`
is countable. -/
theorem nonempty_weakOrderUnit_iff_countable (hp : p ≠ ∞) :
    (∃ x : ℓ^p(ι, ℝ), WeakOrderUnit x) ↔ Countable ι := by
  rw [exists_weakOrderUnit_iff hp]
  have hset : {i : ι | Nontrivial ℝ} = Set.univ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    infer_instance
  rw [hset, Set.countable_univ_iff]
  constructor
  · exact And.left
  · intro hι
    refine ⟨hι, fun _ ↦ ⟨1, zero_le_one, fun y hy ↦ ?_⟩⟩
    change min |y| |(1 : ℝ)| = 0 at hy
    rw [abs_one] at hy
    by_cases hle : |y| ≤ 1
    · rw [min_eq_left hle] at hy
      exact abs_eq_zero.mp hy
    · rw [min_eq_right (le_of_not_ge hle)] at hy
      norm_num at hy

end lp
