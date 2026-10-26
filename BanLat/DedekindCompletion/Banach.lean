/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.ExistenceUniqueness
import BanLat.Normed
import Mathlib.Analysis.Normed.Group.Completeness

/-!
# Banach lattice norm on a Dedekind completion

We equip the Dedekind completion of a Banach lattice with a complete lattice norm which makes the
canonical inclusion an isometric embedding.
-/

noncomputable section

open Set Filter
open scoped BigOperators

namespace DedekindCompletion

universe u

variable {X : Type u} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- Norms of positive elements whose images dominate the modulus of `y`. -/
private def majorantNorms (D : DedekindCompletion X) (y : D.carrier) : Set ℝ :=
  {r | ∃ x : X, 0 ≤ x ∧ |y| ≤ D.inclusion x ∧ ‖x‖ = r}

/-- The infimum of the norms of positive original-space majorants of `|y|`. -/
def upperNorm (D : DedekindCompletion X) (y : D.carrier) : ℝ :=
  sInf (majorantNorms D y)

/-- Every completion element has a positive majorant from the original lattice. -/
private lemma majorantNorms_nonempty (D : DedekindCompletion X) (y : D.carrier) :
    (majorantNorms D y).Nonempty := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := D.majorizing |y|
  exact ⟨‖x⁺‖, x⁺, posPart_nonneg x,
    hx.trans (D.inclusion.monotone le_sup_left), rfl⟩

/-- Norms of positive majorants are bounded below by zero. -/
private lemma majorantNorms_bddBelow (D : DedekindCompletion X) (y : D.carrier) :
    BddBelow (majorantNorms D y) :=
  ⟨0, by rintro r ⟨x, _, _, rfl⟩; exact norm_nonneg x⟩

/-- The upper norm is bounded by the norm of any positive majorant. -/
private lemma upperNorm_le (D : DedekindCompletion X) {y : D.carrier} {x : X}
    (hx : 0 ≤ x) (hy : |y| ≤ D.inclusion x) : upperNorm D y ≤ ‖x‖ :=
  csInf_le (majorantNorms_bddBelow D y) ⟨x, hx, hy, rfl⟩

/-- A lower bound for all majorant norms bounds the upper norm. -/
private lemma le_upperNorm (D : DedekindCompletion X) {y : D.carrier} {r : ℝ}
    (h : ∀ x : X, 0 ≤ x → |y| ≤ D.inclusion x → r ≤ ‖x‖) :
    r ≤ upperNorm D y := by
  apply le_csInf (majorantNorms_nonempty D y)
  rintro s ⟨x, hx, hy, rfl⟩
  exact h x hx hy

/-- The upper norm is nonnegative. -/
private lemma upperNorm_nonneg (D : DedekindCompletion X) (y : D.carrier) :
    0 ≤ upperNorm D y :=
  le_upperNorm D (fun x _ _ => norm_nonneg x)

/-- A positive original-space element below `|y|` has norm at most the upper norm of `y`. -/
private lemma norm_le_upperNorm (D : DedekindCompletion X) {y : D.carrier} {x : X}
    (hx : 0 ≤ x) (hy : D.inclusion x ≤ |y|) : ‖x‖ ≤ upperNorm D y := by
  apply le_upperNorm D
  intro z hz hyz
  apply HasSolidNorm.solid
  rw [abs_of_nonneg hx, abs_of_nonneg hz]
  exact D.inclusion.le_of_map_le D.injective (hy.trans hyz)

/-- The upper norm agrees with the original norm on embedded elements. -/
theorem upperNorm_inclusion (D : DedekindCompletion X) (x : X) :
    upperNorm D (D.inclusion x) = ‖x‖ := by
  apply le_antisymm
  · simpa only [norm_abs_eq_norm] using
      upperNorm_le D (abs_nonneg x) ((D.inclusion.map_abs x).symm.le)
  · have h := norm_le_upperNorm D (abs_nonneg x) (y := D.inclusion x)
      (D.inclusion.map_abs x).le
    simpa only [norm_abs_eq_norm] using h

/-- The upper norm is monotone with respect to domination of absolute values. -/
private lemma upperNorm_solid (D : DedekindCompletion X) {y z : D.carrier}
    (hyz : |y| ≤ |z|) : upperNorm D y ≤ upperNorm D z := by
  apply le_upperNorm D
  intro x hx hzx
  exact upperNorm_le D hx (hyz.trans hzx)

/-- Reflection leaves the upper norm unchanged. -/
private lemma upperNorm_neg (D : DedekindCompletion X) (y : D.carrier) :
    upperNorm D (-y) = upperNorm D y := by
  apply le_antisymm <;> apply upperNorm_solid D <;> simp only [abs_neg, le_refl]

/-- The upper norm of zero is zero. -/
private lemma upperNorm_zero (D : DedekindCompletion X) : upperNorm D 0 = 0 := by
  have h := upperNorm_inclusion D 0
  simpa only [map_zero, norm_zero] using h

/-- Order density makes the upper norm strictly positive on nonzero elements. -/
private lemma upperNorm_eq_zero (D : DedekindCompletion X) {y : D.carrier}
    (hy : upperNorm D y = 0) : y = 0 := by
  by_contra hne
  have hpos : 0 < |y| := lt_of_le_of_ne (abs_nonneg y) (by
    intro h
    exact hne ((abs_eq_zero_iff_zero y).mp h.symm))
  obtain ⟨_, ⟨x, rfl⟩, hxpos, hxy⟩ := D.dense hpos
  have hx0 : 0 ≤ x := D.inclusion.le_of_map_le D.injective (by
    rw [map_zero]
    exact hxpos.le)
  have hnorm := norm_le_upperNorm D hx0 hxy
  rw [hy] at hnorm
  have hxz : x = 0 := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg x))
  have hz : D.inclusion x = 0 := by rw [hxz]; exact map_zero D.inclusion
  exact hxpos.ne' hz

/-- The upper norm satisfies the triangle inequality. -/
private lemma upperNorm_add (D : DedekindCompletion X) (y z : D.carrier) :
    upperNorm D (y + z) ≤ upperNorm D y + upperNorm D z := by
  have hp {a b : X} (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hya : |y| ≤ D.inclusion a) (hzb : |z| ≤ D.inclusion b) :
      upperNorm D (y + z) ≤ ‖a‖ + ‖b‖ := by
    apply (upperNorm_le D (add_nonneg ha hb) _).trans (norm_add_le a b)
    calc
      |y + z| ≤ |y| + |z| := abs_add_le y z
      _ ≤ D.inclusion a + D.inclusion b := add_le_add hya hzb
      _ = D.inclusion (a + b) := (map_add D.inclusion a b).symm
  have hi {a : X} (ha : 0 ≤ a) (hya : |y| ≤ D.inclusion a) :
      upperNorm D (y + z) ≤ ‖a‖ + upperNorm D z := by
    have h := le_upperNorm D (y := z) (r := upperNorm D (y + z) - ‖a‖)
      (fun b hb hzb => sub_le_iff_le_add.mpr (by
        simpa only [add_comm] using hp ha hb hya hzb))
    linarith
  have h := le_upperNorm D (y := y)
    (r := upperNorm D (y + z) - upperNorm D z)
    (fun a ha hya => sub_le_iff_le_add.mpr (hi ha hya))
  linarith

/-- Positive scalar multiplication bounds the upper norm by the scaled norm. -/
private lemma upperNorm_scale_le (D : DedekindCompletion X) (r : ℝ) (hr : 0 < r)
    (y : D.carrier) : upperNorm D (r • y) ≤ r * upperNorm D y := by
  have hdiv : upperNorm D (r • y) / r ≤ upperNorm D y := by
    apply le_upperNorm D
    intro x hx hyx
    apply (div_le_iff₀ hr).mpr
    have hbound : upperNorm D (r • y) ≤ ‖r • x‖ := by
      apply upperNorm_le D (smul_nonneg hr.le hx)
      calc
        |r • y| = r • |y| := by rw [abs_smul', abs_of_pos hr]
        _ ≤ r • D.inclusion x := smul_le_smul_of_nonneg_left hyx hr.le
        _ = D.inclusion (r • x) := (map_smul D.inclusion r x).symm
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_comm] using hbound
  simpa only [mul_comm] using (div_le_iff₀ hr).mp hdiv

/-- Positive scalar multiplication scales the upper norm exactly. -/
private lemma upperNorm_smul_pos (D : DedekindCompletion X) (r : ℝ) (hr : 0 < r)
    (y : D.carrier) : upperNorm D (r • y) = r * upperNorm D y := by
  apply le_antisymm (upperNorm_scale_le D r hr y)
  have h := upperNorm_scale_le D r⁻¹ (inv_pos.mpr hr) (r • y)
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h
  have hm := mul_le_mul_of_nonneg_left h hr.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hm

/-- Real scalar multiplication scales the upper norm by the scalar absolute value. -/
private lemma upperNorm_smul (D : DedekindCompletion X) (r : ℝ) (y : D.carrier) :
    upperNorm D (r • y) = |r| * upperNorm D y := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have heq : r • y = (-r) • (-y) := by rw [smul_neg, neg_smul, neg_neg]
    rw [heq, upperNorm_smul_pos D (-r) (neg_pos.mpr hr),
      upperNorm_neg, abs_of_neg hr]
  · subst r
    simp only [zero_smul, upperNorm_zero, abs_zero, zero_mul]
  · rw [upperNorm_smul_pos D r hr, abs_of_pos hr]

/-- The proposed norm on the carrier of a Dedekind completion. -/
local instance upperNormInst (D : DedekindCompletion X) : Norm D.carrier := ⟨upperNorm D⟩

/-- The normed-space core induced by positive majorants. -/
private theorem normCore (D : DedekindCompletion X) : NormedSpace.Core ℝ D.carrier where
  norm_nonneg := upperNorm_nonneg D
  norm_eq_zero_iff := fun y => ⟨upperNorm_eq_zero D, fun h => h ▸ upperNorm_zero D⟩
  norm_smul := by
    intro r y
    change upperNorm D (r • y) = |r| * upperNorm D y
    exact upperNorm_smul D r y
  norm_triangle := upperNorm_add D

/-- The normed additive group induced by the upper norm. -/
local instance normedGroup (D : DedekindCompletion X) : NormedAddCommGroup D.carrier :=
  NormedAddCommGroup.ofCore (normCore D)

/-- The normed real vector-space structure induced by the upper norm. -/
local instance normedSpace (D : DedekindCompletion X) : NormedSpace ℝ D.carrier :=
  NormedSpace.ofCore (normCore D)

/-- The upper norm respects domination of absolute values. -/
local instance solidNorm (D : DedekindCompletion X) : HasSolidNorm D.carrier :=
  ⟨fun _ _ h => upperNorm_solid D h⟩

/-- The completion carries the induced normed vector-lattice structure. -/
local instance normedLattice (D : DedekindCompletion X) : NormedVectorLattice D.carrier := {}

/-- The norm of a completion element is the infimum of the norms of its positive majorants. -/
theorem norm_eq_sInf_majorants (D : DedekindCompletion X) (y : D.carrier) :
    ‖y‖ = sInf {r : ℝ | ∃ x : X, |y| ≤ D.inclusion x ∧ ‖x‖ = r} := by
  change sInf (majorantNorms D y) = sInf _
  congr 1
  ext r
  constructor
  · rintro ⟨x, _, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, hx, rfl⟩
    apply D.inclusion.le_of_map_le D.injective
    simpa only [map_zero] using (abs_nonneg y).trans hx

/-- Positive majorants can be chosen with norm arbitrarily close to the upper norm. -/
private lemma exists_majorant (D : DedekindCompletion X) (y : D.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, 0 ≤ x ∧ |y| ≤ D.inclusion x ∧ ‖x‖ ≤ upperNorm D y + ε := by
  obtain ⟨r, ⟨x, hx, hy, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (majorantNorms_nonempty D y) (lt_add_of_pos_right (upperNorm D y) hε)
  exact ⟨x, hx, hy, hr.le⟩

/-- Positive absolutely summable series converge in the upper norm. -/
private lemma positive_series (D : DedekindCompletion X) (v : ℕ → D.carrier)
    (hv : ∀ n, 0 ≤ v n) (hs : Summable (fun n => ‖v n‖)) :
    ∃ s, Tendsto (fun n => ∑ i ∈ Finset.range n, v i) atTop (nhds s) := by
  have hchoose (n : ℕ) : ∃ x : X, 0 ≤ x ∧ |v n| ≤ D.inclusion x ∧
      ‖x‖ ≤ ‖v n‖ + (1 / 2 : ℝ) ^ n := by
    exact exists_majorant D (v n) (ε := (1 / 2 : ℝ) ^ n) (by positivity)
  choose x hx0 hxv hnx using hchoose
  have hsε : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsxnorm : Summable (fun n => ‖x n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnx (hs.add hsε)
  have hsx : Summable x := hsxnorm.of_norm
  let p (n : ℕ) : D.carrier := ∑ i ∈ Finset.range n, v i
  let q (n : ℕ) : X := ∑ i ∈ Finset.range n, x i
  let t : X := ∑' i, x i
  have hpmono : Monotone p := by
    intro n m hnm
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      (fun i _ _ => hv i)
  have hqle (n : ℕ) : q n ≤ t := hsx.sum_le_tsum _ (fun i _ => hx0 i)
  have hpq (n : ℕ) : p n ≤ D.inclusion (q n) := by
    calc
      p n ≤ ∑ i ∈ Finset.range n, D.inclusion (x i) :=
        Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hxv i))
      _ = D.inclusion (q n) := (map_sum D.inclusion.toLinearMap _ _).symm
  have hb : BddAbove (range p) := ⟨D.inclusion t, by
    rintro z ⟨n, rfl⟩
    exact (hpq n).trans (D.inclusion.monotone (hqle n))⟩
  let s : D.carrier := sSup (range p)
  have hsLUB : IsLUB (range p) s := isLUB_csSup (range_nonempty p) hb
  refine ⟨s, ?_⟩
  have hpartial {n m : ℕ} (hnm : n ≤ m) :
      p m - p n ≤ D.inclusion (q m - q n) := by
    have hpadd : p n + ∑ i ∈ Finset.Ico n m, v i = p m :=
      Finset.sum_range_add_sum_Ico v hnm
    have hqadd : q n + ∑ i ∈ Finset.Ico n m, x i = q m :=
      Finset.sum_range_add_sum_Ico x hnm
    calc
      p m - p n = ∑ i ∈ Finset.Ico n m, v i := by rw [← hpadd]; abel
      _ ≤ ∑ i ∈ Finset.Ico n m, D.inclusion (x i) :=
        Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hxv i))
      _ = D.inclusion (∑ i ∈ Finset.Ico n m, x i) :=
        (map_sum D.inclusion.toLinearMap _ _).symm
      _ = D.inclusion (q m - q n) := by congr 1; rw [← hqadd]; abel
  have hbound (n : ℕ) : s - p n ≤ D.inclusion (t - q n) := by
    apply sub_le_iff_le_add.mpr
    apply hsLUB.2
    rintro z ⟨m, rfl⟩
    by_cases hmn : m ≤ n
    · have ht0 : 0 ≤ D.inclusion (t - q n) :=
        D.inclusion.map_nonneg (sub_nonneg.mpr (hqle n))
      exact (hpmono hmn).trans (le_add_of_nonneg_left ht0)
    · have hnm : n ≤ m := le_of_not_ge hmn
      apply sub_le_iff_le_add.mp
      exact (hpartial hnm).trans (D.inclusion.monotone (sub_le_sub_right (hqle m) _))
  have hnorm (n : ℕ) : ‖s - p n‖ ≤ ‖t - q n‖ := by
    change upperNorm D (s - p n) ≤ ‖t - q n‖
    apply upperNorm_le D (sub_nonneg.mpr (hqle n))
    rw [abs_of_nonneg (sub_nonneg.mpr (hsLUB.1 ⟨n, rfl⟩))]
    exact hbound n
  have hdist (n : ℕ) : dist (p n) s ≤ dist (q n) t := by
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (p n) s, norm_sub_rev (q n) t]
    exact hnorm n
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsx.hasSum.tendsto_sum_nat ε hε
  exact ⟨N, fun n hn => (hdist n).trans_lt (hN n hn)⟩

/-- Every absolutely summable series converges in the upper norm. -/
private theorem completeSpace (D : DedekindCompletion X) : CompleteSpace D.carrier := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro v hv
  have hp : Summable (fun n => ‖(v n)⁺‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => NormedVectorLattice.norm_posPart_le (v n)) hv
  have hn : Summable (fun n => ‖(v n)⁻‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      simpa only [negPart_def, posPart_def, norm_neg] using
        NormedVectorLattice.norm_posPart_le (-v n)) hv
  obtain ⟨a, ha⟩ := positive_series D (fun n => (v n)⁺) (fun _ => posPart_nonneg _) hp
  obtain ⟨b, hb⟩ := positive_series D (fun n => (v n)⁻) (fun _ => negPart_nonneg _) hn
  refine ⟨a - b, ?_⟩
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, v i) =
      (∑ i ∈ Finset.range n, (v i)⁺) -
        (∑ i ∈ Finset.range n, (v i)⁻) := by
    rw [← Finset.sum_sub_distrib]
    simp only [posPart_sub_negPart]
  simpa only [hsum] using ha.sub hb

/-- The upper norm makes every Dedekind completion of a Banach lattice a Banach lattice. -/
@[reducible]
def banachLattice (D : DedekindCompletion X) : BanachLattice D.carrier :=
  { complete := (completeSpace D).complete }

/-- The inclusion of the original Banach lattice preserves the norm. -/
theorem inclusion_isometry (D : DedekindCompletion X) : Isometry D.inclusion := by
  apply (AddMonoidHomClass.isometry_iff_norm D.inclusion).mpr
  intro x
  exact upperNorm_inclusion D x

end DedekindCompletion
