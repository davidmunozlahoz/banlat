/-
Authors: David Muñoz-Lahoz
-/

import BanLat.Examples.Ellp.Basic
import BanLat.OrderContinuous.MeyerNieberg

/-!
# Order continuity and lattice copies of `ℓ∞`

A sigma order complete Banach lattice has order continuous norm exactly when it does not
contain a lattice copy of `ℓ∞`.
-/

open scoped ENNReal lp Topology
open Filter Finset

noncomputable section

private def linftyBasis (n : ℕ) : ℓ^∞(ℕ, ℝ) :=
  lp.single ∞ n 1

private lemma linftyBasis_nonneg (n : ℕ) : 0 ≤ linftyBasis n := by
  intro k
  change (0 : ℝ) ≤ (Pi.single n (1 : ℝ) : ℕ → ℝ) k
  by_cases h : n = k
  · subst k
    rw [Pi.single_eq_same]
    norm_num
  · rw [Pi.single_eq_of_ne' h]

private lemma linftyBasis_le_one (n : ℕ) : linftyBasis n ≤ 1 := by
  intro k
  change (Pi.single n (1 : ℝ) : ℕ → ℝ) k ≤ (1 : ℝ)
  by_cases h : n = k
  · subst k
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne' h]
    norm_num

private lemma linftyBasis_disjoint :
    Pairwise fun n m => IsVLDisjoint (linftyBasis n) (linftyBasis m) := by
  intro n m hnm
  apply isVLDisjoint_of_inf_eq_zero
  apply lp.ext
  funext k
  change (Pi.single n (1 : ℝ) : ℕ → ℝ) k ⊓
    (Pi.single m (1 : ℝ) : ℕ → ℝ) k = 0
  by_cases hnk : n = k
  · subst k
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hnm]
    simp
  · rw [Pi.single_eq_of_ne' hnk]
    by_cases hmk : m = k
    · subst k
      rw [Pi.single_eq_same]
      norm_num
    · rw [Pi.single_eq_of_ne' hmk]
      simp

private lemma norm_linftyBasis (n : ℕ) : ‖linftyBasis n‖ = 1 := by
  simp [linftyBasis]

private def linftyPartialSum
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (x : ℕ → X) (a : ℓ^∞(ℕ, ℝ)) (N : ℕ) : X :=
  ∑ n ∈ Finset.range N, a n • x n

private def linftyPositiveSeries
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    (x : ℕ → X) (a : ℓ^∞(ℕ, ℝ)) : X :=
  sSup (Set.range (linftyPartialSum x a))

private lemma linftyPartialSum_nonneg
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    {a : ℓ^∞(ℕ, ℝ)} (ha : 0 ≤ a) (N : ℕ) :
    0 ≤ linftyPartialSum x a N := by
  apply Finset.sum_nonneg
  intro n _
  exact smul_nonneg (ha n) (hx n)

private lemma linftyPartialSum_mono
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    {a : ℓ^∞(ℕ, ℝ)} (ha : 0 ≤ a) :
    Monotone (linftyPartialSum x a) := by
  intro N M hNM
  exact Finset.sum_le_sum_of_subset_of_nonneg ((Finset.range_subset_range).2 hNM)
    (fun n _ _ => smul_nonneg (ha n) (hx n))

private lemma sum_range_le_of_pairwise_isVLDisjoint
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) :
    ∀ N, (∑ n ∈ Finset.range N, x n) ≤ w := by
  intro N
  induction N with
  | zero => simpa using (hx 0).trans (hw 0)
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hd : IsVLDisjoint (∑ n ∈ Finset.range N, x n) (x N) :=
        isVLDisjoint_comm.mpr <| IsVLDisjoint.finset_sum_right fun n hn =>
          hdisj (Nat.ne_of_gt (Finset.mem_range.mp hn))
      rw [add_eq_sup_of_isVLDisjoint_of_nonneg
        (Finset.sum_nonneg fun n _ => hx n) (hx N) hd]
      exact sup_le ih (hw N)

private lemma linftyPartialSum_le
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) {a : ℓ^∞(ℕ, ℝ)} (N : ℕ) :
    linftyPartialSum x a N ≤ ‖a‖ • w := by
  calc
    linftyPartialSum x a N ≤ ∑ n ∈ Finset.range N, ‖a‖ • x n := by
      apply Finset.sum_le_sum
      intro n _
      apply smul_le_smul_of_nonneg_right _ (hx n)
      exact (le_abs_self (a n)).trans <| by
        rw [← Real.norm_eq_abs]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero a n
    _ = ‖a‖ • ∑ n ∈ Finset.range N, x n := by
      rw [Finset.smul_sum]
    _ ≤ ‖a‖ • w := by
      exact smul_le_smul_of_nonneg_left
        (sum_range_le_of_pairwise_isVLDisjoint hx hdisj hw N) (norm_nonneg a)

private lemma linftyPositiveSeries_isLUB
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) (a : ℓ^∞(ℕ, ℝ)) :
    IsLUB (Set.range (linftyPartialSum x a)) (linftyPositiveSeries x a) := by
  have hbdd : BddAbove (Set.range (linftyPartialSum x a)) :=
    ⟨‖a‖ • w, by rintro _ ⟨N, rfl⟩; exact linftyPartialSum_le hx hdisj hw N⟩
  constructor
  · intro y hy
    exact SigmaConditionallyCompleteLattice.le_csSup _ _
      (Set.countable_range _) hbdd hy
  · intro y hy
    exact SigmaConditionallyCompleteLattice.csSup_le _ _
      (Set.countable_range _) (Set.range_nonempty _) hy

private lemma linftyPositiveSeries_nonneg
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) (a : ℓ^∞(ℕ, ℝ)) :
    0 ≤ linftyPositiveSeries x a := by
  have h := (linftyPositiveSeries_isLUB hx hdisj hw a).1
    (Set.mem_range_self 0)
  simpa [linftyPartialSum] using h

private lemma isLUB_add_monotone_sequences
    {X : Type*} [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X]
    {u v : ℕ → X} {a b : X} (hu : Monotone u) (hv : Monotone v)
    (hua : IsLUB (Set.range u) a) (hvb : IsLUB (Set.range v) b) :
    IsLUB (Set.range fun n => u n + v n) (a + b) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact add_le_add (hua.1 (Set.mem_range_self n)) (hvb.1 (Set.mem_range_self n))
  · intro z hz
    have hub : ∀ n, u n + b ≤ z := by
      intro n
      rw [add_comm, ← le_sub_iff_add_le]
      apply hvb.2
      rintro _ ⟨m, rfl⟩
      rw [le_sub_iff_add_le]
      rw [add_comm]
      exact (add_le_add (hu (Nat.le_max_left n m))
        (hv (Nat.le_max_right n m))).trans (hz (Set.mem_range_self (max n m)))
    rw [← le_sub_iff_add_le]
    apply hua.2
    rintro _ ⟨n, rfl⟩
    rw [le_sub_iff_add_le]
    exact hub n

private lemma linftyPartialSum_add
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (x : ℕ → X) (a b : ℓ^∞(ℕ, ℝ)) (N : ℕ) :
    linftyPartialSum x (a + b) N =
      linftyPartialSum x a N + linftyPartialSum x b N := by
  simp only [linftyPartialSum, lp.coeFn_add, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]

private lemma linftyPositiveSeries_add
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w)
    {a b : ℓ^∞(ℕ, ℝ)} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    linftyPositiveSeries x (a + b) =
      linftyPositiveSeries x a + linftyPositiveSeries x b := by
  have hsum := isLUB_add_monotone_sequences
    (linftyPartialSum_mono hx ha) (linftyPartialSum_mono hx hb)
    (linftyPositiveSeries_isLUB hx hdisj hw a)
    (linftyPositiveSeries_isLUB hx hdisj hw b)
  have hab := linftyPositiveSeries_isLUB hx hdisj hw (a + b)
  have hrange : Set.range (linftyPartialSum x (a + b)) =
      Set.range (fun N => linftyPartialSum x a N + linftyPartialSum x b N) := by
    congr 1
    funext N
    exact linftyPartialSum_add x a b N
  rw [hrange] at hab
  exact hab.unique hsum

private def linftyLinearMap
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X]
    (x : ℕ → X) (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) : ℓ^∞(ℕ, ℝ) →ₗ[ℝ] X :=
  Positive.extension
    (fun a _ => linftyPositiveSeries_nonneg hx hdisj hw a)
    (fun _ _ ha hb => linftyPositiveSeries_add hx hdisj hw ha hb)

private lemma linftyLinearMap_apply_of_nonneg
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) {a : ℓ^∞(ℕ, ℝ)} (ha : 0 ≤ a) :
    linftyLinearMap x hx hdisj hw a = linftyPositiveSeries x a := by
  exact Positive.extension_nonneg _ _ ha

private lemma isVLDisjoint_posPart_smul_negPart_smul
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (r : ℝ) (y : X) :
    IsVLDisjoint (r⁺ • y) (r⁻ • y) := by
  rcases le_total 0 r with hr | hr
  · rw [negPart_eq_zero.mpr hr, zero_smul]
    exact isVLDisjoint_zero_right _
  · rw [posPart_eq_zero.mpr hr, zero_smul]
    exact isVLDisjoint_zero_left _

private lemma isVLDisjoint_linfty_posPart_negPart_terms
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {x : ℕ → X}
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    (a : ℓ^∞(ℕ, ℝ)) (i j : ℕ) :
    IsVLDisjoint ((a i)⁺ • x i) ((a j)⁻ • x j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact isVLDisjoint_posPart_smul_negPart_smul _ _
  · exact ((hdisj hij).smul_left (a i)⁺).smul_right (a j)⁻

private lemma isVLDisjoint_linftyPartialSum_posPart_negPart
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {x : ℕ → X}
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    (a : ℓ^∞(ℕ, ℝ)) (N M : ℕ) :
    IsVLDisjoint (linftyPartialSum x a⁺ N) (linftyPartialSum x a⁻ M) := by
  change IsVLDisjoint (∑ i ∈ Finset.range N, (a i)⁺ • x i)
    (∑ j ∈ Finset.range M, (a j)⁻ • x j)
  apply IsVLDisjoint.finset_sum_right
  intro j _
  rw [isVLDisjoint_comm]
  apply IsVLDisjoint.finset_sum_right
  intro i _
  exact isVLDisjoint_comm.mpr
    (isVLDisjoint_linfty_posPart_negPart_terms hdisj a i j)

private lemma isVLDisjoint_linftyPositiveSeries_posPart_negPart
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) (a : ℓ^∞(ℕ, ℝ)) :
    IsVLDisjoint (linftyPositiveSeries x a⁺) (linftyPositiveSeries x a⁻) := by
  apply isVLDisjoint_of_inf_eq_zero
  apply le_antisymm
  · apply (isLUB_inf_const (linftyPositiveSeries x a⁺)
      (linftyPositiveSeries_isLUB hx hdisj hw a⁻)).2
    rintro _ ⟨_, ⟨M, rfl⟩, rfl⟩
    change linftyPositiveSeries x a⁺ ⊓ linftyPartialSum x a⁻ M ≤ 0
    rw [inf_comm]
    apply (isLUB_inf_const (linftyPartialSum x a⁻ M)
      (linftyPositiveSeries_isLUB hx hdisj hw a⁺)).2
    rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
    change linftyPartialSum x a⁻ M ⊓ linftyPartialSum x a⁺ N ≤ 0
    exact le_of_eq <| inf_eq_zero_of_isVLDisjoint
      (linftyPartialSum_nonneg hx (negPart_nonneg a) M)
      (linftyPartialSum_nonneg hx (posPart_nonneg a) N)
      (isVLDisjoint_comm.mpr <|
        isVLDisjoint_linftyPartialSum_posPart_negPart hdisj a N M)
  · exact le_inf (linftyPositiveSeries_nonneg hx hdisj hw _)
      (linftyPositiveSeries_nonneg hx hdisj hw _)

private lemma abs_sub_eq_add_of_isVLDisjoint_of_nonneg
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {y z : X} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hdisj : IsVLDisjoint y z) : |y - z| = y + z := by
  rw [sub_eq_add_neg, abs_add_of_isVLDisjoint, abs_of_nonneg hy, abs_neg,
    abs_of_nonneg hz]
  simpa only [neg_one_smul] using hdisj.smul_right (-1)

private lemma linftyLinearMap_map_abs
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) (a : ℓ^∞(ℕ, ℝ)) :
    linftyLinearMap x hx hdisj hw |a| = |linftyLinearMap x hx hdisj hw a| := by
  rw [linftyLinearMap_apply_of_nonneg hx hdisj hw (abs_nonneg a)]
  change linftyPositiveSeries x |a| =
    |linftyPositiveSeries x a⁺ - linftyPositiveSeries x a⁻|
  rw [← posPart_add_negPart a,
    linftyPositiveSeries_add hx hdisj hw (posPart_nonneg a) (negPart_nonneg a)]
  exact (abs_sub_eq_add_of_isVLDisjoint_of_nonneg
    (linftyPositiveSeries_nonneg hx hdisj hw _)
    (linftyPositiveSeries_nonneg hx hdisj hw _)
    (isVLDisjoint_linftyPositiveSeries_posPart_negPart hx hdisj hw a)).symm

private def linftyVecLatHom
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X]
    (x : ℕ → X) (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) : VecLatHom (ℓ^∞(ℕ, ℝ)) X :=
  VecLatHom.ofAbs (linftyLinearMap x hx hdisj hw)
    (linftyLinearMap_map_abs hx hdisj hw)

private lemma linftyVecLatHom_coordinate_le
    {X : Type*} [AddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) (a : ℓ^∞(ℕ, ℝ)) (n : ℕ) :
    |a n| • x n ≤ linftyVecLatHom x hx hdisj hw |a| := by
  change |a n| • x n ≤ linftyLinearMap x hx hdisj hw |a|
  rw [linftyLinearMap_apply_of_nonneg hx hdisj hw (abs_nonneg a)]
  have hterm : |a n| • x n ≤ linftyPartialSum x |a| (n + 1) := by
    rw [linftyPartialSum, Finset.sum_range_succ]
    change |a n| • x n ≤
      (∑ i ∈ Finset.range n, |a i| • x i) + |a n| • x n
    exact le_add_of_nonneg_left <| Finset.sum_nonneg fun i _ =>
      smul_nonneg (abs_nonneg (a i)) (hx i)
  exact hterm.trans <| (linftyPositiveSeries_isLUB hx hdisj hw |a|).1
    (Set.mem_range_self (n + 1))

private lemma linftyVecLatHom_norm_le
    {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] [IsVLArchimedean X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) {ε : ℝ} (hε : 0 < ε)
    (hx_norm : ∀ n, ε ≤ ‖x n‖) (a : ℓ^∞(ℕ, ℝ)) :
    ‖a‖ ≤ ε⁻¹ * ‖linftyVecLatHom x hx hdisj hw a‖ := by
  have hcoord : ∀ n, ε * |a n| ≤ ‖linftyVecLatHom x hx hdisj hw a‖ := by
    intro n
    have hnorm : ‖|a n| • x n‖ ≤ ‖linftyVecLatHom x hx hdisj hw |a|‖ := by
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (smul_nonneg (abs_nonneg _) (hx n)),
        abs_of_nonneg ((linftyVecLatHom x hx hdisj hw).map_nonneg (abs_nonneg a))]
      exact linftyVecLatHom_coordinate_le hx hdisj hw a n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
      VecLatHom.map_abs, norm_abs_eq_norm] at hnorm
    calc
      ε * |a n| = |a n| * ε := mul_comm _ _
      _ ≤ |a n| * ‖x n‖ := mul_le_mul_of_nonneg_left (hx_norm n) (abs_nonneg _)
      _ ≤ ‖linftyVecLatHom x hx hdisj hw a‖ := hnorm
  apply lp.norm_le_of_forall_le (mul_nonneg (inv_nonneg.mpr hε.le) (norm_nonneg _))
  intro n
  rw [Real.norm_eq_abs, le_inv_mul_iff₀ hε]
  exact hcoord n

private theorem containsLatticeCopy_linf_of_disjoint
    {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [BanachLattice X]
    {x : ℕ → X} (hx : ∀ n, 0 ≤ x n)
    (hdisj : Pairwise fun n m => IsVLDisjoint (x n) (x m))
    {w : X} (hw : ∀ n, x n ≤ w) {ε : ℝ} (hε : 0 < ε)
    (hx_norm : ∀ n, ε ≤ ‖x n‖) :
    ContainsLatticeCopy X (ℓ^∞(ℕ, ℝ)) := by
  letI : IsVLArchimedean X := IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  let T : VecLatHom (ℓ^∞(ℕ, ℝ)) X := linftyVecLatHom x hx hdisj hw
  have hnorm : ∀ a, ‖a‖ ≤ ε⁻¹ * ‖T a‖ := by
    intro a
    exact linftyVecLatHom_norm_le hx hdisj hw hε hx_norm a
  have hinj : Function.Injective T := by
    intro a b hab
    have h := hnorm (a - b)
    rw [map_sub, hab, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  let Tc : ℓ^∞(ℕ, ℝ) →L[ℝ] X := ContinuousLinearMap.mk T.toLinearMap <|
    Positive.continuous (Positive.monotone_iff.mp T.monotone)
  let K : NNReal := ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩
  have hanti : AntilipschitzWith K Tc := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    change dist a b ≤ ε⁻¹ * dist (Tc a) (Tc b)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hnorm (a - b)
  have hclosed_range : IsClosed (Set.range Tc) :=
    hanti.isClosed_range Tc.uniformContinuous
  let Z : VectorSublattice X :=
    { toSubmodule := T.toLinearMap.range
      sup_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a ⊔ b, map_sup T a b⟩ }
  have hrange : (T.toLinearMap.range : Set X) = Set.range Tc := by
    ext y
    constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, rfl⟩
  have hZ_closed : IsClosed (Z : Set X) := by
    change IsClosed (T.toLinearMap.range : Set X)
    rw [hrange]
    exact hclosed_range
  let Tr : ℓ^∞(ℕ, ℝ) →ₗ[ℝ] Z := T.toLinearMap.rangeRestrict
  have hTr_bij : Function.Bijective Tr := by
    constructor
    · intro a b hab
      apply hinj
      exact congrArg Subtype.val hab
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha⟩ := hy
      refine ⟨a, ?_⟩
      exact Subtype.ext ha
  let e : VecLatEquiv (ℓ^∞(ℕ, ℝ)) Z :=
    { toLinearEquiv := LinearEquiv.ofBijective Tr hTr_bij
      map_sup' := by
        intro a b
        apply Subtype.ext
        exact map_sup T a b
      map_inf' := by
        intro a b
        apply Subtype.ext
        exact map_inf T a b }
  exact ⟨Z, hZ_closed, ⟨e⟩⟩

private lemma exists_strictMono_norm_ge_of_not_tendsto_zero
    {X : Type*} [NormedAddCommGroup X] {u : ℕ → X}
    (hnot : ¬ Filter.Tendsto u Filter.atTop (nhds 0)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ε ≤ ‖u (φ n)‖ := by
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  obtain ⟨φ, hφ_mono, hφ⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨ε, hε, φ, hφ_mono, fun n => ?_⟩
  simpa [dist_zero_right] using hφ n

private theorem containsLatticeCopy_linf_of_not_isOrderContinuousNorm
    {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [BanachLattice X]
    (hX : ¬ IsOrderContinuousNorm X) :
    ContainsLatticeCopy X (ℓ^∞(ℕ, ℝ)) := by
  have hfail : ¬ ∀ {u : ℕ → X},
      Pairwise (fun n m => IsVLDisjoint (u n) (u m)) →
      BddAbove (Set.range fun n => |u n|) →
      Filter.Tendsto u Filter.atTop (nhds 0) := by
    intro h
    exact hX (BanachLattice.isOrderContinuousNorm_iff_disjoint_tendsto_zero.mpr h)
  push Not at hfail
  obtain ⟨u, hu_disj, hu_bdd, hu_not⟩ := hfail
  obtain ⟨ε, hε, φ, hφ_mono, hφ_norm⟩ :=
    exists_strictMono_norm_ge_of_not_tendsto_zero hu_not
  let x : ℕ → X := fun n => |u (φ n)|
  have hx : ∀ n, 0 ≤ x n := fun n => abs_nonneg _
  have hx_disj : Pairwise fun n m => IsVLDisjoint (x n) (x m) := by
    intro n m hnm
    have hφ_ne : φ n ≠ φ m := hφ_mono.injective.ne hnm
    simpa [x, IsVLDisjoint, abs_abs] using hu_disj hφ_ne
  obtain ⟨w, hw⟩ := hu_bdd
  have hx_le : ∀ n, x n ≤ w := fun n => hw (Set.mem_range_self (φ n))
  have hx_norm : ∀ n, ε ≤ ‖x n‖ := fun n => by
    simpa [x, norm_abs_eq_norm] using hφ_norm n
  exact containsLatticeCopy_linf_of_disjoint hx hx_disj hx_le hε hx_norm

private theorem not_containsLatticeCopy_linf_of_isOrderContinuousNorm
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [IsOrderContinuousNorm X] :
    ¬ ContainsLatticeCopy X (ℓ^∞(ℕ, ℝ)) := by
  rintro ⟨Z, hZ_closed, ⟨e⟩⟩
  letI : BanachLattice Z := Z.banachLatticeCoe hZ_closed
  let v : ℕ → X := fun n => (e (linftyBasis n)).1
  have hv_nonneg : ∀ n, 0 ≤ v n := fun n =>
    e.toVecLatHom.map_nonneg (linftyBasis_nonneg n)
  have hv_disj : Pairwise fun n m => IsVLDisjoint (v n) (v m) := by
    intro n m hnm
    apply isVLDisjoint_of_inf_eq_zero
    have hbase : linftyBasis n ⊓ linftyBasis m = 0 :=
      inf_eq_zero_of_isVLDisjoint (linftyBasis_nonneg n) (linftyBasis_nonneg m)
        (linftyBasis_disjoint hnm)
    exact congrArg Subtype.val (e.toVecLatHom.map_disjoint hbase)
  have hv_bdd : BddAbove (Set.range fun n => |v n|) := by
    refine ⟨(e 1).1, ?_⟩
    rintro _ ⟨n, rfl⟩
    change |v n| ≤ (e 1).1
    rw [abs_of_nonneg (hv_nonneg n)]
    exact e.toVecLatHom.monotone (linftyBasis_le_one n)
  have hv_tend : Filter.Tendsto v Filter.atTop (nhds 0) :=
    BanachLattice.disjoint_bddAbove_tendsto_zero hv_disj hv_bdd
  have he_tend : Filter.Tendsto (fun n => e (linftyBasis n))
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_nhds] at hv_tend ⊢
    intro ε hε
    simpa [v] using hv_tend ε hε
  have hbasis_tend : Filter.Tendsto linftyBasis Filter.atTop (nhds 0) := by
    have h := (e.toContinuousLinearEquiv.symm.continuous.tendsto 0).comp he_tend
    have h' : Filter.Tendsto
        (e.toContinuousLinearEquiv.symm ∘ fun n => e (linftyBasis n))
        Filter.atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    exact Filter.Eventually.of_forall fun n => by
      change e.toContinuousLinearEquiv.symm (e.toContinuousLinearEquiv (linftyBasis n)) =
        linftyBasis n
      exact e.toContinuousLinearEquiv.symm_apply_apply _
  rw [Metric.tendsto_nhds] at hbasis_tend
  have hev := hbasis_tend (1 / 2) (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have h := hN N (le_refl N)
  rw [dist_zero_right, norm_linftyBasis] at h
  norm_num at h

/-- A sigma order complete Banach lattice has order continuous norm if and only if it
does not contain a lattice copy of `ℓ∞`. -/
theorem isOrderContinuousNorm_iff_not_containsLatticeCopy_linfty
    {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] :
    IsOrderContinuousNorm X ↔ ¬ ContainsLatticeCopy X (ℓ^∞(ℕ, ℝ)) := by
  constructor
  · intro hX
    letI : IsOrderContinuousNorm X := hX
    exact not_containsLatticeCopy_linf_of_isOrderContinuousNorm
  · intro hcopy
    by_contra hX
    exact hcopy (containsLatticeCopy_linf_of_not_isOrderContinuousNorm hX)
