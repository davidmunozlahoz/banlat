/-
Authors: Pedro Tradacete
-/

import BanLat.PConvexity
import BanLat.Dual
import BanLat.Preliminaries.PiLpDuality
import Mathlib.Topology.PartitionOfUnity

/-!
# Lattice Hölder inequalities

Finite partitions of unity transfer scalar inequalities to the pairing between a Banach
lattice and its dual. This gives the lattice Hölder inequality for conjugate exponents.
-/

noncomputable section

open scoped BigOperators

/-- A finite continuous family on a compact space can be uniformly approximated by
convex combinations of its values, using one common finite partition of unity. -/
private lemma exists_partition_approximation {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] {ι : Type*} [Finite ι] (f : ι → C(K, ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset K) (ρ : PartitionOfUnity s K),
      ∀ i, ‖∑ j : s, f i j • ρ j - f i‖ ≤ ε := by
  classical
  let := Fintype.ofFinite ι
  let U (t : K) : Set K := {s | ∀ i, dist (f i s) (f i t) < ε}
  have hU (t : K) : IsOpen (U t) := by
    simpa only [U, Set.ofPred_forall] using
      isOpen_iInter_of_finite (fun i ↦ isOpen_lt ((f i).continuous.dist continuous_const)
        continuous_const)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun t _ ↦ Set.mem_iUnion.mpr ⟨t, by simpa [U] using fun _ : ι ↦ hε⟩)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun j : s ↦ U j) (fun j ↦ hU j) (by simpa only [Set.iUnion_subtype] using hs)
  refine ⟨s, ρ, fun i ↦ (ContinuousMap.norm_le _ hε.le).mpr fun t ↦ ?_⟩
  have hsum : ∑ j : s, ρ j t = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ t)
  have hbound (j : s) : ‖(f i j - f i t) * ρ j t‖ ≤ ε * ρ j t := by
    by_cases hj : ρ j t = 0
    · simp [hj]
    · rw [norm_mul, Real.norm_of_nonneg (ρ.nonneg j t)]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.dist_eq, abs_sub_comm, Real.norm_eq_abs] using
          (hρ j (subset_closure hj) i).le) (ρ.nonneg j t)
  calc
    ‖(∑ j : s, f i j • ρ j - f i) t‖ =
        ‖∑ j : s, (f i j - f i t) * ρ j t‖ := by
      simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hsum, mul_one]
    _ ≤ ∑ j : s, ‖(f i j - f i t) * ρ j t‖ := norm_sum_le _ _
    _ ≤ ∑ j : s, ε * ρ j t := Finset.sum_le_sum fun j _ ↦ hbound j
    _ = ε := by rw [← Finset.mul_sum, hsum, mul_one]

/-- If every scalar combination obtained by evaluating a continuous family is a positive
functional, then applying each functional to its corresponding function has nonnegative sum. -/
private lemma sum_dual_apply_nonneg {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] {ι : Type*} [Fintype ι] (f : ι → C(K, ℝ))
    (φ : ι → StrongDual ℝ C(K, ℝ)) (hφ : ∀ t, 0 ≤ ∑ i, f i t • φ i) :
    0 ≤ ∑ i, φ i (f i) := by
  classical
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hA : 0 ≤ ∑ i, ‖φ i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg (φ i)
  let δ := ε / (∑ i, ‖φ i‖ + 1)
  obtain ⟨s, ρ, hρ⟩ := exists_partition_approximation f
    (show 0 < δ from div_pos hε (by positivity))
  let g (i : ι) : C(K, ℝ) := ∑ j : s, f i j • ρ j
  have hg : 0 ≤ ∑ i, φ i (g i) := by
    have hj (j : s) := StrongDual.apply_nonneg_of_nonneg (hφ j)
      (show 0 ≤ ρ j from ρ.nonneg j)
    simp only [g, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    simpa only [sum_apply, smul_apply, smul_eq_mul] using
      Finset.sum_nonneg (s := Finset.univ) (fun j _ ↦ hj j)
  have he : ∑ i, φ i (g i) ≤ ∑ i, φ i (f i) + (∑ i, ‖φ i‖) * δ := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hi := (le_abs_self (φ i (g i - f i))).trans
      (((φ i).le_opNorm (g i - f i)).trans
        (mul_le_mul_of_nonneg_left (hρ i) (norm_nonneg (φ i))))
    simpa only [map_sub, sub_le_iff_le_add, add_comm] using hi
  have hδ : (∑ i, ‖φ i‖) * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- Positivity of all scalar combinations transfers to functional calculus inside the
duality pairing, by restricting the homogeneous functions to the compact unit sphere. -/
private lemma sum_apply_functionalCalculus_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (x : Fin n → X) (f : ι → posHomFunctions n) (φ : ι → StrongDual ℝ X)
    (hφ : ∀ a : Fin n → ℝ, 0 ≤ ∑ i, f i a • φ i) :
    letI := isUniformlyCompleteVectorLattice_of_banachLattice X
    0 ≤ ∑ i, φ i (PosHomFunction.functionalCalculus x (f i)) := by
  let := isUniformlyCompleteVectorLattice_of_banachLattice X
  let e := PosHomFunction.ellInfinityUnitSphereEquiv (n := n)
  let V := (PosHomFunction.functionalCalculus x).comp e.symm.toVecLatHom
  have h (t : PosHomFunction.ellInfinityUnitSphere n) :
      0 ≤ ∑ i, e (f i) t • (φ i).comp V.toContinuousLinearMap := by
    refine StrongDual.nonneg_iff.mpr fun g hg ↦ ?_
    have hpos := StrongDual.apply_nonneg_of_nonneg (hφ t)
      (show 0 ≤ V g by simpa only [map_zero] using V.monotone hg)
    simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
      VecLatHom.toContinuousLinearMap_apply] at hpos ⊢
    exact hpos
  have hd := sum_dual_apply_nonneg (fun i ↦ e (f i))
    (fun i ↦ (φ i).comp V.toContinuousLinearMap) h
  have he (i : ι) : e.symm.toVecLatHom (e (f i)) = f i :=
    e.toLinearEquiv.symm_apply_apply (f i)
  simpa only [ContinuousLinearMap.comp_apply, VecLatHom.toContinuousLinearMap_apply,
    V, VecLatHom.comp_apply, he] using hd

open scoped ENNReal

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Bounds on all scalar combinations of a dual family also bound its pairing with
a lattice family by the dominating functional evaluated at the lattice p-sum. -/
theorem sum_apply_le_of_sum_smul_le {n : ℕ} (x : Fin n → X)
    (φ : Fin n → StrongDual ℝ X) (ψ : StrongDual ℝ X)
    (hψ : ∀ a : Fin n → ℝ, ∑ i, a i • φ i ≤ ‖WithLp.toLp p a‖ • ψ) :
    ∑ i, φ i (x i) ≤ ψ (latticePSum p x) := by
  let := isUniformlyCompleteVectorLattice_of_banachLattice X
  let f : Fin (n + 1) → posHomFunctions n :=
    Fin.cons (pSumFunction p n) (fun i ↦ -PosHomFunction.coordinate i)
  let Φ : Fin (n + 1) → StrongDual ℝ X := Fin.cons ψ φ
  have hΦ (a : Fin n → ℝ) : 0 ≤ ∑ i, f i a • Φ i := by
    simp only [f, Φ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change 0 ≤ ‖WithLp.toLp p a‖ • ψ + ∑ i, (-a i) • φ i
    simpa only [neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
      using sub_nonneg.mpr (hψ a)
  have h := sum_apply_functionalCalculus_nonneg x f Φ hΦ
  simpa only [f, Φ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_neg,
    PosHomFunction.functionalCalculus_coordinate, Finset.sum_neg_distrib,
    ← sub_eq_add_neg, sub_nonneg, latticePSum] using h

/-- Scalar coefficients in the unit ball of ℓᵖ send a positive finite partition
to a family whose lattice p-sum is bounded by the sum of that partition. -/
private lemma latticePSum_sum_smul_le_sum_fin {m n : ℕ}
    (a : Fin m → Fin n → ℝ) (ha : ∀ j, ‖WithLp.toLp p (a j)‖ ≤ 1)
    (y : Fin m → X) (hy : ∀ j, 0 ≤ y j) :
    latticePSum p (fun i ↦ ∑ j, a j i • y j) ≤ ∑ j, y j := by
  classical
  let := isUniformlyCompleteVectorLattice_of_banachLattice X
  let g (i : Fin n) : posHomFunctions m := ∑ j, a j i • PosHomFunction.coordinate j
  have hg (i : Fin n) (z : Fin m → ℝ) : g i z = ∑ j, a j i * z j := by
    change ((posHomFunctions m).toSubmodule.subtype
      (∑ j, a j i • PosHomFunction.coordinate j)) z = _
    simp only [map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply]
    rfl
  have hpoint : PosHomFunction.comp (pSumFunction p n) g ≤ pSumFunction 1 m := by
    intro z
    change ‖WithLp.toLp p (fun i ↦ g i z)‖ ≤ ‖WithLp.toLp 1 z‖
    have he : (fun i ↦ g i z) = ∑ j, z j • a j := by
      ext i
      simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he, WithLp.toLp_sum]
    refine (norm_sum_le _ _).trans ?_
    simp only [WithLp.toLp_smul, norm_smul, PiLp.norm_eq_of_L1]
    exact Finset.sum_le_sum fun j _ ↦
      (mul_le_mul_of_nonneg_left (ha j) (norm_nonneg (z j))).trans_eq (mul_one _)
  have hcalc := (PosHomFunction.functionalCalculus y).monotone hpoint
  rw [← PosHomFunction.functionalCalculus_comp] at hcalc
  simp only [g, map_sum, map_smul, PosHomFunction.functionalCalculus_coordinate] at hcalc
  change latticePSum p (fun i ↦ ∑ j, a j i • y j) ≤ latticePSum 1 y at hcalc
  simpa only [latticePSum_one, abs_of_nonneg (hy _)] using hcalc

/-- Coefficients from the scalar ℓᵖ unit ball combine a positive finite family
into vectors whose lattice p-sum is bounded by the sum of the original family. -/
theorem latticePSum_sum_smul_le_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (ha : ∀ j, ‖WithLp.toLp p (a j)‖ ≤ 1)
    (y : ι → X) (hy : ∀ j, 0 ≤ y j) :
    latticePSum p (fun i ↦ ∑ j, a j i • y j) ≤ ∑ j, y j := by
  let e := (Fintype.equivFin ι).symm
  have he (i : Fin n) : ∑ j, a (e j) i • y (e j) = ∑ j, a j i • y j :=
    e.sum_comp (fun j ↦ a j i • y j)
  simpa only [he, Equiv.sum_comp] using latticePSum_sum_smul_le_sum_fin
    (fun j ↦ a (e j)) (fun j ↦ ha (e j)) (fun j ↦ y (e j)) (fun j ↦ hy (e j))

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

omit [Fact (1 ≤ p)] in
/-- A scalar combination of a lattice family is dominated by its lattice q-sum
multiplied by the ℓᵖ norm of the coefficients, for conjugate exponents `p` and `q`. -/
theorem sum_smul_le_norm_smul_latticePSum {n : ℕ} (a : Fin n → ℝ) (x : Fin n → X) :
    ∑ i, a i • x i ≤ ‖WithLp.toLp p a‖ • latticePSum q x := by
  let := isUniformlyCompleteVectorLattice_of_banachLattice X
  have hpoint : (∑ i, a i • PosHomFunction.coordinate i) ≤
      ‖WithLp.toLp p a‖ • pSumFunction q n := by
    intro b
    change (∑ i, a i • PosHomFunction.coordinate i : posHomFunctions n) b ≤ _
    change ((posHomFunctions n).toSubmodule.subtype
      (∑ i, a i • PosHomFunction.coordinate i)) b ≤ _
    simp only [map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply]
    exact PiLp.sum_mul_le_norm_mul (p := p) (q := q) a b
  simpa only [map_sum, map_smul, PosHomFunction.functionalCalculus_coordinate, latticePSum]
    using (PosHomFunction.functionalCalculus x).monotone hpoint

/-- The pairing of two finite families is bounded by the dual lattice q-sum evaluated
at the lattice p-sum, whenever `p` and `q` are conjugate exponents. -/
theorem sum_apply_le_latticePSum_apply_latticePSum {n : ℕ} (x : Fin n → X)
    (φ : Fin n → StrongDual ℝ X) :
    ∑ i, φ i (x i) ≤ (latticePSum q φ) (latticePSum p x) :=
  sum_apply_le_of_sum_smul_le x φ (latticePSum q φ)
    (fun a ↦ sum_smul_le_norm_smul_latticePSum a φ)

/-- The absolute value of a finite dual pairing is bounded by evaluating the dual
lattice q-sum at the lattice p-sum, including the conjugate endpoint exponents. -/
theorem abs_sum_apply_le_latticePSum_apply_latticePSum {n : ℕ} (x : Fin n → X)
    (φ : Fin n → StrongDual ℝ X) :
    |∑ i, φ i (x i)| ≤ (latticePSum q φ) (latticePSum p x) := by
  refine abs_le.mpr ⟨?_, sum_apply_le_latticePSum_apply_latticePSum x φ⟩
  have h := sum_apply_le_of_sum_smul_le x (fun i ↦ -φ i) (latticePSum q φ)
    (fun a ↦ by
      simpa only [smul_neg, neg_smul, Pi.neg_apply, WithLp.toLp_neg, norm_neg] using
        sum_smul_le_norm_smul_latticePSum (p := p) (-a) φ)
  simpa only [neg_apply, Finset.sum_neg_distrib, neg_le] using h

/-- Lattice Hölder bounds a finite dual pairing by the product of the norms of
the lattice p-sum and the dual lattice q-sum. -/
theorem abs_sum_apply_le_norm_latticePSum_mul_norm_latticePSum {n : ℕ}
    (x : Fin n → X) (φ : Fin n → StrongDual ℝ X) :
    |∑ i, φ i (x i)| ≤ ‖latticePSum p x‖ * ‖latticePSum q φ‖ := by
  calc
    |∑ i, φ i (x i)| ≤ (latticePSum q φ) (latticePSum p x) :=
      abs_sum_apply_le_latticePSum_apply_latticePSum x φ
    _ ≤ ‖latticePSum q φ‖ * ‖latticePSum p x‖ :=
      (le_abs_self _).trans ((latticePSum q φ).le_opNorm (latticePSum p x))
    _ = ‖latticePSum p x‖ * ‖latticePSum q φ‖ := mul_comm _ _
