/-
Authors: Pedro Tradacete
-/

import BanLat.PConvexity.Holder
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Dual representations of lattice q-sums

Finite Riesz–Kantorovich formulas and scalar supporting functionals identify the norm of
lattice q-sums in the dual with the corresponding finite-family pairing norm.
-/

open scoped ENNReal Topology

noncomputable section

variable {p q : ℝ≥0∞} [p.HolderConjugate q]

private lemma exists_finite_scalar_support {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (PiLp p (fun _ : Fin n ↦ ℝ)), ∃ hs : s.Nonempty,
      (∀ a ∈ s, ‖a‖ ≤ 1) ∧ ∀ b : Fin n → ℝ,
        (1 - ε) * ‖WithLp.toLp q b‖ ≤ s.sup' hs (fun a ↦ ∑ i, a i * b i) := by
  classical
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let := (PiLp.basisFun p ℝ (Fin n)).finiteDimensional_of_finite
  obtain ⟨s, hsball, hsfin, hscover⟩ :=
    (isCompact_closedBall (0 : PiLp p (fun _ : Fin n ↦ ℝ)) 1).finite_cover_balls hε
  obtain ⟨a₀, ha₀, _⟩ := Set.mem_iUnion₂.mp
    (hscover (by simp : (0 : PiLp p (fun _ : Fin n ↦ ℝ)) ∈ Metric.closedBall 0 1))
  refine ⟨hsfin.toFinset, ⟨a₀, hsfin.mem_toFinset.mpr ha₀⟩,
    fun a ha ↦ mem_closedBall_zero_iff.mp (hsball (hsfin.mem_toFinset.mp ha)), ?_⟩
  intro b
  obtain ⟨a, ha, hab⟩ := PiLp.exists_norming (p := q) (q := p) b
  have hab' : ∑ i, a i * b i = ‖WithLp.toLp q b‖ := by simpa only [mul_comm] using hab
  obtain ⟨c, hc, hac⟩ := Set.mem_iUnion₂.mp (hscover (mem_closedBall_zero_iff.mpr ha))
  have hclose : ‖WithLp.toLp p (fun i ↦ a i - c i)‖ ≤ ε :=
    (show ‖WithLp.toLp p a - c‖ < ε from by
      simpa only [Metric.mem_ball, dist_eq_norm] using hac).le
  have hpair := (PiLp.sum_mul_le_norm_mul (p := p) (q := q)
    (fun i ↦ a i - c i) b).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  apply le_trans ?_ (Finset.le_sup' (fun a ↦ ∑ i, a i * b i) (hsfin.mem_toFinset.mpr hc))
  simpa only [sub_mul, Finset.sum_sub_distrib, hab, one_mul] using
    (show ‖WithLp.toLp q b‖ - ε * ‖WithLp.toLp q b‖ ≤ ∑ i, c i * b i from
      sub_le_comm.mp (by simpa only [sub_mul, Finset.sum_sub_distrib, hab'] using hpair))

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X] [Fact (1 ≤ q)]

private lemma exists_finite_lattice_support {n : ℕ} (x : Fin n → X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (PiLp p (fun _ : Fin n ↦ ℝ)), ∃ hs : s.Nonempty,
      (∀ a ∈ s, ‖a‖ ≤ 1) ∧
        (1 - ε) • latticePSum q x ≤ s.sup' hs (fun a ↦ ∑ i, a i • x i) := by
  obtain ⟨s, hs, hnorms, hbound⟩ := exists_finite_scalar_support (p := p) (q := q) (n := n) hε
  let := isUniformlyCompleteVectorLattice_of_banachLattice X
  have hfun : (1 - ε) • pSumFunction q n ≤
      s.sup' hs (fun a ↦ ∑ i, a i • PosHomFunction.coordinate i) := by
    intro b
    apply (hbound b).trans
    refine Finset.sup'_le hs _ fun a ha ↦ ?_
    have h := (Finset.le_sup' (fun a ↦ ∑ i, a i • PosHomFunction.coordinate i) ha) b
    change ((posHomFunctions n).toSubmodule.subtype
      (∑ i, a i • PosHomFunction.coordinate i)) b ≤ _ at h
    simp only [map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply] at h
    exact h
  refine ⟨s, hs, hnorms, ?_⟩
  simpa only [map_smul, map_finset_sup', Function.comp_def, map_sum,
    PosHomFunction.functionalCalculus_coordinate, latticePSum] using
    (PosHomFunction.functionalCalculus x).monotone hfun

private lemma isLUB_finset_sup_dual_apply {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (φ : ι → StrongDual ℝ X) {x : X} (hx : 0 ≤ x) :
    IsLUB {w | ∃ y : ι → X, (∀ i ∈ s, 0 ≤ y i) ∧
      (∑ i ∈ s, y i = x) ∧ w = ∑ i ∈ s, φ i (y i)} ((s.sup' hs φ) x) := by
  let e : StrongDual ℝ X ≃o OrderDualSpace X :=
    { StrongDual.equivOrderDualSpace.toEquiv with map_rel_iff' := Iff.rfl }
  have h := OrderBoundedHom.isLUB_finset_sup_apply hs (e ∘ φ) hx
  rw [← map_finset_sup' e hs φ] at h
  exact h

variable [Fact (1 ≤ p)]

private lemma finset_support_apply_le {n : ℕ} (φ : Fin n → StrongDual ℝ X)
    {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ x : Fin n → X, ∑ i, φ i (x i) ≤ C * ‖latticePSum p x‖)
    {s : Finset (PiLp p (fun _ : Fin n ↦ ℝ))} (hs : s.Nonempty)
    (hsnorm : ∀ a ∈ s, ‖a‖ ≤ 1) {u : X} (hu : 0 ≤ u) :
    (s.sup' hs (fun a ↦ ∑ i, a i • φ i)) u ≤ C * ‖u‖ := by
  apply (isLUB_finset_sup_dual_apply hs (fun a ↦ ∑ i, a i • φ i) hu).2
  rintro _ ⟨y, hy, hsum, rfl⟩
  calc
    _ = ∑ i, φ i (∑ a ∈ s, a i • y a) := by
      simp only [sum_apply, smul_apply, smul_eq_mul, map_sum, map_smul]
      exact Finset.sum_comm
    _ ≤ C * ‖latticePSum p (fun i ↦ ∑ a ∈ s, a i • y a)‖ := hpair _
    _ ≤ C * ‖u‖ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply norm_le_norm_of_abs_le_abs
      have hsum' (i : Fin n) : (∑ a : s, a.1.ofLp i • y a.1) =
          ∑ a ∈ s, a i • y a := s.sum_coe_sort (fun a ↦ a i • y a)
      simpa only [abs_of_nonneg (latticePSum_nonneg p _), abs_of_nonneg hu,
        hsum', Finset.sum_coe_sort, hsum] using
        latticePSum_sum_smul_le_sum (p := p) (fun a : s ↦ a.1.ofLp)
          (fun a ↦ hsnorm a.1 a.2) (fun a : s ↦ y a.1) (fun a ↦ hy a.1 a.2)

private lemma latticePSum_dual_apply_le_of_pairing {n : ℕ}
    (φ : Fin n → StrongDual ℝ X) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ x : Fin n → X, ∑ i, φ i (x i) ≤ C * ‖latticePSum p x‖)
    {u : X} (hu : 0 ≤ u) : (latticePSum q φ) u ≤ C * ‖u‖ := by
  have hlim : Filter.Tendsto (fun ε : ℝ ↦ (1 - ε) * (latticePSum q φ) u)
      (𝓝[>] 0) (𝓝 ((latticePSum q φ) u)) := by
    convert
      (((continuous_const.sub continuous_id).mul continuous_const :
        Continuous (fun ε : ℝ ↦ (1 - ε) * (latticePSum q φ) u)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))) using 1
    · rfl
    · simp
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨s, hs, hsbound, hsupport⟩ := exists_finite_lattice_support (p := p) (q := q) φ hε
  exact (StrongDual.le_iff.mp hsupport u hu).trans
    (finset_support_apply_le φ hC hpair hs hsbound hu)

/-- For conjugate exponents `p` and `q` and `C ≥ 0`, the bound
`∑ i, φ i (x i) ≤ C * ‖latticePSum p x‖` for every family `x : Fin n → X` implies
`‖latticePSum q φ‖ ≤ C`. This includes the endpoint exponents one and infinity. -/
theorem norm_latticePSum_dual_le {n : ℕ} (φ : Fin n → StrongDual ℝ X)
    {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ x : Fin n → X, ∑ i, φ i (x i) ≤ C * ‖latticePSum p x‖) :
    ‖latticePSum q φ‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  simpa only [Real.norm_eq_abs, norm_abs_eq_norm] using
    (StrongDual.abs_apply_le_apply_abs (latticePSum_nonneg q φ) x).trans
      (latticePSum_dual_apply_le_of_pairing φ hC hpair (abs_nonneg x))
