/-
Authors: Pedro Tradacete
-/

import BanLat.QConcavity

/-!
# q-concavity of quotient Banach lattices

A quotient by a closed order ideal inherits every q-concavity constant of its
ambient Banach lattice. Absolute values of finite quotient families admit positive
lifts with lattice q-sum norms arbitrarily close to the corresponding quotient norm.
-/

open scoped ENNReal Topology

noncomputable section

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

private lemma posPart_sub_le_scaled_abs {a u r : ℝ} (hu : 0 ≤ u) (hur : u < r)
    (ha : |a| ≤ r) : (a - u)⁺ ≤ ((r - u) / r) * |a| := by
  rw [posPart_def, sup_le_iff]
  refine ⟨?_, mul_nonneg (div_nonneg (sub_nonneg.mpr hur.le) (hu.trans hur.le))
    (abs_nonneg a)⟩
  rw [div_mul_eq_mul_div, le_div_iff₀ (hu.trans_lt hur)]
  nlinarith [mul_nonneg (hu.trans hur.le) (sub_nonneg.mpr (le_abs_self a)),
    mul_nonneg hu (sub_nonneg.mpr ha)]

private lemma norm_toLp_posPart_sub_le {n : ℕ} (a : Fin n → ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    ‖WithLp.toLp q (fun i ↦ (a i - u)⁺)‖ ≤ (‖WithLp.toLp q a‖ - u)⁺ := by
  by_cases h : ‖WithLp.toLp q a‖ ≤ u
  · have ha (i : Fin n) : (a i - u)⁺ = 0 :=
      posPart_eq_zero.mpr (sub_nonpos.mpr ((le_abs_self (a i)).trans
        ((PiLp.norm_apply_le (WithLp.toLp q a) i).trans h)))
    simpa only [ha, show (fun _ : Fin n ↦ (0 : ℝ)) = 0 from rfl,
      WithLp.toLp_zero, norm_zero] using posPart_nonneg (‖WithLp.toLp q a‖ - u)
  · have hr : 0 < ‖WithLp.toLp q a‖ := hu.trans_lt (lt_of_not_ge h)
    have hc : 0 ≤ (‖WithLp.toLp q a‖ - u) / ‖WithLp.toLp q a‖ :=
      div_nonneg (sub_nonneg.mpr (le_of_not_ge h)) hr.le
    have hn : ‖WithLp.toLp q (fun i ↦ (a i - u)⁺)‖ ≤
        ‖((‖WithLp.toLp q a‖ - u) / ‖WithLp.toLp q a‖) • |WithLp.toLp q a|‖ := by
      apply norm_le_norm_of_abs_le_abs
      intro i
      change |(a i - u)⁺| ≤ |(((‖WithLp.toLp q a‖ - u) / ‖WithLp.toLp q a‖) * |a i|)|
      rw [abs_of_nonneg (posPart_nonneg _), abs_of_nonneg (mul_nonneg hc (abs_nonneg _))]
      exact posPart_sub_le_scaled_abs hu (lt_of_not_ge h)
        (PiLp.norm_apply_le (WithLp.toLp q a) i)
    simpa only [norm_smul_of_nonneg hc, norm_abs_eq_norm, div_mul_cancel₀ _ hr.ne',
      posPart_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))] using hn

private lemma latticePSum_posPart_sub_le {n : ℕ} (x : Fin n → X) {u : X}
    (hu : 0 ≤ u) :
    latticePSum q (fun i ↦ (x i - u)⁺) ≤ (latticePSum q x - u)⁺ := by
  let := isUniformlyCompleteVectorLattice_of_banachLattice X
  let g : Fin n → posHomFunctions (n + 1) := fun i ↦ PosHomFunction.coordinate i.succ
  have h : PosHomFunction.comp (pSumFunction q n)
      (fun i ↦ (g i - (PosHomFunction.coordinate 0)⁺)⁺) ≤
      (PosHomFunction.comp (pSumFunction q n) g - (PosHomFunction.coordinate 0)⁺)⁺ :=
    fun a ↦ norm_toLp_posPart_sub_le (fun i ↦ a i.succ) (posPart_nonneg (a 0))
  simpa only [← PosHomFunction.functionalCalculus_comp, VecLatHom.map_posPart, map_sub,
    g, PosHomFunction.functionalCalculus_coordinate, Fin.cons_succ, Fin.cons_zero,
    posPart_of_nonneg hu, latticePSum] using
      (PosHomFunction.functionalCalculus (Fin.cons u x)).monotone h

/-- A finite family in a quotient admits lifts of its absolute values whose
lattice q-sum norm is arbitrarily close to the quotient lattice q-sum norm. -/
private lemma exists_lifts_abs_latticePSum_norm_lt (J : OrderIdeal X)
    (hJ : IsClosed (J : Set X)) {n : ℕ}
    (x : Fin n → X ⧸ J.toSubmodule) {δ : ℝ} (hδ : 0 < δ) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∃ a : Fin n → X, (∀ i, J.mkQ (a i) = |x i|) ∧
      ‖latticePSum q a‖ < ‖latticePSum q x‖ + δ := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  choose a _ ha using fun i ↦ J.lift_pos (abs_nonneg (x i))
  obtain ⟨z, hz, hz_norm⟩ := Submodule.Quotient.norm_mk_lt (latticePSum q x) hδ
  have hs : J.mkQ (latticePSum q a) = latticePSum q x := by
    simpa only [OrderIdeal.mkQVecLatHom_apply, ha, latticePSum_abs] using
      latticePSum_map q J.mkQVecLatHom a
  have hzabs : J.mkQ |z| = latticePSum q x := by
    simp only [OrderIdeal.mkQ_abs, show J.mkQ z = latticePSum q x from hz,
      abs_of_nonneg (latticePSum_nonneg q x)]
  let u := (latticePSum q a - |z|)⁺
  have hu : J.mkQ u = 0 := by
    change J.mkQVecLatHom (latticePSum q a - |z|)⁺ = 0
    rw [VecLatHom.map_posPart, map_sub, OrderIdeal.mkQVecLatHom_apply,
      OrderIdeal.mkQVecLatHom_apply, hs, hzabs, sub_self, posPart_zero]
  refine ⟨fun i ↦ (a i - u)⁺, ?_, ?_⟩
  · intro i
    change J.mkQVecLatHom (a i - u)⁺ = |x i|
    rw [VecLatHom.map_posPart, map_sub, OrderIdeal.mkQVecLatHom_apply,
      OrderIdeal.mkQVecLatHom_apply, ha, hu, sub_zero, posPart_of_nonneg (abs_nonneg _)]
  · refine (norm_le_norm_of_abs_le_abs ?_).trans_lt hz_norm
    rw [abs_of_nonneg (latticePSum_nonneg q _)]
    refine (latticePSum_posPart_sub_le a (posPart_nonneg _)).trans ?_
    rw [← inf_eq_sub_posPart_sub, posPart_def]
    exact sup_le inf_le_right (abs_nonneg z)

private lemma norm_toLp_le_of_quotient_lifts {C δ : ℝ} (hC : IsQConcaveWith q C X)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) {n : ℕ}
    (x : Fin n → X ⧸ J.toSubmodule) (a : Fin n → X)
    (ha : ∀ i, J.mkQ (a i) = |x i|) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ‖latticePSum q a‖ ≤ ‖latticePSum q x‖ + δ →
      ‖WithLp.toLp q (fun i ↦ ‖x i‖)‖ ≤ C * (‖latticePSum q x‖ + δ) := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  intro hbound
  have hnorm (i : Fin n) : ‖x i‖ ≤ ‖a i‖ := by
    rw [← norm_abs_eq_norm (x i), ← ha i]
    exact Submodule.Quotient.norm_mk_le J.toSubmodule (a i)
  have hsum : ‖WithLp.toLp q (fun i ↦ ‖x i‖)‖ ≤ ‖WithLp.toLp q (fun i ↦ ‖a i‖)‖ := by
    apply norm_le_norm_of_abs_le_abs
    change ∀ i, |‖x i‖| ≤ |‖a i‖|
    simpa only [abs_norm] using hnorm
  exact hsum.trans ((hC.2 n a).trans (mul_le_mul_of_nonneg_left hbound hC.1))

/-- A quotient by a closed order ideal inherits every q-concavity constant
of the ambient Banach lattice. -/
theorem ConcaveWith.id_quotient {C : ℝ} (hC : IsQConcaveWith q C X)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    IsQConcaveWith q C (X ⧸ J.toSubmodule) := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  refine ⟨hC.1, fun n x ↦ ?_⟩
  have hcont : Continuous (fun δ : ℝ ↦ C * (‖latticePSum q x‖ + δ)) :=
    continuous_const.mul (continuous_const.add continuous_id)
  have hlim := (hcont.tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  obtain ⟨a, ha, hbound⟩ := exists_lifts_abs_latticePSum_norm_lt (q := q) J hJ x hδ
  exact norm_toLp_le_of_quotient_lifts hC J hJ x a ha hbound.le

/-- Every quotient of a q-concave Banach lattice by a closed order ideal is q-concave. -/
theorem IsQConcave.quotient (hX : IsQConcave q X)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    IsQConcave q (X ⧸ J.toSubmodule) :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  hX.elim fun C hC ↦ ⟨C, hC.id_quotient J hJ⟩

/-- Taking a quotient by a closed order ideal cannot increase the optimal
q-concavity constant of a q-concave Banach lattice. -/
theorem IsQConcave.concavityConstant_quotient_le (hX : IsQConcave q X)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    qConcavityConstant q (X ⧸ J.toSubmodule) ≤ qConcavityConstant q X :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  ((IsQConcaveOp.concavityConstant_spec hX).id_quotient J hJ).concavityConstant_le
