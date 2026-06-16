import BanLat.Substructures.Ideal
import BanLat.OrderUnit
import BanLat.OrderContinuous.Ando
import BanLat.Substructures.Band.Generated
import Mathlib.Topology.Bases

/-!
# Quasi-interior points

A non-negative element `e` of a normed vector lattice `X` is a **quasi-interior
point** (or *topological order unit*) if the principal ideal it generates is
norm-dense in `X`. This notion sits strictly between strong order units (whose
principal ideal is the whole space) and weak order units (whose generated band
is the whole space). This file develops the truncation characterisation by
`x ⊓ n • e`, proves existence in separable Banach lattices, and relates
quasi-interior points to weak order units under order continuity.
-/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

/-- A **quasi-interior point** of a normed vector lattice is a non-negative
element whose principal ideal is norm-dense. -/
def QuasiInteriorPoint (e : X) : Prop :=
  0 ≤ e ∧ Dense ((OrderIdeal.principal e : Set X))

/-- The truncation `x ⊓ (n : ℝ) • e` belongs to the principal ideal of `e`
whenever `0 ≤ x` and `0 ≤ e`. -/
private lemma inf_nsmul_mem_principal {e x : X} (he : 0 ≤ e) (hx : 0 ≤ x) (n : ℕ) :
    x ⊓ (n : ℝ) • e ∈ OrderIdeal.principal e := by
  refine ⟨n, Nat.cast_nonneg n, ?_⟩
  have hne : (0 : X) ≤ (n : ℝ) • e := smul_nonneg (Nat.cast_nonneg n) he
  have h_inf_nn : (0 : X) ≤ x ⊓ (n : ℝ) • e := le_inf hx hne
  rw [abs_of_nonneg h_inf_nn, abs_of_nonneg he]
  exact inf_le_right

/-- Membership in the closure of a principal ideal: in a Banach lattice, a
non-negative element `x` lies in the closure of the principal ideal of `e ≥ 0`
iff the truncations `x ⊓ (n : ℝ) • e` converge to `x` in norm. -/
theorem mem_closure_principal_iff_tendsto_inf [CompleteSpace X]
    {e x : X} (he : 0 ≤ e) (hx : 0 ≤ x) :
    x ∈ closure ((OrderIdeal.principal e : Set X)) ↔
      Filter.Tendsto (fun n : ℕ => x ⊓ (n : ℝ) • e) Filter.atTop (nhds x) := by
  refine ⟨fun hxcl => ?_, fun htend => ?_⟩
  · -- Forward: approximate by elements of the ideal and bound the truncation error.
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Pick `y` in the principal ideal with `‖x - y‖ < ε`; replace by `|y|`.
    obtain ⟨y, hy_mem, hy_dist⟩ :
        ∃ y ∈ (OrderIdeal.principal e : Set X), ‖x - y‖ < ε := by
      rcases Metric.mem_closure_iff.mp hxcl ε hε with ⟨y, hy_mem, hy_dist⟩
      exact ⟨y, hy_mem, by rwa [dist_eq_norm] at hy_dist⟩
    have habs_mem : |y| ∈ OrderIdeal.principal e :=
      OrderIdeal.abs_mem _ hy_mem
    obtain ⟨c, hc, hyc⟩ := habs_mem
    -- Choose `N` with `(N : ℝ) • e ≥ c • e`, i.e. `c ≤ N`.
    obtain ⟨N, hN⟩ := exists_nat_ge c
    refine ⟨N, fun n hn => ?_⟩
    have hne : (0 : X) ≤ (n : ℝ) • e := smul_nonneg (Nat.cast_nonneg n) he
    have h_inf_nn : (0 : X) ≤ x ⊓ (n : ℝ) • e := le_inf hx hne
    -- Bound: `|y| ≤ c • e ≤ N • e ≤ n • e`.
    have hcN : c ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    have habs_le_ne : |y| ≤ (n : ℝ) • e := by
      rw [abs_of_nonneg he, abs_abs] at hyc
      exact hyc.trans (smul_le_smul_of_nonneg_right hcN he)
    -- Hence `x ⊓ |y| ≤ x ⊓ n•e ≤ x`, so `0 ≤ x - x⊓n•e ≤ x - x⊓|y| = (x - |y|)⁺`.
    have h_inf_mono : x ⊓ |y| ≤ x ⊓ (n : ℝ) • e :=
      inf_le_inf_left _ habs_le_ne
    have h_diff_le : x - x ⊓ (n : ℝ) • e ≤ x - x ⊓ |y| :=
      sub_le_sub_left h_inf_mono _
    have h_diff_nn : 0 ≤ x - x ⊓ (n : ℝ) • e := sub_nonneg.mpr inf_le_left
    have h_eq_pos : x - x ⊓ |y| = (x - |y|)⁺ := sub_inf_eq_posPart x |y|
    -- Norm bound via solidity, then `‖(x - |y|)⁺‖ ≤ ‖x - |y|‖ ≤ ‖x - y‖`.
    have h_norm_le : ‖x - x ⊓ (n : ℝ) • e‖ ≤ ‖(x - |y|)⁺‖ := by
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg h_diff_nn, abs_of_nonneg (posPart_nonneg _), ← h_eq_pos]
      exact h_diff_le
    have h_pp_le : ‖(x - |y|)⁺‖ ≤ ‖x - |y|‖ := by
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (posPart_nonneg _)]
      exact sup_le (le_abs_self _) (abs_nonneg _)
    have h_abs_le : ‖x - |y|‖ ≤ ‖x - y‖ := by
      conv_lhs => rw [show x = |x| from (abs_of_nonneg hx).symm]
      exact norm_abs_sub_abs x y
    have hlt : ‖x - x ⊓ (n : ℝ) • e‖ < ε :=
      ((h_norm_le.trans h_pp_le).trans h_abs_le).trans_lt hy_dist
    rw [dist_eq_norm, ← norm_neg, neg_sub]; exact hlt
  · -- Backward: each truncation lies in the ideal, hence so does the limit's closure.
    refine mem_closure_of_tendsto htend ?_
    exact Filter.Eventually.of_forall fun n => inf_nsmul_mem_principal he hx n

/-- A non-negative element `e` of a Banach lattice is a quasi-interior point
iff `x ⊓ (n : ℝ) • e → x` in norm for every non-negative `x`. -/
theorem quasiInteriorPoint_iff_tendsto_inf [CompleteSpace X] {e : X} :
    QuasiInteriorPoint e ↔
      0 ≤ e ∧ ∀ x : X, 0 ≤ x →
        Filter.Tendsto (fun n : ℕ => x ⊓ (n : ℝ) • e) Filter.atTop (nhds x) := by
  refine ⟨fun ⟨he, hd⟩ => ⟨he, fun x hx => ?_⟩, fun ⟨he, h⟩ => ⟨he, ?_⟩⟩
  · exact (mem_closure_principal_iff_tendsto_inf he hx).mp (hd.closure_eq ▸ Set.mem_univ x)
  · -- Show density: every `x` lies in the closure, via `x = x⁺ - x⁻`.
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_forall fun x => ?_
    have hclos_eq :
        closure ((OrderIdeal.principal e : Set X)) =
          ((OrderIdeal.principal e).toSubmodule.topologicalClosure : Set X) :=
      (Submodule.topologicalClosure_coe _).symm
    rw [hclos_eq]
    have hpos_mem : x⁺ ∈ (OrderIdeal.principal e).toSubmodule.topologicalClosure := by
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact (mem_closure_principal_iff_tendsto_inf he (posPart_nonneg _)).mpr
        (h _ (posPart_nonneg _))
    have hneg_mem : x⁻ ∈ (OrderIdeal.principal e).toSubmodule.topologicalClosure := by
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact (mem_closure_principal_iff_tendsto_inf he (negPart_nonneg _)).mpr
        (h _ (negPart_nonneg _))
    have := (OrderIdeal.principal e).toSubmodule.topologicalClosure.sub_mem hpos_mem hneg_mem
    rw [posPart_sub_negPart] at this
    exact this

/-- Every separable Banach lattice admits a quasi-interior point. -/
theorem exists_quasiInteriorPoint_of_separable [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] :
    ∃ e : X, QuasiInteriorPoint e := by
  haveI : Nonempty X := ⟨0⟩
  set u : ℕ → X := TopologicalSpace.denseSeq X with hu_def
  have hu_dense : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  -- Coefficients `c n = 1 / (2^n * (1 + ‖u n‖))`, all in `(0, 1]`.
  set c : ℕ → ℝ := fun n => 1 / (2 ^ n * (1 + ‖u n‖)) with hc_def
  have hc_pos : ∀ n, 0 < c n := fun n => by
    refine div_pos one_pos (mul_pos (pow_pos (by norm_num) n) ?_)
    exact lt_of_lt_of_le one_pos (by linarith [norm_nonneg (u n)])
  have hc_nn : ∀ n, 0 ≤ c n := fun n => (hc_pos n).le
  -- Term of the series.
  set f : ℕ → X := fun n => c n • |u n| with hf_def
  have hf_nn : ∀ n, 0 ≤ f n := fun n => smul_nonneg (hc_nn n) (abs_nonneg _)
  -- Norm bound: `‖f n‖ ≤ (1/2)^n`.
  have hf_bound : ∀ n, ‖f n‖ ≤ (1 / 2 : ℝ) ^ n := fun n => by
    have h1 : ‖f n‖ = c n * ‖u n‖ := by
      rw [hf_def, norm_smul, Real.norm_of_nonneg (hc_nn n), norm_abs_eq_norm]
    rw [h1, hc_def]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀
      (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)
        (lt_of_lt_of_le one_pos (by linarith [norm_nonneg (u n)])))]
    rw [one_div, inv_pow, inv_mul_eq_div, le_div_iff₀ (pow_pos (by norm_num) n)]
    have : ‖u n‖ ≤ 1 + ‖u n‖ := by linarith
    calc ‖u n‖ * 2 ^ n ≤ (1 + ‖u n‖) * 2 ^ n :=
          mul_le_mul_of_nonneg_right this (pow_nonneg (by norm_num) n)
      _ = 2 ^ n * (1 + ‖u n‖) := by ring
  -- Summability of `f` via the geometric majorant.
  have hf_sum : Summable f :=
    Summable.of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) hf_bound
  set e : X := ∑' n, f n with he_def
  have he_nn : 0 ≤ e := tsum_nonneg hf_nn
  refine ⟨e, he_nn, ?_⟩
  -- Density: it suffices that each `u n` lies in the principal ideal of `e`.
  apply Dense.mono _ hu_dense
  rintro _ ⟨n, rfl⟩
  -- `f n ≤ e`, so `|u n| ≤ (c n)⁻¹ • e`, hence `u n ∈ principal e`.
  have hfn_le : f n ≤ e := hf_sum.le_tsum n (fun k _ => hf_nn k)
  refine ⟨(c n)⁻¹, (inv_pos.mpr (hc_pos n)).le, ?_⟩
  rw [abs_of_nonneg he_nn]
  have habs : |u n| = (c n)⁻¹ • f n := by
    rw [hf_def, smul_smul, inv_mul_cancel₀ (hc_pos n).ne', one_smul]
  rw [habs]
  exact smul_le_smul_of_nonneg_left hfn_le (inv_pos.mpr (hc_pos n)).le

/-- In an order continuous normed vector lattice, the notions of weak order
unit and quasi-interior point coincide. -/
theorem quasiInteriorPoint_iff_weakOrderUnit [CompleteSpace X]
    [IsOrderContinuousNorm X] {e : X} :
    QuasiInteriorPoint e ↔ WeakOrderUnit e := by
  letI : BanachLattice X := { }
  refine ⟨fun ⟨he, hd⟩ => ?_, fun hw => ⟨hw.1, ?_⟩⟩
  · -- Forward: density gives `Band.generated {e} = ⊤`.
    rw [weakOrderUnit_iff_generated_singleton_eq_top he]
    refine eq_top_iff.mpr fun x _ => ?_
    -- The band generated by `{e}` is closed; it contains the principal ideal.
    have hprinc_sub :
        ((OrderIdeal.principal e : Set X)) ⊆ ((Band.generated ({e} : Set X) : Set X)) := by
      intro y ⟨c, hc, hyc⟩
      have he_in : e ∈ Band.generated ({e} : Set X) := Band.subset_generated _ rfl
      have hce_mem : c • e ∈ Band.generated ({e} : Set X) :=
        (Band.generated ({e} : Set X)).toSubmodule.smul_mem c he_in
      refine (Band.generated ({e} : Set X)).mem_of_abs_le_abs hce_mem ?_
      rw [abs_of_nonneg he] at hyc
      have hce_nn : (0 : X) ≤ c • e := smul_nonneg hc he
      rw [abs_of_nonneg hce_nn]; exact hyc
    have hsub : closure ((OrderIdeal.principal e : Set X)) ⊆
        ((Band.generated ({e} : Set X) : Set X)) :=
      closure_minimal hprinc_sub (Band.isClosed_coe _)
    have : closure ((OrderIdeal.principal e : Set X)) = Set.univ := hd.closure_eq
    rw [this] at hsub; exact hsub (Set.mem_univ x)
  · -- Backward: the closure of the principal ideal is a band containing `e`.
    obtain ⟨B, hB⟩ := BanachLattice.band_of_isClosed_orderIdeal
      (OrderIdeal.topologicalClosure (OrderIdeal.principal e)) isClosed_closure
    have he_in_B : e ∈ B := by
      rw [← SetLike.mem_coe, hB]
      exact subset_closure (OrderIdeal.self_mem_principal e)
    have hge_le_B : Band.generated ({e} : Set X) ≤ B :=
      Band.generated_le (Set.singleton_subset_iff.mpr he_in_B)
    rw [(weakOrderUnit_iff_generated_singleton_eq_top hw.1).mp hw] at hge_le_B
    intro x
    have hxB : x ∈ B := hge_le_B (Band.mem_top)
    rw [← SetLike.mem_coe, hB] at hxB
    exact hxB
