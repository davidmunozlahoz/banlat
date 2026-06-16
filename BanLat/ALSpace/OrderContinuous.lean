import BanLat.ALSpace.Dual
import BanLat.OrderContinuous.Nakano

/-!
# Order continuity of AL-spaces

This file records that every AL-space has an order continuous norm, and hence
the resulting order-completeness consequence.
-/

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

private lemma dualUnit_apply_nonneg {x : X} (hx : 0 ≤ x) :
    0 ≤ dualUnit X x := by
  rw [dualUnit_apply_of_nonneg hx]
  exact norm_nonneg x

private lemma dualUnit_apply_mono {x y : X} (hxy : x ≤ y) :
    dualUnit X x ≤ dualUnit X y := by
  have hnonneg : 0 ≤ dualUnit X (y - x) :=
    dualUnit_apply_nonneg (sub_nonneg.mpr hxy)
  rw [map_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

private lemma dist_eq_dist_dualUnit_of_monotone_nonneg {u : ℕ → X}
    (hmono : Monotone u) (n m : ℕ) :
    dist (u n) (u m) = dist (dualUnit X (u n)) (dualUnit X (u m)) := by
  by_cases hnm : n ≤ m
  · have hle : u n ≤ u m := hmono hnm
    have hsub_nn : 0 ≤ u m - u n := sub_nonneg.mpr hle
    have hnorm_sub : ‖u m - u n‖ = dualUnit X (u m) - dualUnit X (u n) := by
      rw [← dualUnit_apply_of_nonneg hsub_nn, map_sub]
    have hdual_mono : dualUnit X (u n) ≤ dualUnit X (u m) :=
      dualUnit_apply_mono hle
    rw [dist_eq_norm, dist_eq_norm, ← norm_neg, neg_sub, hnorm_sub]
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hdual_mono)]
    ring
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hle : u m ≤ u n := hmono hmn
    have hsub_nn : 0 ≤ u n - u m := sub_nonneg.mpr hle
    have hnorm_sub : ‖u n - u m‖ = dualUnit X (u n) - dualUnit X (u m) := by
      rw [← dualUnit_apply_of_nonneg hsub_nn, map_sub]
    have hdual_mono : dualUnit X (u m) ≤ dualUnit X (u n) :=
      dualUnit_apply_mono hle
    rw [dist_eq_norm, dist_eq_norm, hnorm_sub]
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hdual_mono)]

private theorem tendsto_of_monotone_nonneg_bddAbove {u : ℕ → X}
    (hmono : Monotone u) (_hnn : ∀ n, 0 ≤ u n)
    (hbd : BddAbove (Set.range u)) :
    ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
  obtain ⟨w, hw⟩ := hbd
  let a : ℕ → ℝ := fun n => dualUnit X (u n)
  have ha_mono : Monotone a := fun n m hnm =>
    dualUnit_apply_mono (hmono hnm)
  have ha_bdd : BddAbove (Set.range a) := by
    refine ⟨dualUnit X w, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact dualUnit_apply_mono (hw ⟨n, rfl⟩)
  have ha_tend : Filter.Tendsto a Filter.atTop (nhds (⨆ n, a n)) :=
    tendsto_atTop_ciSup ha_mono ha_bdd
  have hu_cauchy : CauchySeq u := by
    have ha_cauchy_seq : CauchySeq a := ha_tend.cauchySeq
    rw [Metric.cauchySeq_iff] at ha_cauchy_seq ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := ha_cauchy_seq ε hε
    exact ⟨N, fun n hn m hm => by
      rw [dist_eq_dist_dualUnit_of_monotone_nonneg hmono]
      exact hN n hn m hm⟩
  obtain ⟨x, hx_tend⟩ := cauchySeq_tendsto_of_complete hu_cauchy
  exact ⟨x, isLUB_of_tendsto_atTop hmono hx_tend, hx_tend⟩

/-- Every AL-space has an order continuous norm. -/
instance instIsOrderContinuousNorm : IsOrderContinuousNorm X := by
  classical
  let banach : BanachLattice X := inferInstance
  letI : SigmaConditionallyCompleteLattice X :=
    sigmaConditionallyCompleteLatticeOfPosSeq X
      (fun hmono hnn hbd =>
        let ⟨x, hx, _⟩ := tendsto_of_monotone_nonneg_bddAbove hmono hnn hbd
        ⟨x, hx⟩)
  let orderedAdd : IsOrderedAddMonoid X := {
    add_le_add_left := fun _ _ h _ => add_le_add_left h _
  }
  letI : IsOrderedAddMonoid X := orderedAdd
  let sigmaOrderContinuous : IsSigmaOrderContinuousNorm X := by
    refine ⟨fun {u} hanti hnn hglb => ?_⟩
    let v : ℕ → X := fun n => u 0 - u n
    have hv_mono : Monotone v := fun n m hnm =>
      sub_le_sub_left (hanti hnm) _
    have hv_nn : ∀ n, 0 ≤ v n := fun n =>
      sub_nonneg.mpr (hanti (Nat.zero_le n))
    have hv_bdd : BddAbove (Set.range v) := by
      refine ⟨u 0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact sub_le_self _ (hnn n)
    obtain ⟨x, hx_lub, hx_tend⟩ :=
      tendsto_of_monotone_nonneg_bddAbove hv_mono hv_nn hv_bdd
    have hub_le : u 0 - x ∈ lowerBounds (Set.range u) := by
      rintro _ ⟨n, rfl⟩
      have h1 : u 0 - u n ≤ x := hx_lub.1 ⟨n, rfl⟩
      exact sub_le_comm.mp h1
    have h_le_zero : u 0 - x ≤ 0 := hglb.2 hub_le
    have hxle : x ≤ u 0 := hx_lub.2 (by
      rintro _ ⟨n, rfl⟩
      exact sub_le_self _ (hnn n))
    have h_ge_zero : (0 : X) ≤ u 0 - x := sub_nonneg.mpr hxle
    have hux_eq : u 0 - x = 0 := le_antisymm h_le_zero h_ge_zero
    have htend : Filter.Tendsto (fun n => u 0 - (u 0 - u n))
        Filter.atTop (nhds (u 0 - x)) :=
      tendsto_const_nhds.sub hx_tend
    have hux : Filter.Tendsto u Filter.atTop (nhds (u 0 - x)) := by
      convert htend using 1
      ext n; abel
    rwa [hux_eq] at hux
  haveI : IsSigmaOrderContinuousNorm X := sigmaOrderContinuous
  exact @BanachLattice.isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice X
    inferInstance inferInstance orderedAdd banach sigmaOrderContinuous

variable [IsOrderContinuousNorm X]

/-- An AL-space with order continuous norm is conditionally complete. -/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice X :=
  BanachLattice.conditionallyCompleteLatticeOf_isOrderContinuousNorm

end ALSpace
