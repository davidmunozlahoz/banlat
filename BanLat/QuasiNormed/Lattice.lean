/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Convergences.Uniform
import BanLat.LocallySolid.Basic
import BanLat.QuasiNormed.Complete

/-!
# Quasi-normed vector and Banach lattices

This file introduces solid quasi-seminorms, **quasi-normed vector and Banach lattices.**
It develops their induced locally solid topology and proves that quasi-Banach lattices
are uniformly complete as vector lattices. It also establishes the following
compatibility results with the normed theory:
* every solid norm is a solid quasi-seminorm;
* every normed vector lattice is a quasi-normed vector lattice;
* every Banach lattice is a quasi-Banach lattice.
-/

open Filter Set

open scoped Topology

-- MATHLIB: the `solid` field of Mathlib's `HasSolidNorm` only needs
-- `[Norm α] [AddGroup α] [Lattice α]`. Weakening its assumptions to these, and keeping
-- `NormedAddCommGroup` only for lemmas using the triangle inequality, would make this class
-- and its solidity-only lemmas below redundant.
/-- A quasi-seminorm is **solid** if domination of absolute values implies
domination of quasi-seminorms. -/
class HasSolidQuasiSeminorm (E : Type*) [AddCommGroup E] [Lattice E] [Norm E]
    [IsQuasiSeminorm E] : Prop where
  solid : ∀ ⦃x y : E⦄, |x| ≤ |y| → ‖x‖ ≤ ‖y‖

namespace HasSolidQuasiSeminorm

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [Norm E]
  [IsQuasiSeminorm E] [HasSolidQuasiSeminorm E]

omit [IsOrderedAddMonoid E] in
/-- A solid quasi-seminorm is monotone. -/
theorem norm_le_norm_of_abs_le_abs {x y : E} (h : |x| ≤ |y|) : ‖x‖ ≤ ‖y‖ :=
  HasSolidQuasiSeminorm.solid h

omit [IsOrderedAddMonoid E] in
/-- Every open ball centered at zero for a solid quasi-seminorm is a solid set. -/
theorem isSolid_ball (r : ℝ) :
    LatticeOrderedAddCommGroup.IsSolid (IsQuasiSeminorm.ball (0 : E) r) := by
  intro x hx y hxy
  rw [IsQuasiSeminorm.mem_ball] at hx ⊢
  simp only [sub_zero] at hx ⊢
  exact (HasSolidQuasiSeminorm.solid hxy).trans_lt hx

/-- For any solid quasi-seminorm, `‖|x|‖ = ‖x‖`. -/
theorem norm_abs_eq_norm (x : E) : ‖|x|‖ = ‖x‖ := by
  exact (HasSolidQuasiSeminorm.solid (abs_abs x).le).antisymm
    (HasSolidQuasiSeminorm.solid (abs_abs x).symm.le)

/-- The quasi-seminorm of the positive part is bounded by the quasi-seminorm. -/
theorem norm_posPart_le (x : E) : ‖x⁺‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (posPart_nonneg x)]
  exact posPart_le_abs x

/-- The quasi-seminorm of the negative part is bounded by the quasi-seminorm. -/
theorem norm_negPart_le (x : E) : ‖x⁻‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (negPart_nonneg x)]
  exact negPart_le_abs x

end HasSolidQuasiSeminorm

/-- A **quasi-normed vector lattice** is a real vector lattice equipped
with a homogeneous solid quasi-norm. -/
class QuasiNormedVectorLattice (E : Type*) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [Norm E] [IsQuasiNorm E] extends VectorLattice E,
      HasSolidQuasiSeminorm E, NormSMulClass ℝ E

namespace HasSolidQuasiSeminorm

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
  [Norm E] [IsQuasiSeminorm E] [NormSMulClass ℝ E] [HasSolidQuasiSeminorm E]

/-- The topology induced by a solid homogeneous quasi-seminorm is locally solid. -/
instance instIsLocallySolidVectorLattice :
    @IsLocallySolidVectorLattice E _ _ _ _ (IsQuasiSeminorm.topology E) := by
  let : TopologicalSpace E := IsQuasiSeminorm.topology E
  have : IsTopologicalAddGroup E :=
    (IsQuasiSeminorm.addGroupFilterBasis E).isTopologicalAddGroup
  have : ContinuousSMul ℝ E := IsQuasiSeminorm.continuousSMul
  refine { hasBasis_solid := ?_ }
  refine IsQuasiSeminorm.nhds_zero_hasBasis.to_hasBasis ?_ ?_
  · intro r hr
    refine ⟨IsQuasiSeminorm.ball 0 r, ?_, Set.Subset.rfl⟩
    exact ⟨IsQuasiSeminorm.nhds_zero_hasBasis.mem_of_mem hr,
      HasSolidQuasiSeminorm.isSolid_ball r⟩
  · intro s hs
    exact IsQuasiSeminorm.nhds_zero_hasBasis.mem_iff.mp hs.1

end HasSolidQuasiSeminorm

namespace QuasiNormedVectorLattice

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [Norm E]
  [IsQuasiNorm E] [QuasiNormedVectorLattice E]

/-- A quasi-normed vector lattice is a quasi-normed space. -/
instance instQuasiNormedSpace : QuasiNormedSpace ℝ E where

/-- Every quasi-normed vector lattice is Archimedean. -/
instance (priority := 100) instIsVLArchimedean : IsVLArchimedean E := by
  let : TopologicalSpace E := IsQuasiSeminorm.topology E
  exact isVLArchimedean_of_t2_locallySolidVectorLattice (E := E)

/-- The order relation of a quasi-normed vector lattice is closed in its induced topology. -/
instance (priority := 100) instOrderClosedTopology :
    @OrderClosedTopology E (IsQuasiSeminorm.topology E) _ := by
  let : TopologicalSpace E := IsQuasiSeminorm.topology E
  exact ⟨isClosed_le_of_isClosed_nonneg
    (isClosed_nonneg_cone_of_t2_locallySolidVectorLattice (E := E))⟩

end QuasiNormedVectorLattice

/-- A **quasi-Banach lattice** is a quasi-normed vector lattice that is complete
for the topology associated to its quasi-norm. -/
class QuasiBanachLattice (E : Type*) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [Norm E] [IsQuasiNorm E] extends QuasiNormedVectorLattice E,
      @CompleteSpace E (IsQuasiSeminorm.uniformSpace E)

namespace QuasiBanachLattice

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [Norm E]
  [IsQuasiNorm E] [QuasiBanachLattice E]

/-- A quasi-Banach lattice is a quasi-Banach space over `ℝ`. -/
instance instQuasiBanachSpace : QuasiBanachSpace ℝ E where

/-- A gauge-norm bound on the difference of two elements of a principal ideal yields the
corresponding order bound by its nonnegative generator. -/
private theorem abs_sub_le_of_gaugeNorm_le {e x y : E} (he : 0 ≤ e)
    (hx : x ∈ OrderIdeal.principal e) (hy : y ∈ OrderIdeal.principal e) {c : ℝ}
    (hxy : OrderIdeal.gaugeNorm e (x - y) ≤ c) :
    |x - y| ≤ c • e := by
  calc
    |x - y| ≤ OrderIdeal.gaugeNorm e (x - y) • |e| :=
      OrderIdeal.abs_le_gaugeNorm_smul_abs e
        ((OrderIdeal.principal e).toSubmodule.sub_mem hx hy)
    _ ≤ c • |e| :=
      smul_le_smul_of_nonneg_right hxy (abs_nonneg e)
    _ = c • e := by rw [abs_of_nonneg he]

/-- The ambient quasi-norm of an element of a principal ideal is bounded by the product of
the generator's quasi-norm and the element's gauge norm. -/
private theorem norm_coe_le_norm_generator_mul_gauge {e : E}
    (x : ↥(OrderIdeal.principalSubmodule e)) :
    ‖(x : E)‖ ≤ ‖e‖ * OrderIdeal.gaugeNorm e (x : E) := by
  have hnonneg : 0 ≤ OrderIdeal.gaugeNorm e (x : E) :=
    OrderIdeal.gaugeNorm_nonneg e (x : E)
  calc
    ‖(x : E)‖ ≤ ‖OrderIdeal.gaugeNorm e (x : E) • |e|‖ := by
      apply HasSolidQuasiSeminorm.norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (smul_nonneg hnonneg (abs_nonneg e))]
      exact OrderIdeal.abs_le_gaugeNorm_smul_abs e x.2
    _ = ‖OrderIdeal.gaugeNorm e (x : E)‖ * ‖|e|‖ := norm_smul _ _
    _ = ‖e‖ * OrderIdeal.gaugeNorm e (x : E) := by
      rw [Real.norm_of_nonneg hnonneg, HasSolidQuasiSeminorm.norm_abs_eq_norm, mul_comm]

omit [Norm E] [IsQuasiNorm E] [QuasiBanachLattice E] in
/-- The norm of the standard normed-group structure on a principal ideal is its gauge norm. -/
private theorem norm_principal_eq_gauge [VectorLattice E] [IsVLArchimedean E] {e : E}
    (x : ↥(OrderIdeal.principalSubmodule e)) :
    letI := OrderIdeal.principalNormedAddCommGroup e
    ‖x‖ = OrderIdeal.gaugeNorm e (x : E) := by
  let := OrderIdeal.principalNormedAddCommGroup e
  rfl

/-- The distance on a principal ideal induced by its standard normed-group structure is the
gauge norm of the ambient difference. -/
private theorem dist_principal_eq_gauge {e : E}
    (x y : ↥(OrderIdeal.principalSubmodule e)) :
    letI := OrderIdeal.principalNormedAddCommGroup e
    letI : PseudoMetricSpace ↥(OrderIdeal.principalSubmodule e) :=
      @SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _
          (OrderIdeal.principalNormedAddCommGroup e))
    dist x y = OrderIdeal.gaugeNorm e ((x : E) - (y : E)) := by
  let := OrderIdeal.principalNormedAddCommGroup e
  let : PseudoMetricSpace ↥(OrderIdeal.principalSubmodule e) :=
    @SeminormedAddCommGroup.toPseudoMetricSpace _
      (@NormedAddCommGroup.toSeminormedAddCommGroup _
        (OrderIdeal.principalNormedAddCommGroup e))
  calc
    dist x y = ‖x - y‖ := @dist_eq_norm _
      (@NormedAddCommGroup.toSeminormedAddCommGroup _
        (OrderIdeal.principalNormedAddCommGroup e)) x y
    _ = OrderIdeal.gaugeNorm e ((x : E) - (y : E)) :=
      norm_principal_eq_gauge (x - y)

/-- The principal ideal generated by a strictly positive element of a quasi-Banach lattice is
complete for its gauge norm. -/
theorem completeSpace_principal (e : E) (he : 0 < e) :
    @CompleteSpace ↥(OrderIdeal.principalSubmodule e)
      (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (OrderIdeal.principalNormedAddCommGroup e)))) := by
  let : UniformSpace E := IsQuasiSeminorm.uniformSpace E
  have : IsUniformAddGroup E :=
    (IsQuasiSeminorm.addGroupFilterBasis E).isUniformAddGroup
  let := OrderIdeal.principalNormedAddCommGroup e
  let Y := ↥(OrderIdeal.principalSubmodule e)
  let : PseudoMetricSpace Y :=
    @SeminormedAddCommGroup.toPseudoMetricSpace Y
      (@NormedAddCommGroup.toSeminormedAddCommGroup Y
        (OrderIdeal.principalNormedAddCommGroup e))
  refine Metric.complete_of_cauchySeq_tendsto (α := Y) fun u hu ↦ ?_
  have hnorme_pos : 0 < ‖e‖ := IsQuasiNorm.norm_pos (ne_of_gt he)
  have hu_ambient :
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖(u n : E) - (u m : E)‖ < ε := by
    rw [Metric.cauchySeq_iff] at hu
    intro ε hε
    obtain ⟨N, hN⟩ := hu (ε / ‖e‖) (div_pos hε hnorme_pos)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hdist := hN n hn m hm
    have hdist_gauge :
        OrderIdeal.gaugeNorm e ((u n : E) - (u m : E)) < ε / ‖e‖ := by
      have heq : dist (u n) (u m) =
          OrderIdeal.gaugeNorm e ((u n : E) - (u m : E)) := by
        simpa only using (dist_principal_eq_gauge (u n) (u m))
      rwa [heq] at hdist
    have hle : ‖(u n : E) - (u m : E)‖ ≤
        ‖e‖ * OrderIdeal.gaugeNorm e ((u n : E) - (u m : E)) :=
      norm_coe_le_norm_generator_mul_gauge (e := e) (u n - u m)
    have hmul : ‖e‖ * OrderIdeal.gaugeNorm e ((u n : E) - (u m : E)) <
        ‖e‖ * (ε / ‖e‖) :=
      mul_lt_mul_of_pos_left hdist_gauge hnorme_pos
    have htarget : ‖e‖ * (ε / ‖e‖) = ε := by
      field_simp [ne_of_gt hnorme_pos]
    exact hle.trans_lt (by rwa [htarget] at hmul)
  obtain ⟨x, hx_norm⟩ :=
    IsQuasiSeminorm.cauchySeq_tendsto (u := fun n ↦ (u n : E)) hu_ambient
  have hx_tend : Filter.Tendsto (fun n ↦ (u n : E)) Filter.atTop (nhds x) :=
    IsQuasiSeminorm.tendsto_nhds_iff.mpr hx_norm
  have habs_cont : Continuous (|·| : E → E) :=
    (isLocallySolidVectorLattice_iff_uniformContinuous_abs.mp inferInstance).continuous
  have hx_mem : x ∈ OrderIdeal.principalSubmodule e := by
    rw [Metric.cauchySeq_iff] at hu
    obtain ⟨N, hN⟩ := hu 1 zero_lt_one
    have htail : ∀ᶠ n in Filter.atTop,
        |(u n : E) - (u N : E)| ≤ (1 : ℝ) • e := by
      filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ hn⟩] with n hn
      have hdist := hN n hn N le_rfl
      apply abs_sub_le_of_gaugeNorm_le he.le (u n).2 (u N).2
      apply le_of_lt
      have heq : dist (u n) (u N) =
          OrderIdeal.gaugeNorm e ((u n : E) - (u N : E)) := by
        simpa only using (dist_principal_eq_gauge (u n) (u N))
      rwa [heq] at hdist
    have hdiff_tend :
        Filter.Tendsto (fun n ↦ (u n : E) - (u N : E)) Filter.atTop
          (nhds (x - (u N : E))) :=
      hx_tend.sub tendsto_const_nhds
    have habs_tend :
        Filter.Tendsto (fun n ↦ |(u n : E) - (u N : E)|) Filter.atTop
          (nhds |x - (u N : E)|) :=
      (habs_cont.tendsto _).comp hdiff_tend
    have hlim : |x - (u N : E)| ≤ (1 : ℝ) • e :=
      le_of_tendsto_of_tendsto habs_tend tendsto_const_nhds htail
    have hdiff_mem : x - (u N : E) ∈ OrderIdeal.principal e :=
      ⟨1, zero_le_one, by simpa [abs_of_nonneg he.le] using hlim⟩
    have hadd_mem :
        (x - (u N : E)) + (u N : E) ∈ OrderIdeal.principalSubmodule e :=
      (OrderIdeal.principal e).toSubmodule.add_mem hdiff_mem (u N).2
    simpa using hadd_mem
  refine ⟨⟨x, hx_mem⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨N, hN⟩ := hu (ε / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have htail : ∀ᶠ m in Filter.atTop,
      |(u m : E) - (u n : E)| ≤ (ε / 2) • e := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun m hm ↦ hm⟩] with m hm
    have hdist := hN m hm n hn
    apply abs_sub_le_of_gaugeNorm_le he.le (u m).2 (u n).2
    apply le_of_lt
    have heq : dist (u m) (u n) =
        OrderIdeal.gaugeNorm e ((u m : E) - (u n : E)) := by
      simpa only using (dist_principal_eq_gauge (u m) (u n))
    rwa [heq] at hdist
  have hdiff_tend :
      Filter.Tendsto (fun m ↦ (u m : E) - (u n : E)) Filter.atTop
        (nhds (x - (u n : E))) :=
    hx_tend.sub tendsto_const_nhds
  have habs_tend :
      Filter.Tendsto (fun m ↦ |(u m : E) - (u n : E)|) Filter.atTop
        (nhds |x - (u n : E)|) :=
    (habs_cont.tendsto _).comp hdiff_tend
  have horder : |x - (u n : E)| ≤ (ε / 2) • e :=
    le_of_tendsto_of_tendsto habs_tend tendsto_const_nhds htail
  have hgauge : OrderIdeal.gaugeNorm e ((u n : E) - x) ≤ ε / 2 := by
    rw [show (u n : E) - x = -(x - (u n : E)) by abel,
      OrderIdeal.gaugeNorm_neg]
    exact OrderIdeal.gaugeNorm_le_of_abs_le e (by linarith) (by
      simpa [abs_of_nonneg he.le] using horder)
  have hgauge_lt : OrderIdeal.gaugeNorm e ((u n : E) - x) < ε := by
    linarith
  have heq : dist (u n) ⟨x, hx_mem⟩ =
      OrderIdeal.gaugeNorm e ((u n : E) - x) := by
    simpa only using (dist_principal_eq_gauge (u n) ⟨x, hx_mem⟩)
  rwa [heq]

end QuasiBanachLattice

/-- Every quasi-Banach lattice is uniformly complete as a vector lattice. -/
instance (priority := 100) QuasiBanachLattice.toIsUniformlyCompleteVectorLattice
    (E : Type*) [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [Norm E]
    [IsQuasiNorm E] [QuasiBanachLattice E] : IsUniformlyCompleteVectorLattice E where
  complete_principal e he := QuasiBanachLattice.completeSpace_principal e he

/-- A solid norm is a solid quasi-seminorm. -/
instance (priority := 100) HasSolidNorm.toHasSolidQuasiSeminorm (E : Type*)
    [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] : HasSolidQuasiSeminorm E where
  solid := HasSolidNorm.solid

/-- Every normed vector lattice is a quasi-normed vector lattice. -/
instance (priority := 100) NormedVectorLattice.toQuasiNormedVectorLattice (E : Type*)
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [NormedVectorLattice E] : QuasiNormedVectorLattice E where

/-- Every Banach lattice is a quasi-Banach lattice. -/
instance (priority := 100) BanachLattice.toQuasiBanachLattice (E : Type*)
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [BanachLattice E] : QuasiBanachLattice E where
  toQuasiNormedVectorLattice := NormedVectorLattice.toQuasiNormedVectorLattice E
  toCompleteSpace :=
    IsQuasiSeminorm.instQuasiSeminormCompleteSpaceOfCompleteSpace E

/-- A normed vector lattice is locally solid in its norm topology. -/
instance (priority := 100) NormedVectorLattice.toIsLocallySolidVectorLattice (E : Type*)
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [NormedVectorLattice E] : IsLocallySolidVectorLattice E := by
  have h : @IsLocallySolidVectorLattice E _ _ _ _ (IsQuasiSeminorm.topology E) :=
    inferInstance
  rw [IsQuasiSeminorm.topology_eq E] at h
  exact h
