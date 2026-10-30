/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Basic

/-!
# Density character

This file defines the **density character** of a topological space and states
its basic cardinal, attainment and invariance under homeomorphism properties.
It also defines homogeneity of the density character of nontrivial order intervals.
-/

universe u v

namespace TopologicalSpace

/-- The density character of a topological space is the least cardinality of
a dense subset. -/
noncomputable def densityCharacter (X : Type u) [TopologicalSpace X] :
    Cardinal.{u} :=
  sInf {κ | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ}

/-- The density character is always realized by a dense subset. -/
theorem exists_dense_mk_eq_densityCharacter
    (X : Type u) [TopologicalSpace X] :
    ∃ D : Set X, Dense D ∧ Cardinal.mk D = densityCharacter X := by
  unfold densityCharacter
  change sInf {κ | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ} ∈
    {κ | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ}
  exact csInf_mem ⟨Cardinal.mk X, Set.univ, dense_univ, Cardinal.mk_univ⟩

/-- The density character is at most `κ` exactly when there is a dense
subset of cardinality at most `κ`. -/
theorem densityCharacter_le_iff_exists_dense_mk_le
    {X : Type u} [TopologicalSpace X] {κ : Cardinal.{u}} :
    densityCharacter X ≤ κ ↔
      ∃ D : Set X, Dense D ∧ Cardinal.mk D ≤ κ := by
  constructor
  · intro hκ
    obtain ⟨D, hD, hcard⟩ := exists_dense_mk_eq_densityCharacter X
    exact ⟨D, hD, hcard.le.trans hκ⟩
  · rintro ⟨D, hD, hcard⟩
    unfold densityCharacter
    have hmem : Cardinal.mk D ∈
        {κ' | ∃ E : Set X, Dense E ∧ Cardinal.mk E = κ'} :=
      ⟨D, hD, rfl⟩
    exact (csInf_le' hmem).trans hcard

/-- A topological space has an injective dense family indexed by the type
representing its density character. -/
theorem exists_injective_denseRange_densityCharacter
    (X : Type u) [TopologicalSpace X] :
    ∃ f : (densityCharacter X).out → X,
      Function.Injective f ∧ DenseRange f := by
  classical
  obtain ⟨D, hD, hcard⟩ := exists_dense_mk_eq_densityCharacter X
  have hmk : Cardinal.mk ((densityCharacter X).out) = Cardinal.mk D := by
    rw [Cardinal.mk_out]
    exact hcard.symm
  let e : (densityCharacter X).out ≃ D := Classical.choice (Cardinal.eq.mp hmk)
  let f : (densityCharacter X).out → X := fun i ↦ e i
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  · change Dense (Set.range f)
    have hrange : Set.range f = D := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro hx
        let d : D := ⟨x, hx⟩
        refine ⟨e.symm d, ?_⟩
        simp [f, d]
    rw [hrange]
    exact hD

/-- If `densityCharacter(X) = κ`, then `X` has a dense family indexed by the type
underlying the initial ordinal `κ.ord`. -/
theorem exists_denseRange_ord
    (X : Type u) [TopologicalSpace X] (κ : Cardinal.{u})
    (hκ : densityCharacter X = κ) :
    ∃ f : κ.ord.ToType → X, DenseRange f := by
  obtain ⟨D, hD, hDcard⟩ := exists_dense_mk_eq_densityCharacter X
  have hcard : Cardinal.mk κ.ord.ToType = Cardinal.mk D := by
    rw [Cardinal.mk_ord_toType, hDcard, hκ]
  let e : κ.ord.ToType ≃ D := Classical.choice (Cardinal.eq.mp hcard)
  refine ⟨fun i ↦ e i, ?_⟩
  change Dense (Set.range fun i ↦ (e i : X))
  convert hD using 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hx
    exact ⟨e.symm ⟨x, hx⟩, by simp⟩

/-- A dense subset bounds the density character from above. -/
theorem densityCharacter_le_mk_of_dense
    {X : Type u} [TopologicalSpace X] {D : Set X} (hD : Dense D) :
    densityCharacter X ≤ Cardinal.mk D := by
  apply csInf_le'
  exact ⟨D, hD, rfl⟩

/-- Density character does not increase under a continuous surjection. -/
theorem densityCharacter_le_of_continuous_surjective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (hfs : Function.Surjective f) :
    densityCharacter Y ≤ densityCharacter X := by
  unfold densityCharacter
  apply le_csInf
  · exact ⟨Cardinal.mk X, Set.univ, dense_univ, Cardinal.mk_univ⟩
  · rintro κ ⟨D, hD, rfl⟩
    exact (densityCharacter_le_mk_of_dense
      (hfs.denseRange.dense_image hf hD)).trans Cardinal.mk_image_le

/-- The cardinality of a uniformly separated family is at most the density
character of the ambient pseudo-metric space. -/
theorem mk_le_densityCharacter_of_pairwise_le_dist
    {X ι : Type u} [PseudoMetricSpace X]
    (x : ι → X) {ε : ℝ} (hε : 0 < ε)
    (hx : Pairwise fun i j ↦ ε ≤ dist (x i) (x j)) :
    Cardinal.mk ι ≤ densityCharacter X := by
  unfold densityCharacter
  apply le_csInf
  · exact ⟨Cardinal.mk X, Set.univ, dense_univ, Cardinal.mk_univ⟩
  · rintro κ ⟨D, hD, rfl⟩
    choose d hdD hdist using fun i ↦ hD.exists_dist_lt (x i) (half_pos hε)
    apply Cardinal.mk_le_of_injective (f := fun i ↦ ⟨d i, hdD i⟩)
    intro i j hij
    by_contra hne
    have hdij : d i = d j := congrArg Subtype.val hij
    have htri : dist (x i) (x j) ≤ dist (x i) (d i) + dist (d i) (x j) :=
      dist_triangle _ _ _
    have hdj : dist (d i) (x j) = dist (x j) (d j) := by
      rw [hdij, dist_comm]
    have hsum : dist (x i) (d i) + dist (d i) (x j) < ε := by
      rw [hdj]
      linarith [hdist i, hdist j]
    exact (not_lt_of_ge (hx hne)) (htri.trans_lt hsum)

/-- The density character is at most the cardinality of the underlying type. -/
theorem densityCharacter_le_card (X : Type u) [TopologicalSpace X] :
    densityCharacter X ≤ Cardinal.mk X := by
  unfold densityCharacter
  apply csInf_le'
  exact ⟨Set.univ, dense_univ, Cardinal.mk_univ⟩

/-- The density character of a nonempty metric space is at most that of any metric
space into which it embeds topologically. -/
theorem densityCharacter_le_of_isEmbedding
    {X Y : Type u} [MetricSpace X] [MetricSpace Y] [Nonempty X]
    {f : X → Y} (hf : Topology.IsEmbedding f) :
    densityCharacter X ≤ densityCharacter Y := by
  classical
  obtain ⟨D, hD, hcard⟩ := exists_dense_mk_eq_densityCharacter Y
  by_cases hfin : D.Finite
  · have hDu : D = Set.univ := hfin.isClosed.closure_eq.symm.trans hD.closure_eq
    exact (densityCharacter_le_card X).trans
      ((Cardinal.mk_le_of_injective hf.injective).trans_eq
        ((by rw [hDu, Cardinal.mk_univ] : Cardinal.mk Y = Cardinal.mk D).trans hcard))
  · let g (i : D × ℕ) : X :=
      if h : ∃ x, dist (f x) i.1.val < 1 / (i.2 + 1 : ℝ) then h.choose
      else Classical.ofNonempty
    have hg (i : D × ℕ) (h : ∃ x, dist (f x) i.1.val < 1 / (i.2 + 1 : ℝ)) :
        dist (f (g i)) i.1.val < 1 / (i.2 + 1 : ℝ) := by
      simpa only [g, dite_eq_left h] using h.choose_spec
    suffices hdense : DenseRange g by
      have : Infinite D := Set.infinite_coe_iff.mpr hfin
      exact ((densityCharacter_le_mk_of_dense hdense).trans
        Cardinal.mk_range_le).trans_eq
          (by simpa [Cardinal.mk_prod,
            Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk D)] using hcard)
    apply hf.isInducing.dense_iff.mpr
    intro x
    refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hd, hdist⟩ := hD.exists_dist_lt (f x)
      (by positivity : 0 < 1 / (n + 1 : ℝ))
    refine ⟨f (g (⟨d, hd⟩, n)), ⟨g (⟨d, hd⟩, n), ⟨(⟨d, hd⟩, n), rfl⟩, rfl⟩, ?_⟩
    have hnear := hg (⟨d, hd⟩, n) ⟨x, hdist⟩
    linarith [dist_triangle (f x) d (f (g (⟨d, hd⟩, n))),
      dist_comm d (f (g (⟨d, hd⟩, n)))]

/-- The density character of a finite topological space is strictly less than `ℵ₀`. -/
theorem densityCharacter_lt_aleph0 (X : Type u) [TopologicalSpace X] [Finite X] :
    densityCharacter X < Cardinal.aleph0 := by
  exact (densityCharacter_le_card X).trans_lt Cardinal.mk_lt_aleph0

/-- The density character of an infinite T₁ space is infinite. -/
theorem aleph0_le_densityCharacter
    (X : Type u) [TopologicalSpace X] [T1Space X] [Infinite X] :
    Cardinal.aleph0 ≤ densityCharacter X := by
  unfold densityCharacter
  apply le_csInf
  · exact ⟨Cardinal.mk X, Set.univ, dense_univ, Cardinal.mk_univ⟩
  · rintro κ ⟨D, hD, rfl⟩
    rw [Cardinal.aleph0_le_mk_iff, Set.infinite_coe_iff, Set.Infinite]
    intro hDfin
    have hDuniv : D = Set.univ := by
      rw [← hD.closure_eq, hDfin.isClosed.closure_eq]
    exact Set.infinite_univ (hDuniv ▸ hDfin)

/-- The density character of a separable space is at most countable. -/
theorem densityCharacter_le_aleph0 (X : Type u) [TopologicalSpace X]
    [SeparableSpace X] :
    densityCharacter X ≤ Cardinal.aleph0 := by
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense X
  have hmem : Cardinal.mk D ∈
      {κ | ∃ E : Set X, Dense E ∧ Cardinal.mk E = κ} :=
    ⟨D, hDdense, rfl⟩
  exact (csInf_le' hmem).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr hDcount)

/-- A topological space is separable if and only if its density character is
at most countable. -/
theorem separableSpace_iff_densityCharacter_le_aleph0
    (X : Type u) [TopologicalSpace X] :
    SeparableSpace X ↔ densityCharacter X ≤ Cardinal.aleph0 := by
  constructor
  · intro hX
    let := hX
    exact densityCharacter_le_aleph0 X
  · intro hX
    obtain ⟨D, hD, hDcard⟩ :=
      densityCharacter_le_iff_exists_dense_mk_le.mp hX
    exact ⟨⟨D, Cardinal.le_aleph0_iff_set_countable.mp hDcard, hD⟩⟩

/-- A nonempty topological space is separable if and only if it admits a
sequence with dense range. -/
theorem separableSpace_iff_exists_dense_seq
    (X : Type u) [TopologicalSpace X] [Nonempty X] :
    SeparableSpace X ↔ ∃ u : ℕ → X, DenseRange u := by
  constructor
  · intro hX
    let := hX
    exact exists_dense_seq X
  · rintro ⟨u, hu⟩
    exact SeparableSpace.of_denseRange u hu

/-- Homeomorphic spaces have the same density character. -/
theorem densityCharacter_eq_of_homeomorph
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Cardinal.lift.{u} (densityCharacter Y) =
      Cardinal.lift.{v} (densityCharacter X) := by
  apply le_antisymm
  · unfold densityCharacter
    rw [Cardinal.lift_sInf, Cardinal.lift_sInf]
    apply le_csInf
    · refine ⟨Cardinal.lift.{v} (Cardinal.mk X), ?_⟩
      exact ⟨Cardinal.mk X, ⟨Set.univ, dense_univ, Cardinal.mk_univ⟩, rfl⟩
    · rintro κ ⟨κX, ⟨D, hDdense, rfl⟩, rfl⟩
      apply csInf_le'
      refine ⟨Cardinal.mk (e '' D), ⟨e '' D, ?_, rfl⟩, ?_⟩
      · exact e.surjective.denseRange.dense_image e.continuous hDdense
      · rw [Cardinal.mk_image_eq_lift e D e.injective]
  · unfold densityCharacter
    rw [Cardinal.lift_sInf, Cardinal.lift_sInf]
    apply le_csInf
    · refine ⟨Cardinal.lift.{u} (Cardinal.mk Y), ?_⟩
      exact ⟨Cardinal.mk Y, ⟨Set.univ, dense_univ, Cardinal.mk_univ⟩, rfl⟩
    · rintro κ ⟨κY, ⟨D, hDdense, rfl⟩, rfl⟩
      apply csInf_le'
      refine ⟨Cardinal.mk (e.symm '' D), ⟨e.symm '' D, ?_, rfl⟩, ?_⟩
      · exact e.symm.surjective.denseRange.dense_image e.symm.continuous hDdense
      · rw [Cardinal.mk_image_eq_lift e.symm D e.symm.injective]

/-- An ordered topological space is **`κ`-homogeneous on order intervals** if every
nontrivial closed order interval has density character `κ`. -/
def IsOrderIntervalHomogeneous (X : Type u) [TopologicalSpace X] [PartialOrder X]
    (κ : Cardinal.{u}) : Prop :=
  ∀ ⦃a b : X⦄, a < b → densityCharacter (Set.Icc a b) = κ

end TopologicalSpace
