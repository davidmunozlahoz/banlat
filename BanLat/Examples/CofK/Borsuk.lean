/-
Authors: Javier Laguna-Ricart, Alberto Salguero-Alarcón
-/

import BanLat.Examples.CofK.Basic
import BanLat.Operators.Positive
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Positive extension operators

*Borsuk's theorem*: continuous real functions on a nonempty closed subset
of a compact metrizable space admit a positive unital linear extension operator.
A partition of unity on the complement gives extensions depending linearly on
the original functions.
-/

open Set Topology

namespace ContinuousMap

noncomputable section

variable {K : Type*} [MetricSpace K] {s : Set K}

/- A *distance lemma* choosing points that attains the distance to a certain closed set.
This will be used to show that `extensionValue` provides a continuous function. -/
private lemma sampling_dist_le {i z x p : K} (hx : x ∈ s)
    (hp : Metric.infDist i s = dist i p) (hz : dist i z < Metric.infDist i s / 2) :
    dist p x ≤ 4 * dist z x := by
  have hi := Metric.infDist_le_dist_of_mem (x := i) hx
  have hiz := dist_triangle i z x
  have hpx := dist_triangle p i x
  rw [dist_comm p i, ← hp] at hpx
  linarith

/- If `s` is a nonempty closed subset of a compact metric space `K`, there is
a partition of unity on `K \ s` subordinate to balls centered at `i` with radius
half the distance from `i` to `s`, together with nearest points `a i` in `s`
satisfying the *distance lemma*. -/
private lemma exists_extension_weights [CompactSpace K] (hs : IsClosed s)
    (hne : s.Nonempty) :
    ∃ (a : ↥(sᶜ) → s) (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ),
      ∀ i z : ↥(sᶜ), ρ i z ≠ 0 → ∀ x : s,
        dist (a i : K) x ≤ 4 * dist (z : K) x := by
  choose a ha_mem ha using fun i : ↥(sᶜ) ↦
    hs.isCompact.exists_infDist_eq_dist hne (i : K)
  have hpos (i : ↥(sᶜ)) : 0 < Metric.infDist (i : K) s :=
    (hs.notMem_iff_infDist_pos hne).mp i.property
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : ↥(sᶜ) ↦ Metric.ball i (Metric.infDist (i : K) s / 2))
    (fun _ ↦ Metric.isOpen_ball)
    (fun z _ ↦ mem_iUnion.mpr ⟨z, Metric.mem_ball_self (half_pos (hpos z))⟩)
  refine ⟨fun i ↦ ⟨a i, ha_mem i⟩, ρ, ?_⟩
  intro i z hz x
  have hzi := Metric.mem_ball.mp (hρ i (subset_closure hz))
  exact sampling_dist_le x.property (ha i)
    (by simpa only [Subtype.dist_eq, dist_comm] using hzi)

open scoped Classical in
private def extensionValue (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ) (f : C(s, ℝ)) (x : K) : ℝ :=
  if hx : x ∈ s then f ⟨x, hx⟩ else ∑ᶠ i, ρ i ⟨x, hx⟩ • f (a i)

open scoped Classical in
/- For any `f` continuous on `s`, the `extensionValue` `Ef` is continuous at points of `s`.
Given a point `x` in `s` and a close point `z` in `K \ s`, the difference `|Ef(x)-Ef(z)|`
is bounded by a convex combination of `|f(x)-f(a i)|` for various `i`.
The *distance lemma* shows that such values are close. -/
private lemma extensionValue_continuousAt_mem (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ)
    (hnear : ∀ i z : ↥(sᶜ), ρ i z ≠ 0 → ∀ x : s,
      dist (a i : K) x ≤ 4 * dist (z : K) x)
    (f : C(s, ℝ)) (x : s) : ContinuousAt (extensionValue a ρ f) (x : K) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ :=
    (Metric.continuousAt_iff (a := x)).mp f.continuous.continuousAt ε hε
  refine ⟨δ / 4, div_pos hδ (by norm_num), fun {z} hz ↦ ?_⟩
  by_cases hzs : z ∈ s
  · simpa only [extensionValue, dite_eq_left hzs, dite_eq_left x.property] using
      @hfδ ⟨z, hzs⟩ (hz.trans (by linarith))
  · simpa only [extensionValue, dite_eq_right hzs, dite_eq_left x.property, Metric.mem_ball] using
      ρ.finsum_smul_mem_convex (g := fun i _ ↦ f (a i)) (x := ⟨z, hzs⟩)
        (mem_univ _) (fun i hi ↦ hfδ ((hnear i ⟨z, hzs⟩ hi x).trans_lt (by linarith)))
        (convex_ball (f x) ε)

/- The `extensionValue` `Ef` is continuous outside of s. -/
private lemma extensionValue_continuous_compl (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ) (f : C(s, ℝ)) :
    Continuous (fun z : ↥(sᶜ) ↦ extensionValue a ρ f z) := by
  convert ρ.continuous_finsum_smul (g := fun i _ ↦ f (a i))
    (fun _ _ _ ↦ continuousAt_const) using 1
  funext z
  simp only [extensionValue, dite_eq_right z.property]

private lemma extensionValue_continuous (hs : IsClosed s) (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ)
    (hnear : ∀ i z : ↥(sᶜ), ρ i z ≠ 0 → ∀ x : s,
      dist (a i : K) x ≤ 4 * dist (z : K) x)
    (f : C(s, ℝ)) : Continuous (extensionValue a ρ f) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  exact (Classical.em (x ∈ s)).elim
    (fun hx ↦ extensionValue_continuousAt_mem a ρ hnear f ⟨x, hx⟩)
    (fun hx ↦ (hs.isOpen_compl.isOpenEmbedding_subtypeVal.continuousAt_iff
      (x := ⟨x, hx⟩)).mp (extensionValue_continuous_compl a ρ f).continuousAt)

open scoped Classical in
private lemma extensionValue_add (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ) (f g : C(s, ℝ)) :
    extensionValue a ρ (f + g) = extensionValue a ρ f + extensionValue a ρ g := by
  funext x
  by_cases hx : x ∈ s
  · simp only [extensionValue, dite_eq_left hx, ContinuousMap.add_apply, Pi.add_apply]
  · simp only [extensionValue, dite_eq_right hx, Pi.add_apply, ContinuousMap.add_apply]
    rw [← ρ.sum_finsupport_smul_eq_finsum (x₀ := ⟨x, hx⟩)
      (fun i _ ↦ f (a i) + g (a i)),
      ← ρ.sum_finsupport_smul_eq_finsum (x₀ := ⟨x, hx⟩) (fun i _ ↦ f (a i)),
      ← ρ.sum_finsupport_smul_eq_finsum (x₀ := ⟨x, hx⟩) (fun i _ ↦ g (a i))]
    simp only [smul_add, Finset.sum_add_distrib]

open scoped Classical in
private lemma extensionValue_smul (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ) (c : ℝ) (f : C(s, ℝ)) :
    extensionValue a ρ (c • f) = c • extensionValue a ρ f := by
  funext x
  by_cases hx : x ∈ s
  · simp only [extensionValue, dite_eq_left hx, ContinuousMap.smul_apply, Pi.smul_apply]
  · simp only [extensionValue, dite_eq_right hx, ContinuousMap.smul_apply, Pi.smul_apply]
    rw [← ρ.sum_finsupport_smul_eq_finsum (x₀ := ⟨x, hx⟩) (fun i _ ↦ c • f (a i)),
      ← ρ.sum_finsupport_smul_eq_finsum (x₀ := ⟨x, hx⟩) (fun i _ ↦ f (a i))]
    simp only [smul_eq_mul, Finset.mul_sum, mul_left_comm]

private def extensionLinear (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ)
    (hcont : ∀ f : C(s, ℝ), Continuous (extensionValue a ρ f)) :
    C(s, ℝ) →ₗ[ℝ] C(K, ℝ) where
  toFun f := ⟨extensionValue a ρ f, hcont f⟩
  map_add' f g := ContinuousMap.ext fun x ↦ congrFun (extensionValue_add a ρ f g) x
  map_smul' c f := ContinuousMap.ext fun x ↦ congrFun (extensionValue_smul a ρ c f) x

open scoped Classical in
private lemma extensionLinear_positive
    (a : ↥(sᶜ) → s) (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ)
    (hcont : ∀ f : C(s, ℝ), Continuous (extensionValue a ρ f)) :
    Positive (extensionLinear a ρ hcont) := by
  intro f hf
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  change 0 ≤ extensionValue a ρ f x
  by_cases hx : x ∈ s
  · simpa only [extensionValue, dite_eq_left hx, ContinuousMap.zero_apply] using
      ContinuousMap.le_def.mp hf ⟨x, hx⟩
  · simpa only [extensionValue, dite_eq_right hx, Set.mem_Ici] using
      ρ.finsum_smul_mem_convex (g := fun i _ ↦ f (a i)) (t := Ici (0 : ℝ))
        (mem_univ ⟨x, hx⟩)
        (fun i _ ↦ by simpa only [mem_Ici, ContinuousMap.zero_apply] using
          ContinuousMap.le_def.mp hf (a i)) (convex_Ici (𝕜 := ℝ) 0)

open scoped Classical in
private lemma extensionLinear_one (a : ↥(sᶜ) → s)
    (ρ : PartitionOfUnity ↥(sᶜ) ↥(sᶜ) univ)
    (hcont : ∀ f : C(s, ℝ), Continuous (extensionValue a ρ f)) :
    extensionLinear a ρ hcont 1 = 1 := by
  ext x
  change extensionValue a ρ 1 x = 1
  by_cases hx : x ∈ s
  · simp only [extensionValue, dite_eq_left hx, ContinuousMap.one_apply]
  · simpa only [extensionValue, dite_eq_right hx, ContinuousMap.one_apply, smul_eq_mul,
      mul_one] using ρ.sum_eq_one (mem_univ ⟨x, hx⟩)

end

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace.MetrizableSpace K]

/-- *Borsuk's theorem*: Continuous real functions on a nonempty compact subset
of a compact metrizable space admit a positive unital linear extension operator. -/
theorem exists_positive_unital_extension (s : Set K) [CompactSpace s] [Nonempty s] :
    ∃ T : C(s, ℝ) →L[ℝ] C(K, ℝ), Positive T.toLinearMap ∧ T 1 = 1 ∧
      ∀ (f : C(s, ℝ)) (x : s), T f x = f x := by
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  exact
    let hs : IsClosed s := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
    let ⟨a, ρ, hnear⟩ := exists_extension_weights hs (nonempty_coe_sort.mp inferInstance)
    let hc := extensionValue_continuous hs a ρ hnear
    let R := extensionLinear a ρ hc
    let hR : Positive R := extensionLinear_positive a ρ hc
    ⟨⟨R, hR.continuous⟩, hR, extensionLinear_one a ρ hc,
      fun f x ↦ show extensionValue a ρ f x = f x from dite_eq_left x.property⟩

variable {L : Type*} [TopologicalSpace L] [CompactSpace L] [Nonempty L]

/-- If `E` is a closed subspace of a compact metric space `K`, then
the space `C(E)` is positively 1-complemented in `C(K)`. -/
theorem IsPositiveContractiveRetract.of_isClosedEmbedding (e : L → K)
    (he : IsClosedEmbedding e) :
    ∃ J : C(L, ℝ) →L[ℝ] C(K, ℝ), Positive.IsPositiveContractiveRetract J := by
  let h : L ≃ₜ range e := he.isEmbedding.toHomeomorph
  let : CompactSpace (range e) := isCompact_iff_compactSpace.mp he.isClosed_range.isCompact
  obtain ⟨T, hT, hOne, hTf⟩ := exists_positive_unital_extension (range e)
  let J : C(L, ℝ) →L[ℝ] C(K, ℝ) :=
    T.comp (ContinuousMap.compCLM ℝ ℝ ⟨h.symm, h.symm.continuous⟩)
  let Q : C(K, ℝ) →L[ℝ] C(L, ℝ) := ContinuousMap.compCLM ℝ ℝ ⟨e, he.continuous⟩
  have hJ : Positive J.toLinearMap := fun (f : C(L, ℝ)) hf ↦
    hT (f.comp ⟨h.symm, h.symm.continuous⟩)
      (ContinuousMap.le_def.mpr fun x ↦ ContinuousMap.le_def.mp hf (h.symm x))
  have hQ : Positive Q.toLinearMap := fun (f : C(K, ℝ)) hf ↦
    ContinuousMap.le_def.mpr fun x ↦ ContinuousMap.le_def.mp hf (e x)
  have hJ1 : J 1 = 1 := hOne
  let : Nonempty K := Nonempty.map e inferInstance
  refine ⟨J, Q, hJ, hQ, ?_, (norm_eq_one_of_positive_of_map_one hJ hJ1).le,
    (norm_eq_one_of_positive_of_map_one hQ rfl).le⟩
  intro f
  apply ContinuousMap.ext fun x ↦ ?_
  exact (hTf (f.comp ⟨h.symm, h.symm.continuous⟩) (h x)).trans
    (congrArg f (h.symm_apply_apply x))

end ContinuousMap
