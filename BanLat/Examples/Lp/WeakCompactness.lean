/-
Authors: Pedro Tradacete
-/

import BanLat.Examples.Lp.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Weak compactness in `L¹`

Uniformly integrable and uniformly tight subsets of real `L¹` are relatively
weakly compact. Domination by an integrable function gives both properties, so
order intervals are weakly compact for arbitrary measures.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

universe u

namespace MeasureTheory.Lp

/-- If every point of `s` is at norm distance at most `ε` from some point of a weakly compact
set `K`, then every point in the weak-star closure of `J(s)` is at norm distance at most `ε`
from some point of `J(K)`, where `J` is the canonical embedding into the bidual. -/
private theorem closure_inclusion_subset_add_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s K : Set E) (ε : ℝ)
    (hK : IsCompact (toWeakSpace ℝ E '' K))
    (hdist : ∀ x ∈ s, ∃ y ∈ K, ‖x - y‖ ≤ ε) :
    closure (NormedSpace.inclusionInDoubleDualWeak ℝ E '' (toWeakSpace ℝ E '' s)) ⊆
      NormedSpace.inclusionInDoubleDualWeak ℝ E '' (toWeakSpace ℝ E '' K) +
        WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 ε := by
  refine closure_minimal ?_ ((WeakDual.isClosed_closedBall 0 ε).add_left_of_isCompact
    (hK.image (NormedSpace.inclusionInDoubleDualWeak ℝ E).continuous))
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hdist x hx
  refine Set.mem_add.mpr ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
    StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDualLi ℝ (x - y)), ?_, ?_⟩
  · exact mem_closedBall_zero_iff.mpr
      (((NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (x - y)).le.trans hxy)
  · exact congrArg StrongDual.toWeakDual
      (show NormedSpace.inclusionInDoubleDualLi ℝ y +
          NormedSpace.inclusionInDoubleDualLi ℝ (x - y) =
          NormedSpace.inclusionInDoubleDualLi ℝ x from
        (map_add _ _ _).symm.trans (congrArg _ (add_sub_cancel y x)))

/-- If for every `ε > 0`, there is a weakly compact set `K` such that every point of
`s` is at norm distance at most `ε` from some point of `K`, then the weak-star closure
of `J(s)` is contained in `J(E)`, where `J` is the canonical embedding into the bidual. -/
private theorem closure_subset_range_of_weak_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : Set E)
    (happrox : ∀ ε > (0 : ℝ), ∃ K : Set E,
      IsCompact (toWeakSpace ℝ E '' K) ∧ ∀ x ∈ s, ∃ y ∈ K, ‖x - y‖ ≤ ε) :
    closure (NormedSpace.inclusionInDoubleDualWeak ℝ E '' (toWeakSpace ℝ E '' s)) ⊆
      range (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
  intro F hF
  suffices hmem : WeakDual.toStrongDual F ∈
      closure (range (NormedSpace.inclusionInDoubleDualLi ℝ (E := E))) by
    have hc := (NormedSpace.inclusionInDoubleDualLi ℝ (E := E)).isometry.isClosedEmbedding
    obtain ⟨x, hx⟩ := hc.isClosed_range.closure_eq ▸ hmem
    exact ⟨toWeakSpace ℝ E x, congrArg StrongDual.toWeakDual hx⟩
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨K, hK, hdist⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨_, ⟨_, ⟨y, _, rfl⟩, rfl⟩, z, hz, rfl⟩ :=
    Set.mem_add.mp (closure_inclusion_subset_add_closedBall s K (ε / 2) hK hdist hF)
  refine ⟨NormedSpace.inclusionInDoubleDualLi ℝ y, ⟨y, rfl⟩, ?_⟩
  change dist (NormedSpace.inclusionInDoubleDualLi ℝ y + WeakDual.toStrongDual z)
    (NormedSpace.inclusionInDoubleDualLi ℝ y) < ε
  simpa only [_root_.dist_eq_norm, add_sub_cancel_left] using
    (mem_closedBall_zero_iff.mp hz).trans_lt (half_lt_self hε)

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The Banach space `L²` is reflexive. -/
private theorem inclusionInDoubleDual_surjective_l2 (μ : Measure Ω) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp ℝ 2 μ)) := by
  intro F
  let e := InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)
  let f : StrongDual ℝ (Lp ℝ 2 μ) := F.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨e.symm f, ?_⟩
  ext φ
  obtain ⟨x, rfl⟩ := e.surjective φ
  change e x (e.symm f) = F (e x)
  rw [InnerProductSpace.toDual_apply_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  rfl

/-- Closed balls in real `L²` are weakly compact by reflexivity. -/
private theorem isCompact_toWeakSpace_closedBall_l2 (μ : Measure Ω) (r : ℝ) :
    IsCompact (toWeakSpace ℝ (Lp ℝ 2 μ) '' Metric.closedBall 0 r) := by
  rw [← Metric.isClosed_closedBall.closure_eq,
    (convex_closedBall (0 : Lp ℝ 2 μ) r).toWeakSpace_closure ℝ]
  refine NormedSpace.isCompact_closure_of_isBounded ℝ (Lp ℝ 2 μ) _
    (by simpa only [preimage_image_eq _ (toWeakSpace ℝ (Lp ℝ 2 μ)).injective]
      using Metric.isBounded_closedBall) ?_
  intro F _
  obtain ⟨x, hx⟩ := inclusionInDoubleDual_surjective_l2 μ (WeakDual.toStrongDual F)
  exact ⟨toWeakSpace ℝ (Lp ℝ 2 μ) x, congrArg StrongDual.toWeakDual hx⟩

/-- Functions bounded by a constant on a fixed set of finite measure lie in a weakly
compact subset of `L¹`, obtained as the image of an `L²` ball. -/
private theorem exists_isCompact_toWeakSpace_of_indicator_bound
    (μ : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (C : ℝ) :
    ∃ K : Set (Lp ℝ 1 μ), IsCompact (toWeakSpace ℝ (Lp ℝ 1 μ) '' K) ∧
      ∀ f : Lp ℝ 1 μ, (∀ᵐ ω ∂μ, ‖f ω‖ ≤ s.indicator (fun _ ↦ C) ω) → f ∈ K := by
  have hg := memLp_indicator_const 2 hs.nullMeasurableSet C (Or.inr hμs)
  let g := indicatorConstLp (μ := μ) 2 hs hμs C
  let u := indicatorConstLp (μ := μ) 2 hs hμs (1 : ℝ)
  let T := (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 u
  refine ⟨T '' Metric.closedBall 0 ‖g‖, ?_, fun f hf ↦ ?_⟩
  · have hc := (isCompact_toWeakSpace_closedBall_l2 μ ‖g‖).image (WeakSpace.map T).continuous
    rw [Set.image_image] at hc ⊢
    exact hc
  have hf2 : MemLp (fun ω ↦ f ω) 2 μ := hg.mono' (Lp.aestronglyMeasurable f) hf
  refine ⟨hf2.toLp _, mem_closedBall_zero_iff.mpr ?_, ?_⟩
  · rw [Lp.norm_toLp, show ‖g‖ = (eLpNorm (s.indicator (fun _ ↦ C)) 2 μ).toReal
      from Lp.norm_toLp _ hg]
    exact ENNReal.toReal_mono hg.ne (eLpNorm_mono_ae_real (Lp.aestronglyMeasurable f) hf)
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) u (hf2.toLp _),
    indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ)),
    hf2.coeFn_toLp, hf] with ω hmul hu hfω hbound
  rw [show (T (hf2.toLp _)) ω = u ω * (hf2.toLp _) ω from hmul,
    show u ω = s.indicator (fun _ ↦ (1 : ℝ)) ω from hu, hfω]
  by_cases hω : ω ∈ s <;> simp_all

private theorem eLpNorm_sub_indicator_inter_le (μ : Measure Ω) (f : Ω → ℝ)
    {s : Set Ω} (hs : NullMeasurableSet s μ) (t : Set Ω) :
    eLpNorm (f - (s ∩ t).indicator f) 1 μ ≤
      eLpNorm (sᶜ.indicator f) 1 μ + eLpNorm (tᶜ.indicator f) 1 μ := by
  have heq : f - (s ∩ t).indicator f = sᶜ.indicator f + s.indicator (tᶜ.indicator f) := by
    simp [indicator_compl, indicator_sub', indicator_indicator]
  rw [heq]
  exact (eLpNorm_add_le (f := sᶜ.indicator f) (g := s.indicator (tᶜ.indicator f))
    (p := 1) (μ := μ) le_rfl).trans
      (add_le_add le_rfl (eLpNorm_indicator_le (tᶜ.indicator f) hs))

/-- Uniformly integrable, uniformly tight set `A` in `L¹` can be approximated for
every `ε > 0` by elements of a weakly compact set. -/
private theorem exists_weakly_compact_approximation
    (μ : Measure Ω) (A : Set (Lp ℝ 1 μ))
    (hA : UniformIntegrable (fun f : A ↦ (f.1 : Ω → ℝ)) 1 μ)
    (hAt : UnifTight (fun f : A ↦ (f.1 : Ω → ℝ)) 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (Lp ℝ 1 μ), IsCompact (toWeakSpace ℝ (Lp ℝ 1 μ) '' K) ∧
      ∀ f ∈ A, ∃ g ∈ K, ‖f - g‖ ≤ ε := by
  obtain ⟨s, hs, hμs, htail⟩ :=
    hAt.exists_measurableSet_indicator (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨C, hC⟩ := hA.spec one_ne_zero ENNReal.one_ne_top
    (ENNReal.ofReal_pos.mpr (half_pos hε))
  obtain ⟨K, hK, hbound⟩ := exists_isCompact_toWeakSpace_of_indicator_bound μ hs hμs.ne C
  refine ⟨K, hK, fun f hf ↦ ?_⟩
  let t := {ω | ‖f ω‖₊ < C}
  have ht : NullMeasurableSet t μ :=
    nullMeasurableSet_lt (Lp.aestronglyMeasurable f).nnnorm.aemeasurable aemeasurable_const
  have hg := (Lp.memLp f).indicator (hs.nullMeasurableSet.inter ht)
  refine ⟨hg.toLp _, hbound _ ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp] with ω hω
    by_cases hωst : ω ∈ s ∩ t
    · simpa [hω, hωst, hωst.1] using (show ‖f ω‖ < (C : ℝ) from hωst.2).le
    · by_cases hωs : ω ∈ s <;> simp [hω, hωst, hωs]
  rw [Lp.norm_def, eLpNorm_congr_ae
    ((Lp.coeFn_sub f _).trans (Filter.EventuallyEq.rfl.sub hg.coeFn_toLp))]
  apply ENNReal.toReal_le_of_le_ofReal hε.le
  refine (eLpNorm_sub_indicator_inter_le μ f hs.nullMeasurableSet t).trans ?_
  have htcompl : tᶜ = {ω | C ≤ ‖f ω‖₊} := by ext ω; simp [t]
  simpa only [htcompl, ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le,
    add_halves] using add_le_add (htail ⟨f, hf⟩) (hC ⟨f, hf⟩)

/-- A uniformly integrable, uniformly tight set in real `L¹` is relatively weakly
compact. Tightness is needed here because the measure may be infinite. -/
theorem isCompact_closure_toWeakSpace_of_uniformIntegrable
    (μ : Measure Ω) (A : Set (Lp ℝ 1 μ))
    (hA : UniformIntegrable (fun f : A ↦ (f.1 : Ω → ℝ)) 1 μ)
    (hAt : UnifTight (fun f : A ↦ (f.1 : Ω → ℝ)) 1 μ) :
    IsCompact (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' A)) := by
  refine NormedSpace.isCompact_closure_of_isBounded ℝ (Lp ℝ 1 μ) _ ?_
    (closure_subset_range_of_weak_approximation A
      (fun _ hε ↦ exists_weakly_compact_approximation μ A hA hAt hε))
  rw [preimage_image_eq _ (toWeakSpace ℝ (Lp ℝ 1 μ)).injective,
    isBounded_iff_forall_norm_le]
  obtain ⟨C, hC⟩ := hA.2
  exact ⟨C, fun f hf ↦ (Lp.norm_def f).trans_le
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (hC ⟨f, hf⟩)).trans_eq
      (ENNReal.coe_toReal C))⟩

/-- Domination by the upper endpoint makes a positive order interval in `L1` uniformly
integrable and uniformly tight. -/
private theorem uniformIntegrable_and_unifTight_Icc_zero
    (μ : Measure Ω) (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    UniformIntegrable (fun f : Icc 0 x ↦ (f.1 : Ω → ℝ)) 1 μ ∧
      UnifTight (fun f : Icc 0 x ↦ (f.1 : Ω → ℝ)) 1 μ := by
  have hdom (f : Icc 0 x) : ∀ᵐ ω ∂μ, ‖f.1 ω‖ ≤ ‖x ω‖ := by
    filter_upwards [(Lp.coeFn_nonneg f.1).mpr f.2.1,
      (Lp.coeFn_le f.1 x).mpr f.2.2, (Lp.coeFn_nonneg x).mpr hx] with ω h0 hle hxω
    simpa only [Real.norm_of_nonneg h0, Real.norm_of_nonneg hxω] using hle
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (unifIntegrable_const (ι := Icc 0 x) le_rfl ENNReal.one_ne_top (Lp.memLp x)).ae_mono
      (fun f ↦ Lp.aestronglyMeasurable f.1)
      (fun f ↦ (hdom f).mono fun _ h ↦ enorm_le_iff_norm_le.mpr h)
  · exact ⟨‖x‖₊, fun f ↦ (eLpNorm_mono_ae (Lp.aestronglyMeasurable f.1) (hdom f)).trans_eq
      (Lp.enorm_def x).symm⟩
  intro ε hε
  obtain ⟨s, hs, hμs, htail⟩ := (Lp.memLp x).exists_eLpNorm_indicator_compl_lt
    ENNReal.one_ne_top hε.ne'
  refine ⟨s, hμs.ne, fun f ↦ le_trans ?_ htail.le⟩
  apply eLpNorm_mono_ae ((Lp.aestronglyMeasurable f.1).indicator hs.compl)
  exact (hdom f).mono fun ω h ↦ by
    by_cases hω : ω ∈ sᶜ
    · simpa only [indicator_of_mem hω] using h
    · simp only [indicator_of_notMem hω, le_refl]

/-- Positive order intervals in `L¹` are weakly compact for arbitrary measures. -/
theorem isCompact_toWeakSpace_Icc_zero (μ : Measure Ω)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    IsCompact (toWeakSpace ℝ (Lp ℝ 1 μ) '' Icc 0 x) := by
  obtain ⟨hUI, hT⟩ := uniformIntegrable_and_unifTight_Icc_zero μ x hx
  simpa only [← (convex_Icc (0 : Lp ℝ 1 μ) x).toWeakSpace_closure ℝ,
    isClosed_Icc.closure_eq] using
    Lp.isCompact_closure_toWeakSpace_of_uniformIntegrable μ (Icc 0 x) hUI hT

end MeasureTheory.Lp
