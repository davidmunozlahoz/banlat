/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Examples.Ellp.Schur
import BanLat.Examples.Lp.AlmostOrderBounded
import BanLat.Preliminaries.EberleinSmulian
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak compactness in real `L¹`

For norm-bounded families in real `L¹` over a finite measure, relative weak compactness,
equi-integrability, and almost order boundedness are equivalent.
-/

open MeasureTheory Set Metric
open scoped Topology Pointwise ENNReal NNReal lp

noncomputable section

/-- The canonical embedding of a real Hilbert space into its bidual is
surjective. Thus every continuous linear functional on `H*` is evaluation
at some vector of `H`. -/
private lemma hilbert_bidual_surjective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro z
  let R := InnerProductSpace.toDual ℝ H
  let φ : StrongDual ℝ H := z.comp R.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨R.symm φ, ?_⟩
  apply DFunLike.ext
  intro f
  rw [NormedSpace.dual_def, ← InnerProductSpace.toDual_symm_apply,
    real_inner_comm, InnerProductSpace.toDual_symm_apply]
  change z (R (R.symm f)) = z f
  rw [R.apply_symm_apply]

/-- The closed ball of radius `r` centered at zero in a real Hilbert space
is compact in the weak topology. -/
private lemma hilbert_isCompact_closedBall {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' closedBall (0 : H) r) := by
  have hc := NormedSpace.isCompact_closure_of_isBounded ℝ H
    (toWeakSpace ℝ H '' closedBall (0 : H) r) (by
      simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective] using
        (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : H) r))) (by
      intro z _
      obtain ⟨x, hx⟩ := hilbert_bidual_surjective (WeakDual.toStrongDual z)
      refine ⟨toWeakSpace ℝ H x, ?_⟩
      apply DFunLike.ext
      intro f
      exact DFunLike.congr_fun hx f)
  rwa [← (convex_closedBall (0 : H) r).toWeakSpace_closure ℝ,
    isClosed_closedBall.closure_eq] at hc

/-- Suppose every element of `F` is within norm distance `ε` of some point of
a weakly compact set `K`. Then every point in the weak-star closure of the
canonical image of `F` is within bidual norm distance `ε` of some point of
the canonical image of `K`. -/
private lemma bidual_approximation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Set E} {K : Set (WeakSpace ℝ E)} {ε : ℝ} (hK : IsCompact K)
    (hF : ∀ f ∈ F, ∃ g ∈ K, ‖f - (toWeakSpace ℝ E).symm g‖ ≤ ε)
    {z : WeakDual ℝ (StrongDual ℝ E)}
    (hz : z ∈ closure (NormedSpace.inclusionInDoubleDualWeak ℝ E ''
      (toWeakSpace ℝ E '' F))) :
    ∃ g ∈ K, ‖WeakDual.toStrongDual z -
      NormedSpace.inclusionInDoubleDual ℝ E ((toWeakSpace ℝ E).symm g)‖ ≤ ε := by
  let hBnorm : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ E)) := inferInstance
  let hBspace : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ E)) := inferInstance
  let : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ E)) := hBnorm
  let : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ E)) := hBspace
  let e := NormedSpace.inclusionInDoubleDualWeak ℝ E
  let J := NormedSpace.inclusionInDoubleDual ℝ E
  let B : Set (WeakDual ℝ (StrongDual ℝ E)) :=
    WeakDual.toStrongDual ⁻¹' closedBall 0 ε
  have hc : IsCompact (e '' K + B) :=
    (hK.image e.continuous).add (WeakDual.isCompact_closedBall 0 ε)
  have hs : e '' (toWeakSpace ℝ E '' F) ⊆ e '' K + B := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨g, hg, hfg⟩ := hF f hf
    refine ⟨e g, ⟨g, hg, rfl⟩, e (toWeakSpace ℝ E f) - e g, ?_, by abel_nf⟩
    change WeakDual.toStrongDual (e (toWeakSpace ℝ E f) - e g) ∈ closedBall 0 ε
    apply mem_closedBall_zero_iff.mpr
    change ‖J f - J ((toWeakSpace ℝ E).symm g)‖ ≤ ε
    rw [← map_sub]
    exact ((NormedSpace.inclusionInDoubleDualLi (E := E) ℝ).norm_map _).trans_le hfg
  obtain ⟨_, ⟨g, hg, rfl⟩, b, hb, hzb⟩ := closure_minimal hs hc.isClosed hz
  refine ⟨g, hg, ?_⟩
  have heq : WeakDual.toStrongDual z - J ((toWeakSpace ℝ E).symm g) =
      WeakDual.toStrongDual b := by
    rw [← hzb, map_add]
    change J ((toWeakSpace ℝ E).symm g) + WeakDual.toStrongDual b -
      J ((toWeakSpace ℝ E).symm g) = WeakDual.toStrongDual b
    abel_nf
  rw [heq]
  change WeakDual.toStrongDual b ∈ closedBall 0 ε at hb
  exact mem_closedBall_zero_iff.mp hb

/-- Let `F` be a norm-bounded subset of a real Banach space. If for every
`ε > 0` there is a weakly compact set `K` such that each point of `F` is
within norm distance `ε` of some point of `K`, then the weak closure of
`F` is compact. -/
private lemma isCompact_closure_of_weaklyCompact_approximation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Set E} (hbounded : Bornology.IsBounded F)
    (happrox : ∀ ε > 0, ∃ K : Set (WeakSpace ℝ E), IsCompact K ∧
      ∀ f ∈ F, ∃ g ∈ K, ‖f - (toWeakSpace ℝ E).symm g‖ ≤ ε) :
    IsCompact (closure (toWeakSpace ℝ E '' F)) := by
  let hBnorm : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ E)) := inferInstance
  let hBspace : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ E)) := inferInstance
  let : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ E)) := hBnorm
  let : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ E)) := hBspace
  apply NormedSpace.isCompact_closure_of_isBounded ℝ E _
    (by simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hbounded)
  intro z hz
  let J := NormedSpace.inclusionInDoubleDual ℝ E
  have hclosed : IsClosed (Set.range J) :=
    (NormedSpace.inclusionInDoubleDualLi (E := E) ℝ).isometry.isClosedEmbedding.isClosed_range
  have hmem : WeakDual.toStrongDual z ∈ Set.range J := by
    rw [← hclosed.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨K, hK, hF⟩ := happrox (ε / 2) (half_pos hε)
    obtain ⟨g, _, hg⟩ := bidual_approximation hK hF hz
    refine ⟨J ((toWeakSpace ℝ E).symm g), ⟨_, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    exact hg.trans_lt (half_lt_self hε)
  obtain ⟨x, hx⟩ := hmem
  refine ⟨toWeakSpace ℝ E x, ?_⟩
  apply DFunLike.ext
  intro f
  exact DFunLike.congr_fun hx f

/-- The continuous linear inclusion from real `L²(μ)` into real `L¹(μ)`
for a finite measure `μ`. It sends each function to the same
almost-everywhere equivalence class in `L¹(μ)`. -/
private def l2ToL1 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ := by
  let T : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 1 μ :=
    { toFun := fun f ↦ ⟨f.1, Lp.antitone (by norm_num : (1 : ENNReal) ≤ 2) f.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine T.mkContinuous ((μ univ) ^ (1 / 2 : ℝ)).toReal fun f ↦ ?_
  change (eLpNorm f 1 μ).toReal ≤
    ((μ univ) ^ (1 / 2 : ℝ)).toReal * (eLpNorm f 2 μ).toReal
  have h : eLpNorm f 1 μ ≤ eLpNorm f 2 μ * (μ univ) ^ (1 / 2 : ℝ) := by
    convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by norm_num : (1 : ENNReal) ≤ 2) (Lp.aestronglyMeasurable f) using 1
    norm_num
  have hfinite : eLpNorm f 2 μ * (μ univ) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _))
  simpa only [ENNReal.toReal_mul, mul_comm] using ENNReal.toReal_mono hfinite h

/-- Let `μ` be a finite measure, `f ∈ L¹(μ)`, and `C ≥ 0`. The function equal
to `f` on `{x | |f x| < C}` and zero elsewhere defines `g ∈ L²(μ)` with
`‖g‖ ≤ C √(μ univ)`. The `L¹(μ)` distance from `f` to the image of `g` is
exactly the integral of `|f|` over `{x | C ≤ |f x|}`. -/
private lemma exists_l2_approximation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (f : Lp ℝ 1 μ) (C : ℝ≥0) :
    ∃ g : Lp ℝ 2 μ,
      ‖g‖ ≤ (measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹ * C ∧
      ‖f - l2ToL1 μ g‖ =
        (eLpNorm ({x | C ≤ ‖f x‖₊}.indicator f) 1 μ).toReal := by
  let A : Set α := {x | C ≤ ‖f x‖₊}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable.nnnorm
  have hbound (x : α) : ‖Aᶜ.indicator f x‖ ≤ (C : ℝ) := by
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_notMem (show x ∉ Aᶜ from not_not.mpr hx), norm_zero]
        using C.coe_nonneg
    · rw [Set.indicator_of_mem (show x ∈ Aᶜ from hx)]
      exact_mod_cast (lt_of_not_ge hx).le
  have hm : MemLp (Aᶜ.indicator f) 2 μ :=
    MemLp.of_bound ((Lp.stronglyMeasurable f).indicator hA.compl).aestronglyMeasurable
      C (Filter.Eventually.of_forall hbound)
  let g := hm.toLp (Aᶜ.indicator f)
  have hg : ⇑g =ᵐ[μ] Aᶜ.indicator f := hm.coeFn_toLp
  refine ⟨g, Lp.norm_le_of_ae_bound C.coe_nonneg ?_, ?_⟩
  · exact hg.mono fun x hx ↦ hx.symm ▸ hbound x
  · rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    have hg' : ⇑(l2ToL1 μ g) =ᵐ[μ] Aᶜ.indicator f := hg
    filter_upwards [Lp.coeFn_sub f (l2ToL1 μ g), hg'] with x hsub hx
    rw [hsub, Pi.sub_apply, hx]
    by_cases hmem : x ∈ A <;> simp [Set.indicator, hmem, A] at *

/-- Let `F` be a uniformly integrable subset of real `L¹(μ)` for a finite
measure `μ`. For every `ε > 0`, there is a weakly compact set `K` in `L¹(μ)`
such that each `f ∈ F` lies within `L¹` distance `ε` of some element of `K`. -/
private lemma weaklyCompact_approximation_of_uniformIntegrable {α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {F : Set (Lp ℝ 1 μ)}
    (hF : UniformIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ) :
    ∀ ε > 0, ∃ K : Set (WeakSpace ℝ (Lp ℝ 1 μ)), IsCompact K ∧
      ∀ f ∈ F, ∃ g ∈ K, ‖f - (toWeakSpace ℝ (Lp ℝ 1 μ)).symm g‖ ≤ ε := by
  intro ε hε
  obtain ⟨C, hC⟩ := hF.spec (by norm_num) (by norm_num) (ENNReal.ofReal_pos.mpr hε)
  let R : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹ * C
  let T := WeakSpace.map (l2ToL1 μ)
  refine ⟨T '' (toWeakSpace ℝ (Lp ℝ 2 μ) '' closedBall 0 R),
    (hilbert_isCompact_closedBall R).image T.continuous, ?_⟩
  intro f hf
  obtain ⟨g, hg, hfg⟩ := exists_l2_approximation f C
  refine ⟨T (toWeakSpace ℝ (Lp ℝ 2 μ) g),
    ⟨_, ⟨g, mem_closedBall_zero_iff.mpr hg, rfl⟩, rfl⟩, ?_⟩
  change ‖f - l2ToL1 μ g‖ ≤ ε
  rw [hfg]
  exact ENNReal.toReal_le_of_le_ofReal hε.le (hC ⟨f, hf⟩)

/-- A norm-bounded equi-integrable family in real `L¹` over a finite measure has compact
closure in the weak topology. -/
theorem MeasureTheory.Lp.isCompact_closure_of_unifIntegrable {α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {F : Set (Lp ℝ 1 μ)}
    (hbounded : Bornology.IsBounded F)
    (hF : UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ) :
    IsCompact (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' F)) :=
  isCompact_closure_of_weaklyCompact_approximation hbounded
    (weaklyCompact_approximation_of_uniformIntegrable
      (Lp.uniformIntegrable_of_isBounded_of_unifIntegrable hbounded hF))

/-- Let `φ` be a sequence of continuous linear functionals on `E`. If every
finite sum of the absolute values `|φ n x|` is bounded by `‖x‖`, then
`x ↦ (φ n x)ₙ` defines a continuous linear map into `ℓ¹(ℕ, ℝ)` with
operator norm at most one. -/
private def l1MapOfSumBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℕ → StrongDual ℝ E)
    (hφ : ∀ x : E, ∀ s : Finset ℕ, ∑ n ∈ s, ‖φ n x‖ ≤ ‖x‖) :
    E →L[ℝ] ℓ¹(ℕ, ℝ) := by
  let T : E →ₗ[ℝ] ℓ¹(ℕ, ℝ) :=
    { toFun := fun x ↦ ⟨fun n ↦ φ n x, memℓp_gen' (p := 1) (C := ‖x‖) (by
        intro s
        simpa only [ENNReal.toReal_one, Real.rpow_one] using hφ x s)⟩
      map_add' := fun x y ↦ by ext n; exact map_add (φ n) x y
      map_smul' := fun a x ↦ by ext n; exact map_smul (φ n) a x }
  refine T.mkContinuous 1 fun x ↦ ?_
  rw [one_mul]
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg x)
  intro s
  simpa [T] using hφ x s

/-- Given `f ∈ L¹(μ)` and a measurable set `s`, the function equal to the sign
of `f` on `s` and zero elsewhere defines an element `g ∈ L∞(μ)`. Almost
everywhere, `|g| ≤ 1ₛ` and `g * f = 1ₛ * |f|`. -/
private lemma exists_signed_indicator {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 1 μ) {s : Set α} (hs : MeasurableSet s) :
    ∃ g : Lp ℝ ∞ μ,
      (∀ᵐ x ∂μ, ‖g x‖ ≤ s.indicator (fun _ ↦ (1 : ℝ)) x) ∧
      (∀ᵐ x ∂μ, g x * f x = s.indicator (fun x ↦ ‖f x‖) x) := by
  let c : α → ℝ := fun x ↦ if 0 ≤ f x then 1 else -1
  have hc : Measurable c :=
    Measurable.ite (measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable)
      measurable_const measurable_const
  have hcn (x : α) : ‖c x‖ = 1 := by simp [c]; split_ifs <;> norm_num
  have hg : MemLp (s.indicator c) ∞ μ :=
    memLp_top_of_bound (hc.indicator hs).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x ↦ (norm_indicator_le_norm_self c x).trans (hcn x).le)
  refine ⟨hg.toLp _, ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, norm_indicator_eq_indicator_norm]
    exact le_of_eq (congrArg (fun k : α → ℝ ↦ s.indicator k x) (funext hcn))
  · filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · simp only [indicator_of_mem hxs, c, Real.norm_eq_abs]
      split_ifs with hf
      · simp [abs_of_nonneg hf]
      · simp [abs_of_neg (lt_of_not_ge hf)]
    · simp [indicator_of_notMem hxs]

/-- Let `s` be measurable and let `g ∈ L∞(μ)` satisfy `|g| ≤ 1ₛ` almost
everywhere. For every `f ∈ L¹(μ)`, the absolute value of
`∫ g * f ∂μ` is at most `∫ x in s, |f x| ∂μ`. -/
private lemma norm_signed_pairing_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (g : Lp ℝ ∞ μ)
    (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ s.indicator (fun _ ↦ (1 : ℝ)) x) (f : Lp ℝ 1 μ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 g f‖ ≤ ∫ x in s, ‖f x‖ ∂μ := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_indicator hs]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((memLp_one_iff_integrable.mp (Lp.memLp f)).norm.indicator hs)
  filter_upwards [hg] with x hx
  change ‖g x * f x‖ ≤ s.indicator (fun x ↦ ‖f x‖) x
  rw [norm_mul]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs] at hx ⊢
    simpa using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
  · simp only [indicator_of_notMem hxs] at hx ⊢
    simpa using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

/-- Let `s n` be pairwise disjoint measurable sets. Suppose each `g n ∈ L∞(μ)`
has absolute value at most one almost everywhere on `s n` and vanishes almost
everywhere outside `s n`. For any `f ∈ L¹(μ)` and finite set of indices `t`,
the sum over `n ∈ t` of the absolute values of the integrals of `g n * f`
is at most `‖f‖`. -/
private lemma sum_norm_signed_pairing_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hd : _root_.Pairwise (fun i j ↦ Disjoint (s i) (s j)))
    (g : ℕ → Lp ℝ ∞ μ)
    (hg : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ (s n).indicator (fun _ ↦ (1 : ℝ)) x)
    (f : Lp ℝ 1 μ) (t : Finset ℕ) :
    ∑ n ∈ t, ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 (g n) f‖ ≤ ‖f‖ := by
  have hf := (memLp_one_iff_integrable.mp (Lp.memLp f)).norm
  calc
    _ ≤ ∑ n ∈ t, ∫ x in s n, ‖f x‖ ∂μ :=
      Finset.sum_le_sum fun n _ ↦ norm_signed_pairing_le (hs n) (g n) (hg n) f
    _ = ∫ x in ⋃ n ∈ t, s n, ‖f x‖ ∂μ :=
      (integral_biUnion_finset t (fun n _ ↦ hs n) (fun i _ j _ hij ↦ hd hij)
        (fun _ _ ↦ hf.integrableOn)).symm
    _ ≤ ∫ x, ‖f x‖ ∂μ :=
      setIntegral_le_integral hf (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

/-- Given a sequence `(f n)` in real `L¹(μ)` and pairwise disjoint measurable
sets `s n`, there is a continuous linear map `T : L¹(μ) → ℓ¹(ℕ, ℝ)` such
that the `n`-th coordinate of `T (f n)` is the integral of `|f n|` over
`s n`. -/
private lemma exists_signed_restriction_map {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : ℕ → Lp ℝ 1 μ) {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n))
    (hd : _root_.Pairwise (fun i j ↦ Disjoint (s i) (s j))) :
    ∃ T : Lp ℝ 1 μ →L[ℝ] ℓ¹(ℕ, ℝ),
      ∀ n, (T (f n) : ℕ → ℝ) n = ∫ x in s n, ‖f n x‖ ∂μ := by
  choose g hg heq using fun n ↦ exists_signed_indicator (f n) (hs n)
  let φ : ℕ → StrongDual ℝ (Lp ℝ 1 μ) :=
    fun n ↦ (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 (g n)
  refine ⟨l1MapOfSumBound φ (sum_norm_signed_pairing_le hs hd g hg), ?_⟩
  intro n
  change φ n (f n) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  exact (integral_congr_ae (heq n)).trans (integral_indicator (hs n))

/-- Let `(s n)` be a sequence of sets. For each `n`, retain only the points of
`s n` that belong to no `s m` with `m > n`. The resulting sets are pairwise
disjoint. -/
private lemma pairwise_disjoint_remove_later {α : Type*} (s : ℕ → Set α) :
    _root_.Pairwise (fun i j ↦
      Disjoint (s i \ ⋃ m > i, s m) (s j \ ⋃ m > j, s m)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hxi.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hij, hxj.1⟩⟩)
  · exact hxj.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hji, hxi.1⟩⟩)

/-- If `F` is not equi-integrable, there exists `ε > 0` such that for every
`δ > 0` there are `f ∈ F` and a measurable set `s` with `μ s ≤ δ` and
`∫ x in s, ‖f x‖ ∂μ > ε`. -/
private lemma exists_small_set_witness {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (Lp ℝ 1 μ)}
    (hF : ¬ UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ f ∈ F, ∃ s : Set α, MeasurableSet s ∧ μ s ≤ δ ∧
        ε < ∫ x in s, ‖(f : α → ℝ) x‖ ∂μ := by
  rw [unifIntegrable_iff'] at hF
  push Not at hF
  obtain ⟨ε, hε, hw⟩ := hF
  obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro δ hδ
  obtain ⟨f, s, hs, hμs, hfs⟩ := hw δ hδ
  refine ⟨f.1, f.2, s, hs, hμs, ?_⟩
  have hint : IntegrableOn (f.1 : α → ℝ) s μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp f.1)).integrableOn
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f.1).restrict,
    ← ofReal_integral_norm_eq_lintegral_enorm hint] at hfs
  by_contra h
  have hle := ENNReal.ofReal_le_ofReal (le_of_not_gt h)
  exact (not_lt_of_ge hle) (by simpa using hrε.trans hfs)

/-- Given `f ∈ L¹(μ)` and `ε > 0`, there exists `δ > 0` such that
`∫ x in s, ‖f x‖ ∂μ ≤ ε` for every set `s` with `μ s ≤ δ`. -/
private lemma exists_integral_small_set_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℝ 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s : Set α, μ s ≤ δ → ∫ x in s, ‖f x‖ ∂μ ≤ ε := by
  obtain ⟨δ, hδ, hsmall⟩ := unifIntegrable_iff.mp
    (unifIntegrable_const (ι := Unit) le_rfl (by norm_num) (Lp.memLp f))
      (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨r, hr, hrδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  refine ⟨r, by exact_mod_cast hr, fun s hs ↦ ?_⟩
  have h := hsmall () s (hs.trans hrδ.le)
  have hint : IntegrableOn (f : α → ℝ) s μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp f)).integrableOn
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f).restrict,
    ← ofReal_integral_norm_eq_lintegral_enorm hint] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

/-- Fix `ε > 0`. Suppose that for every `δ > 0` there exist `f ∈ F` and a
measurable set `s` with `μ s ≤ δ` and `ε < ∫ x in s, ‖f x‖ ∂μ`.
Then for every `q > 0` there exist `f ∈ F`, a measurable set `s`, and
`0 < r ≤ q / 2` such that `μ s ≤ q` and `ε < ∫ x in s, ‖f x‖ ∂μ`.
For the same `f`, every set `t` with `μ t ≤ 2 * r` satisfies
`∫ x in t, ‖f x‖ ∂μ ≤ ε / 2`. -/
private lemma exists_witness_step {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (Lp ℝ 1 μ)} {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ δ : ℝ≥0∞, 0 < δ → ∃ f ∈ F, ∃ s : Set α,
      MeasurableSet s ∧ μ s ≤ δ ∧ ε < ∫ x in s, ‖(f : α → ℝ) x‖ ∂μ)
    {q : ℝ≥0} (hq : 0 < q) :
    ∃ f ∈ F, ∃ s : Set α, ∃ r : ℝ≥0, MeasurableSet s ∧ μ s ≤ q ∧
      ε < ∫ x in s, ‖(f : α → ℝ) x‖ ∂μ ∧ 0 < r ∧ r ≤ q / 2 ∧
      ∀ t : Set α, μ t ≤ (2 * r : ℝ≥0) → ∫ x in t, ‖(f : α → ℝ) x‖ ∂μ ≤ ε / 2 := by
  obtain ⟨f, hf, s, hs, hμs, hfs⟩ := hw q (by exact_mod_cast hq)
  obtain ⟨δ, hδ, hsmall⟩ := exists_integral_small_set_bound f (half_pos hε)
  refine ⟨f, hf, s, min q δ / 2, hs, hμs, hfs, ?_, ?_, ?_⟩
  · exact div_pos (lt_min hq hδ) (by norm_num)
  · exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  · intro t ht
    apply hsmall t (ht.trans ?_)
    exact_mod_cast (show 2 * (min q δ / 2) ≤ δ by
      rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)]
      exact min_le_right _ _)

/-- Fix `ε > 0` and suppose that for every `δ > 0` there are `f ∈ F` and a
measurable set `s` with `μ s ≤ δ` and `∫ x in s, ‖f x‖ ∂μ > ε`.
Then there are sequences `(f n)` in `F`, `(s n)` of measurable sets, and
`(q n)` of nonnegative numbers such that for every `n`, the set `s n` has
measure at most `q n` and `∫ x in s n, ‖f n x‖ ∂μ > ε`.
The bounds satisfy `q (n + 1) ≤ q n / 2`, and the integral of `‖f n x‖`
over any set of measure at most `2 * q (n + 1)` is at most `ε / 2`. -/
private lemma exists_witness_sequence {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (Lp ℝ 1 μ)} {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ δ : ℝ≥0∞, 0 < δ → ∃ f ∈ F, ∃ s : Set α,
      MeasurableSet s ∧ μ s ≤ δ ∧ ε < ∫ x in s, ‖(f : α → ℝ) x‖ ∂μ) :
    ∃ f : ℕ → Lp ℝ 1 μ, ∃ s : ℕ → Set α, ∃ q : ℕ → ℝ≥0,
      ∀ n, f n ∈ F ∧ MeasurableSet (s n) ∧ μ (s n) ≤ q n ∧
        ε < ∫ x in s n, ‖f n x‖ ∂μ ∧ q (n + 1) ≤ q n / 2 ∧
        ∀ t : Set α, μ t ≤ (2 * q (n + 1) : ℝ≥0) →
          ∫ x in t, ‖f n x‖ ∂μ ≤ ε / 2 := by
  choose f hf s r hs hμ hfs hr hrq hsmall using
    fun q : {q : ℝ≥0 // 0 < q} ↦ exists_witness_step hε hw q.2
  let next : {q : ℝ≥0 // 0 < q} → {q : ℝ≥0 // 0 < q} := fun q ↦ ⟨r q, hr q⟩
  let q := fun n ↦ next^[n] ⟨1, by norm_num⟩
  refine ⟨fun n ↦ f (q n), fun n ↦ s (q n), fun n ↦ (q n).1, fun n ↦ ?_⟩
  have hnext : (q (n + 1)).1 = r (q n) := by
    simp only [q, Function.iterate_succ_apply', next]
  refine ⟨hf _, hs _, hμ _, hfs _, ?_, ?_⟩
  · simpa only [hnext] using hrq (q n)
  · simpa only [hnext] using hsmall (q n)

/-- Let `(q n)` be a sequence of nonnegative numbers with `q (n + 1) ≤ q n / 2`
for every `n`. The sum of any `k` consecutive terms starting at index `n`
is at most `2 * q n`. -/
private lemma sum_range_le_of_halving (q : ℕ → ℝ≥0)
    (hq : ∀ n, q (n + 1) ≤ q n / 2) (n k : ℕ) :
    ∑ i ∈ Finset.range k, q (n + i) ≤ 2 * q n := by
  have h : ∀ k, (∑ i ∈ Finset.range k, q (n + i)) + 2 * q (n + k) ≤ 2 * q n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk := hq (n + k)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)] at hk
      simp only [Nat.add_assoc] at hk
      nlinarith
  exact (le_add_of_nonneg_right (by positivity)).trans (h k)

/-- Let `(s n)` be a sequence of sets and `(q n)` a sequence of nonnegative
numbers such that `μ (s n) ≤ q n` and `q (n + 1) ≤ q n / 2` for every `n`.
Then the union of the sets `s m` with `m > n` has measure at most
`2 * q (n + 1)`. -/
private lemma measure_later_union_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : ℕ → Set α) (q : ℕ → ℝ≥0) (hs : ∀ n, μ (s n) ≤ q n)
    (hq : ∀ n, q (n + 1) ≤ q n / 2) (n : ℕ) :
    μ (⋃ m > n, s m) ≤ (2 * q (n + 1) : ℝ≥0) := by
  have hsub : (⋃ m > n, s m) ⊆ ⋃ k, s (n + 1 + k) := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    obtain ⟨hnm, hxm⟩ := mem_iUnion.mp hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hnm)
    exact mem_iUnion.mpr ⟨k, hxm⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  refine (ENNReal.tsum_le_tsum fun k ↦ hs (n + 1 + k)).trans ?_
  apply ENNReal.tsum_le_of_sum_range_le
  intro k
  exact_mod_cast sum_range_le_of_halving q hq (n + 1) k

/-- If `F` is not equi-integrable, there exist `ε > 0`, a sequence `(f n)` in
`F`, and pairwise disjoint measurable sets `(s n)` such that the integral
of `|f n|` over `s n` is greater than `ε` for every `n`. -/
private lemma exists_disjoint_witnesses {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (Lp ℝ 1 μ)}
    (hF : ¬ UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ f : ℕ → Lp ℝ 1 μ, ∃ s : ℕ → Set α,
      (∀ n, f n ∈ F) ∧ (∀ n, MeasurableSet (s n)) ∧
      _root_.Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧
      ∀ n, ε < ∫ x in s n, ‖f n x‖ ∂μ := by
  obtain ⟨ε, hε, hw⟩ := exists_small_set_witness hF
  obtain ⟨f, s, q, h⟩ := exists_witness_sequence hε hw
  let U := fun n ↦ ⋃ m > n, s m
  have hU (n) : MeasurableSet (U n) :=
    MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun _ ↦ (h m).2.1
  refine ⟨ε / 2, half_pos hε, f, fun n ↦ s n \ U n, fun n ↦ (h n).1,
    fun n ↦ (h n).2.1.diff (hU n), pairwise_disjoint_remove_later s, ?_⟩
  intro n
  have hμ := measure_later_union_le s q (fun n ↦ (h n).2.2.1)
    (fun n ↦ (h n).2.2.2.2.1) n
  have hsmall := (h n).2.2.2.2.2 (s n ∩ U n)
    ((measure_mono inter_subset_right).trans hμ)
  have hint : IntegrableOn (fun x ↦ ‖f n x‖) (s n) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp (f n))).norm.integrableOn
  have heq := integral_inter_add_sdiff (hU n) hint
  have hlarge := (h n).2.2.2.1
  dsimp only at heq ⊢
  linarith

/-- Let `(u n)` be a sequence in `ℓ¹(ℕ, ℝ)` that converges in norm to `a`, and
let `k : ℕ → ℕ` be strictly increasing. Then the absolute value of the
`k n`-th coordinate of `u n` tends to zero as `n → ∞`. -/
private lemma tendsto_diagonal_norm_zero {u : ℕ → ℓ¹(ℕ, ℝ)} {a : ℓ¹(ℕ, ℝ)}
    (hu : Filter.Tendsto u Filter.atTop (𝓝 a)) {k : ℕ → ℕ} (hk : StrictMono k) :
    Filter.Tendsto (fun n ↦ ‖u n (k n)‖) Filter.atTop (𝓝 0) := by
  have ha : Summable (fun i ↦ ‖a i‖) := by
    simpa using (lp.memℓp a).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have hka := ha.tendsto_atTop_zero.comp hk.tendsto_atTop
  have hdiff : Filter.Tendsto (fun n ↦ ‖u n - a‖) Filter.atTop (𝓝 0) := by
    simpa using (hu.sub_const a).norm
  apply squeeze_zero (fun n ↦ norm_nonneg _) ?_ (by simpa using hdiff.add hka)
  intro n
  calc
    ‖u n (k n)‖ = ‖(u n - a) (k n) + a (k n)‖ := by simp
    _ ≤ ‖(u n - a) (k n)‖ + ‖a (k n)‖ := norm_add_le _ _
    _ ≤ ‖u n - a‖ + ‖a (k n)‖ :=
      add_le_add (lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
        (u n - a) (k n)) le_rfl

/-- A relatively weakly compact family in real `L¹` is equi-integrable. -/
theorem MeasureTheory.Lp.unifIntegrable_of_isCompact_closure {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {F : Set (Lp ℝ 1 μ)}
    (hF : IsCompact (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' F))) :
    UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ := by
  by_contra h
  obtain ⟨ε, hε, f, s, hf, hs, hd, hlarge⟩ := exists_disjoint_witnesses h
  obtain ⟨T, hT⟩ := exists_signed_restriction_map f hs hd
  obtain ⟨a, _, k, hk, hlim⟩ := (WeakSpace.isCompact_iff_isSeqCompact.mp hF)
    (fun n ↦ subset_closure (mem_image_of_mem _ (hf n)))
  have hweak := (WeakSpace.map T).continuous.tendsto a |>.comp hlim
  have hnorm : Filter.Tendsto (fun n ↦ T (f (k n))) Filter.atTop
      (𝓝 (T ((toWeakSpace ℝ (Lp ℝ 1 μ)).symm a))) :=
    lp.tendsto_l1_of_weak_tendsto hweak
  have hdiag := tendsto_diagonal_norm_zero hnorm hk
  have hlower (n) : ε ≤ ‖T (f (k n)) (k n)‖ := by
    rw [hT]
    exact (hlarge (k n)).le.trans (le_abs_self _)
  have : ε ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdiag hlower
  exact (not_le_of_gt hε) this

/-- **Dunford–Pettis theorem.** Let `μ` be a finite measure and `F` a
norm-bounded subset of real `L¹(μ)`. The following are equivalent:
* `F` is relatively weakly compact.
* `F` is equi-integrable.
* `F` is almost order bounded. -/
theorem MeasureTheory.Lp.dunford_pettis {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {F : Set (Lp ℝ 1 μ)}
    (hbounded : Bornology.IsBounded F) :
    List.TFAE [IsCompact (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' F)),
      UnifIntegrable (fun f : F ↦ (f.1 : α → ℝ)) 1 μ, AlmostOrderBounded F] := by
  tfae_have 1 → 2 := MeasureTheory.Lp.unifIntegrable_of_isCompact_closure
  tfae_have 2 → 1 := MeasureTheory.Lp.isCompact_closure_of_unifIntegrable hbounded
  tfae_have 3 ↔ 2 := MeasureTheory.Lp.almostOrderBounded_iff_unifIntegrable hbounded
  tfae_finish
